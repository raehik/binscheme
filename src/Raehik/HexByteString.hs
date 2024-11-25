{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE UnboxedTuples #-}

module Raehik.HexByteString where

import Data.ByteString.Internal qualified as B
import Data.Text.Builder.Linear.Core qualified as TBLC
import Data.Text.Builder.Linear      qualified as TBL
import Data.Text.Array qualified as A
import Data.Word ( Word8, Word64, Word16, Word32 )
import GHC.ST ( ST(ST) )
import Raehik.Compat.Data.Primitive.Types
  ( indexWord8OffAddrAs#, writeWord8ByteArrayAs#, Prim' )

import GHC.Exts
  ( Int#, Int(I#), (-#), (*#), (+#), (>#), (>=#), Word8#, indexWord8OffAddr#
  , MutableByteArray#
  , Addr#, Ptr(Ptr) )
import Data.Bits ( Bits, (.&.), unsafeShiftR, (.|.), unsafeShiftL )
import GHC.Word ( Word8(W8#) )

import Foreign.ForeignPtr ( ForeignPtr )
import Raehik.Compat.GHC98KeepAlive ( withForeignPtr )

appendHexUpperByteString :: B.ByteString -> TBLC.Buffer %1 -> TBLC.Buffer
appendHexUpperByteString (B.BS fptr bsLen@(I# bsLen#)) buf =
    if   bsLen == 0 then buf
    else TBLC.appendExact srcLen (writeHexByteString nibbleHexUpperBranch fptr bsLen#) buf
  where
    srcLen = (bsLen * 3) - 1

fromHexUpperByteString :: B.ByteString -> TBL.Builder
fromHexUpperByteString bs = TBL.Builder $ \b -> appendHexUpperByteString bs b

-- | consume 8 bytes (not final, >=9 bytes remaining), write 24 bytes
{-# INLINE c8w24 #-}
c8w24
    :: (Word64 -> Word64) -> MutableByteArray# s -> Int# -> Word64 -> ST s ()
c8w24 nibbleHex dst# dstOff# w64 = do
    writeWord8ByteArrayAs dst#  dstOff#         c0
    writeWord8ByteArrayAs dst# (dstOff# +#  8#) c1
    writeWord8ByteArrayAs dst# (dstOff# +# 16#) c2
  where
    c0  = packW64WithW8 n0   n1   0x20 n2   n3   0x20 n4   n5
    c1  = packW64WithW8 0x20 n6   n7   0x20 n8   n9   0x20 n10
    c2  = packW64WithW8 n11  0x20 n12  n13  0x20 n14  n15  0x20

    -- TODO nibble isolation is endian-dependent, everything else agnostic
    n0  = nibbleHex ((w64 `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w64                    .&. 0xF)
    n2  = nibbleHex ((w64 `unsafeShiftR` 12) .&. 0xF)
    n3  = nibbleHex ((w64 `unsafeShiftR`  8) .&. 0xF)
    n4  = nibbleHex ((w64 `unsafeShiftR` 20) .&. 0xF)
    n5  = nibbleHex ((w64 `unsafeShiftR` 16) .&. 0xF)
    n6  = nibbleHex ((w64 `unsafeShiftR` 28) .&. 0xF)
    n7  = nibbleHex ((w64 `unsafeShiftR` 24) .&. 0xF)
    n8  = nibbleHex ((w64 `unsafeShiftR` 36) .&. 0xF)
    n9  = nibbleHex ((w64 `unsafeShiftR` 32) .&. 0xF)
    n10 = nibbleHex ((w64 `unsafeShiftR` 44) .&. 0xF)
    n11 = nibbleHex ((w64 `unsafeShiftR` 40) .&. 0xF)
    n12 = nibbleHex ((w64 `unsafeShiftR` 52) .&. 0xF)
    n13 = nibbleHex ((w64 `unsafeShiftR` 48) .&. 0xF)
    n14 = nibbleHex  (w64 `unsafeShiftR` 60)
    n15 = nibbleHex ((w64 `unsafeShiftR` 56) .&. 0xF)

-- | consume final 1 byte, writes 2 bytes
{-# INLINE cf1w2 #-}
cf1w2 :: (Word16 -> Word16) -> MutableByteArray# s -> Int# -> Word8 -> ST s ()
cf1w2 nibbleHex dst# dstOff# w = do
    writeWord8ByteArrayAs dst#  dstOff#         c0
  where
    c0  = packW16WithW8 n0 n1
    -- TODO nibble isolation is endian-dependent, everything else agnostic
    n0  = nibbleHex ((w' `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w'                    .&. 0xF)
    w'  = fromIntegral w

-- | consume final 2 bytes, writes 5 (4+1) bytes
{-# INLINE cf2w5 #-}
cf2w5
    :: (forall a. Integral a => a -> a)
    -> MutableByteArray# s -> Int# -> Word16
    -> ST s ()
cf2w5 nibbleHex dst# dstOff# w = do
    writeWord8ByteArrayAs dst#  dstOff#        c0
    writeWord8ByteArrayAs dst# (dstOff# +# 4#) n3
  where
    c0  = packW32WithW8 n0 n1 0x20 n2
    -- TODO nibble isolation is endian-dependent, everything else agnostic
    n0  = nibbleHex ((w32 `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w32                    .&. 0xF)
    n2  = nibbleHex ((w32 `unsafeShiftR` 12) .&. 0xF)
    w32 :: Word32 = fromIntegral w
    n3  = nibbleHex @Word8 (fromIntegral ((w `unsafeShiftR`  8) .&. 0xF))

-- | consume final 3 bytes, writes 8 bytes
{-# INLINE cf3w8 #-}
cf3w8
    :: (forall a. Integral a => a -> a)
    -> MutableByteArray# s -> Int# -> Word16 -> Word8
    -> ST s ()
cf3w8 nibbleHex dst# dstOff# w16 w8 = do
    writeWord8ByteArrayAs dst#  dstOff#        c0
  where
    c0  = packW64WithW8 n0 n1 0x20 n2 n3 0x20 n4 n5
    n0  = nibbleHex ((w16_64 `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w16_64                    .&. 0xF)
    n2  = nibbleHex ((w16_64 `unsafeShiftR` 12) .&. 0xF)
    n3  = nibbleHex ((w16_64 `unsafeShiftR`  8) .&. 0xF)
    n4  = nibbleHex  ((w8_64 `unsafeShiftR`  4) .&. 0xF)
    n5  = nibbleHex   (w8_64                    .&. 0xF)
    w16_64 :: Word64 = fromIntegral w16
    w8_64  :: Word64 = fromIntegral  w8

-- | consume final 4 bytes, writes 11 (8+2+1) bytes
{-# INLINE cf4w11 #-}
cf4w11
    :: (forall a. Integral a => a -> a)
    -> MutableByteArray# s -> Int# -> Word32
    -> ST s ()
cf4w11 nibbleHex dst# dstOff# w32 = do
    writeWord8ByteArrayAs dst#  dstOff#         c0
    writeWord8ByteArrayAs dst# (dstOff# +#  8#) c1
    writeWord8ByteArrayAs dst# (dstOff# +# 10#) n7
  where
    c0  = packW64WithW8 n0   n1 0x20 n2 n3 0x20 n4 n5
    c1  = packW16WithW8 0x20 n6
    n0  = nibbleHex ((w32_64 `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w32_64                    .&. 0xF)
    n2  = nibbleHex ((w32_64 `unsafeShiftR` 12) .&. 0xF)
    n3  = nibbleHex ((w32_64 `unsafeShiftR`  8) .&. 0xF)
    n4  = nibbleHex ((w32_64 `unsafeShiftR` 20) .&. 0xF)
    n5  = nibbleHex ((w32_64 `unsafeShiftR` 16) .&. 0xF)
    n6  = nibbleHex @Word16 (fromIntegral ((w32 `unsafeShiftR` 28) .&. 0xF))
    n7  = nibbleHex @Word8  (fromIntegral ((w32 `unsafeShiftR` 24) .&. 0xF))
    w32_64 :: Word64 = fromIntegral w32

-- | consume final 5 bytes, writes 14 (8+4+2) bytes
{-
{-# INLINE cf5w14 #-}
cf5w14
    :: (forall a. Integral a => a -> a)
    -> MutableByteArray# s -> Int# -> Word32 -> Word8
    -> ST s ()
cf5w14 nibbleHex dst# dstOff# w32 w8 = do
    writeWord8ByteArrayAs dst#  dstOff#         c0
    writeWord8ByteArrayAs dst# (dstOff# +#  8#) c1
    writeWord8ByteArrayAs dst# (dstOff# +# 10#) c2
  where
    c0  = packW64WithW8 n0   n1 0x20 n2 n3 0x20 n4 n5
    c1  = packW32WithW8 0x20 n6 n7 0x20
    c1  = packW16WithW8 n8 n9
    n0  = nibbleHex ((w32_64 `unsafeShiftR`  4) .&. 0xF)
    n1  = nibbleHex  (w32_64                    .&. 0xF)
    n2  = nibbleHex ((w32_64 `unsafeShiftR` 12) .&. 0xF)
    n3  = nibbleHex ((w32_64 `unsafeShiftR`  8) .&. 0xF)
    n4  = nibbleHex ((w32_64 `unsafeShiftR` 20) .&. 0xF)
    n5  = nibbleHex ((w32_64 `unsafeShiftR` 16) .&. 0xF)
    n6  = nibbleHex @Word16 (fromIntegral ((w32 `unsafeShiftR` 28) .&. 0xF))
    n7  = nibbleHex @Word8  (fromIntegral ((w32 `unsafeShiftR` 24) .&. 0xF))
    w32_64 :: Word64 = fromIntegral w32
-}

{-
idk :: (Bits a, Integral a) => (Word8 -> Word8) -> a -> Int -> Word8
idk f a idx = f (fromIntegral ((a `unsafeShiftR` idx) .&. 0xF))
-}

{-
you must not call with bsLen == idx :)
TODO handle <=8 case:
* if 1 byte,  read 1 byte,  write 2
* if 2 bytes, read 2 bytes, write 4+1
* if 3 bytes, read (2+1) bytes, write 8
* if 4 bytes, read 4 bytes, write 8+2+1
* if 5 bytes, read (4+1) bytes, write 8+4+2
* if 6 bytes, read (4+2) bytes, write 8+8+1
* if 7 bytes, read (4+2+1) bytes, write 8+8+4
* if 8 bytes, read 8 bytes, write 8+8+4+2+1
1  2  3  4  5  6  7  8
11 22 33 44 55 66 77 88 
123456789012345678901234
order that way for amortization (fast cases at top so not slowed)
-}
writeHexByteString
    :: (forall a. Integral a => a -> a)
    -> ForeignPtr Word8 -> Int# -> A.MArray s -> Int
    -> ST s ()
writeHexByteString nibbleHex fptr bsLen# (A.MutableByteArray dst#) (I# dstOff#) =
    withForeignPtr fptr $ \(Ptr addr#) ->
        writeHexByteString' nibbleHex addr# bsLen# dst# 0# dstOff#

writeHexByteString'
    :: (forall a. Integral a => a -> a)
    -> Addr# -> Int# -> MutableByteArray# s -> Int# -> Int#
    -> ST s ()
writeHexByteString' nibbleHex addr# bsLen# dst# idx# dstOff# =
    case bsRemaining# >=# 9# of
      1# -> do -- true, 1#
        let w64 = indexWord8OffAddrAs# addr# idx#
        c8w24 nibbleHex dst# dstOff# w64
        writeHexByteString' nibbleHex addr# bsLen# dst# (idx# +# 8#) (dstOff# +# 24#)

      _  -> -- false, 0#
        case bsRemaining# of
          1# -> do
            let w8 = indexWord8OffAddrAs# addr# idx#
            cf1w2 nibbleHex dst# dstOff# w8
            pure () -- TODO Should we touch here? fpc, or the whole fptr?

          2# -> do
            let w16 = indexWord8OffAddrAs# addr# idx#
            cf2w5 nibbleHex dst# dstOff# w16
            pure () -- TODO Should we touch here? fpc, or the whole fptr?

          3# -> do
            let w16 = indexWord8OffAddrAs# addr# idx#
                w8  = indexWord8OffAddrAs# addr# (idx# +# 2#)
            cf3w8 nibbleHex dst# dstOff# w16 w8
            pure () -- TODO Should we touch here? fpc, or the whole fptr?

          4# -> do
            let w32 = indexWord8OffAddrAs# addr# idx#
            cf4w11 nibbleHex dst# dstOff# w32
            pure () -- TODO Should we touch here? fpc, or the whole fptr?

          _ -> do
            -- TODO CBA haven't filled out 5,6,7,8
            let b#      = indexWord8OffAddr# addr# idx#
                bInt    = fromIntegral (W8# b#) :: Int
                nibble1 = (bInt .&. 0xF0) `unsafeShiftR` 4
                nibble2 =  bInt .&. 0x0F
            A.unsafeWrite (A.MutableByteArray dst#) (I# dstOff#)     (W8# (nibbleHexLowerBranch nibble1))
            A.unsafeWrite (A.MutableByteArray dst#) (I# dstOff# + 1) (W8# (nibbleHexLowerBranch nibble2))
            A.unsafeWrite (A.MutableByteArray dst#) (I# dstOff# + 2) 0x20
            writeHexByteString' nibbleHex addr# bsLen# dst# (idx# +# 1#) (dstOff# +# 3#)
  where bsRemaining# = bsLen# -# idx#

-- uses branch (CMP, JMP)
-- n < 0x10 !!
nibbleHexLowerBranch' :: Integral a => a -> a
nibbleHexLowerBranch' a =
    if   a > 9
    then 0x57 + a
    else 0x30 + a

-- uses branch (CMP, JMP)
-- n < 0x10 !!
nibbleHexUpperBranch :: Integral a => a -> a
nibbleHexUpperBranch a =
    if   a > 9
    then 0x37 + a
    else 0x30 + a

writeWord8ByteArrayAs :: Prim' a => MutableByteArray# s -> Int# -> a -> ST s ()
writeWord8ByteArrayAs arr# os# a = ST $ \st0 ->
    case writeWord8ByteArrayAs# arr# os# a st0 of
      st1 -> (# st1, () #)

{-
writeHexByteString
    :: ForeignPtr Word8 -> Int -> A.MArray s -> Int -> ST s ()
writeHexByteString fptr bsLen dst dstOff = unsafeIOToST $
    withForeignPtr fptr $ \ptr ->
        writeHexByteString' ptr bsLen 0 dst dstOff

writeHexByteString'
    :: Ptr Word8 -> Int -> Int -> A.MArray s -> Int -> IO ()
writeHexByteString' bsPtr bsLen idx dst dstOff =
    case bsLen - idx of
      1 -> do
        A.unsafeWrite dst (dstOff + idx)     0xFF
        A.unsafeWrite dst (dstOff + idx + 1) 0xFF
        pure ()
      _ -> do
        A.unsafeWrite dst (dstOff + idx)     0xFF
        A.unsafeWrite dst (dstOff + idx + 1) 0xFF
        A.unsafeWrite dst (dstOff + idx + 2) 0x20
        writeHexByteString' bsPtr bsLen (idx+1) dst dstOff
-}

-- uses branch (CMP, JMP)
-- n < 0x10 !!
nibbleHexLowerBranch :: Int -> Word8#
nibbleHexLowerBranch (I# n#) = b
  where
    !(W8# b) = fromIntegral (I# (0x30# +# n# +# (n# ># 9#) *# (0x60# -# 0x39#)))

-- uses memory (pointer dereference)
-- after some consideration, this is probably worse. but really unclear
nibbleHexLowerMem :: Int -> Word8#
nibbleHexLowerMem n = indexWord8OffAddr# "0123456789abcdef"# idx
  where !(I# idx) = n .&. 0x0F

-- | Pack a 'Word64' with 'Word8's.
packW64WithW8
    :: Bits a
    => a -> a -> a -> a
    -> a -> a -> a -> a
    -> a
packW64WithW8 b0 b1 b2 b3 b4 b5 b6 b7 =
        b0
    .|. unsafeShiftL b1  8
    .|. unsafeShiftL b2 16
    .|. unsafeShiftL b3 24
    .|. unsafeShiftL b4 32
    .|. unsafeShiftL b5 40
    .|. unsafeShiftL b6 48
    .|. unsafeShiftL b7 56
{-# INLINE packW64WithW8 #-}

-- | Pack a 'Word16' with 'Word8's.
packW16WithW8 :: Bits a => a -> a -> a
packW16WithW8 b0 b1 = b0 .|. unsafeShiftL b1 8
{-# INLINE packW16WithW8 #-}

-- | Pack a 'Word32' with 'Word8's.
packW32WithW8 :: Bits a => a -> a -> a -> a -> a
packW32WithW8 b0 b1 b2 b3 =
        b0
    .|. unsafeShiftL b1  8
    .|. unsafeShiftL b2 16
    .|. unsafeShiftL b3 24
{-# INLINE packW32WithW8 #-}
