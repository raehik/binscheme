{-
I mix string and bytestring terminology here due to bad C influences, but this
module is specifically interested in bytestrings and their encoding. String/text
encoding is handled in another module.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Binrep.Type.ByteString where

import Binrep
import Binrep.Type.Common ( Endianness )
import Binrep.Type.Int
import Binrep.Util

import Refined
import Refined.Unsafe

import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.ByteString.Builder qualified as B
import Data.Serialize qualified as Cereal
import Data.Word
import Numeric.Natural
import Data.Typeable ( Typeable, typeRep, Proxy, typeOf )
import Control.Monad ( replicateM )

-- | Bytestring representation.
data Rep
  = C
  -- ^ C-style bytestring. Arbitrary length, terminated with a null byte.
  --   Permits no null bytes inside the bytestring.

  | Pascal ISize Endianness
  -- ^ Pascal-style bytestring. Length defined in a prefixing integer of given
  --   size and endianness.

getCString :: Cereal.Get BS.ByteString
getCString = go mempty
  where go buf = do
            Cereal.getWord8 >>= \case
              0x00    -> return $ BL.toStrict $ B.toLazyByteString buf
              nonNull -> go $ buf <> B.word8 nonNull

instance BLen (Refined 'C BS.ByteString) where
    blen cbs = fromIntegral $ BS.length (unrefine cbs) + 1

instance Put (Refined 'C BS.ByteString) where
    put cbs = do
        Cereal.putByteString $ unrefine cbs
        Cereal.putWord8 0x00

-- | Total shite parsing efficiency. But, to be fair, that's why we don't
--   serialize arbitrary-length C strings!
instance Get (Refined 'C BS.ByteString) where
    get = reallyUnsafeRefine <$> getCString

-- | TODO why safe
instance (BLen a, itype ~ I 'U size e, BLen itype)
      => BLen (Refined ('Pascal size e) a) where
    blen rpa = blen @itype undefined + blen (unrefine rpa)

-- | TODO explain why safe
instance Put (Refined ('Pascal 'I1 e) BS.ByteString) where
    put rpbs = do
        put @(I 'U 'I1 e) $ fromIntegral $ BS.length pbs
        Cereal.putByteString pbs
      where pbs = unrefine rpbs
instance Get (Refined ('Pascal 'I1 e) BS.ByteString) where
    get = do
        len <- get @(I 'U 'I1 e)
        pbs <- Cereal.getByteString $ fromIntegral len
        return $ reallyUnsafeRefine pbs

deriving anyclass instance PutWith r (Refined ('Pascal 'I1 e) BS.ByteString)
deriving anyclass instance GetWith r (Refined ('Pascal 'I1 e) BS.ByteString)

-- TODO finish and explain why safe. actually should use singletons!
instance PutWith Rep BS.ByteString where
    putWith strRep bs =
        case strRep of
          C -> case refine @'C bs of
                 Left  e   -> Left $ show e
                 Right rbs -> putWithout rbs
          Pascal size _e -> do
            case size of
              I1 -> do
                if   len > fromIntegral (maxBound @Word8)
                then Left "bytestring too long for configured static-size length prefix"
                else Right $ B.byteString bs
              _ -> undefined
      where len = BS.length bs

-- TODO finish and explain why safe. actually should use singletons!
instance GetWith Rep BS.ByteString where
    getWith = \case C -> getCString
                    Pascal _size _e -> undefined

-- | A C-style bytestring must not contain any null bytes.
instance Predicate 'C BS.ByteString where
    validate p bs
     | BS.any (== 0x00) bs = throwRefineOtherException (typeRep p) $
        "null byte not permitted in in C-style bytestring"
     | otherwise = success

-- | Is the given 'BS.ByteString' short enough to allow placing its length in
--   the given size prefix?
instance
    ( irep ~ IRep 'U size
    , Bounded irep, Integral irep
    , Show irep, Typeable size, Typeable e
    ) => Predicate ('Pascal size e) BS.ByteString where
    validate p = validateLengthPrefixed @size p (fromIntegral . BS.length)

-- | Is the given list-like short enough to allow placing its length in the
--   given size prefix?
--
-- Note that we don't care about the elements inside or their size.
instance
    ( irep ~ IRep 'U size
    , Bounded irep, Integral irep
    , Foldable t
    , Show irep, Typeable size, Typeable e, Typeable t, Typeable a
    ) => Predicate ('Pascal size e) (t a) where
    validate p = validateLengthPrefixed @size p (fromIntegral . length)

-- | Instance helper. We cheat with 'Typeable's to obtain type tags without
--   asking the user explicitly. It's good enough, and refined uses them anyway.
validateLengthPrefixed
    :: forall size irep p a
    .  ( irep ~ IRep 'U size
       , Bounded irep, Integral irep
       , Show irep, Typeable size, Typeable p, Typeable a
       )
    => Proxy p
    -> (a -> Natural) -> a -> Maybe RefineException
validateLengthPrefixed p f a
 | len > fromIntegral max'
    = throwRefineOtherException (typeRep p) $
          tshow (typeOf a)
        <>" too long for given length prefix type: "
        <>tshow len<>" > "<>tshow max'
 | otherwise = success
  where
    len  = f a
    max' = maxBound @irep

instance
    ( Put a
    , irep ~ IRep 'U size
    , Num irep, Integral irep
    , itype ~ I 'U size e
    , Put itype)
      => Put (Refined ('Pascal size e) [a]) where
    put ras = do
        put @itype $ fromIntegral $ length as
        mapM_ (put @a) as
      where as = unrefine ras

-- TODO why safe
instance
    ( Get a
    , irep ~ IRep 'U size
    , Num irep, Integral irep
    , itype ~ I 'U size e
    , Get itype)
      => Get (Refined ('Pascal size e) [a]) where
    get = do
        len <- get @itype
        as <- replicateM (fromIntegral len) (get @a)
        return $ reallyUnsafeRefine as
