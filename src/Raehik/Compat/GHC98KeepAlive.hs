{-# LANGUAGE UnboxedTuples #-}

-- | More generalized 'keepAlive#' users.

module Raehik.Compat.GHC98KeepAlive where

import GHC.ForeignPtr
  ( ForeignPtr(ForeignPtr), ForeignPtrContents, unsafeForeignPtrToPtr )
import GHC.Ptr
import GHC.ST
import GHC.Exts ( keepAlive#, touch# )

-- TODO v is this wrong? lol. I couldn't use it like this.
--withForeignPtr :: ForeignPtr a -> (forall s'. Ptr a -> ST s' b) -> ST s b
withForeignPtr :: forall a b s. ForeignPtr a -> (Ptr a -> ST s b) -> ST s b
withForeignPtr fo@(ForeignPtr _ r) f = ST $ \s ->
  case f (unsafeForeignPtrToPtr fo) of
    ST action# -> keepAlive# r s action#

unsafeWithForeignPtr :: ForeignPtr a -> (forall s'. Ptr a -> ST s' b) -> ST s b
unsafeWithForeignPtr fo f = do
  r <- f (unsafeForeignPtrToPtr fo)
  touchForeignPtr fo
  return r

touchForeignPtr :: ForeignPtr a -> ST s ()
touchForeignPtr (ForeignPtr _ r) = touch r

touch :: ForeignPtrContents -> ST s ()
touch r = ST $ \s -> case touch# r s of s' -> (# s', () #)
