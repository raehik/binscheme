{-# LANGUAGE OverloadedStrings #-}

module Binrep.Type.Text.Encoding.Ascii where

import Binrep.Type.Text.Internal
import Binrep.Type.Text.Encoding.Utf8

import Rerefined.Predicate.Common
import Rerefined.Refine ( unsafeRefine )

import Data.Text qualified as Text
import Data.Text ( Text )

import Data.Text.Encoding qualified as Text

-- | 7-bit
data Ascii
instance Predicate Ascii where type PredicateName d Ascii = "ASCII"

-- | 'Text' must be validated if you want to permit 7-bit ASCII only.
--
-- TODO there should be a MUCH faster check here in text-2.0. text-short has it,
-- text doesn't yet. see: https://github.com/haskell/text/issues/496
instance Refine Ascii Text where
    validate p t = validateBool p "not valid 7-bit ASCII" (Text.isAscii t)

-- | We reuse UTF-8 encoding for ASCII, since it is a subset of UTF-8.
instance Encode Ascii where encode' = encode' @Utf8

instance Decode Ascii where
    decode bs =
        case Text.decodeASCII' bs of
          Just t  -> Right $ unsafeRefine t
          Nothing -> Left  "not valid 7-bit ASCII"
