{-# LANGUAGE DeriveDataTypeable #-}

module Idx (
  Idx(..), mkIdx
)where

import Pretty
import Data.Data
import Data.Generics()

newtype Idx = IdS String
  deriving (Show,Eq,Ord,Data,Typeable)

mkIdx :: Idx -> Int -> Idx
mkIdx (IdS s) i = IdS (s++"."++(show i))

instance Pretty Idx where
  pretty (IdS s) = text s
