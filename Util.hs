module Util (
  mytrace,
  module Control.Monad,
  module Control.Monad.Error,
  module Control.Monad.List,
  module Control.Monad.State.Strict,
  module Data.List
) where
import Data.List
import Control.Monad
import Control.Monad.Error
import Control.Monad.List
import Control.Monad.State.Strict
import Debug.Trace

mytrace :: Show a1 => a1 -> a -> a
mytrace x = trace (show x)
