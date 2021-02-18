{-# Language LinearTypes #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language BlockArguments #-}
{-# Language RoleAnnotations #-}
{-# Language ImportQualifiedPost #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language InstanceSigs #-}
{-# Language GADTs #-}

module Data.Primitive.Linear.Token
  ( Token(..)
  , alloc
  , step
  , Unique(unique)
  ) where

import Data.Unrestricted.Linear (Ur(..))
import GHC.ST
import GHC.Stack
import Data.Primitive.Linear.Unlifted.Token (Token#(..))
import Data.Primitive.Linear.Unlifted.Token qualified as Unlifted
import Unsafe.Linear qualified as Unsafe
import Prelude.Linear (Consumable(..))

type role Token nominal
data Token s where
  Token :: Token# s %1 -> Token s

unToken :: Token s %1 -> Token# s
unToken = Unsafe.toLinear go where
  go :: Token s -> Token# s
  go (Token s) = s

alloc :: (forall s. Token s %1 -> Ur b) %1 -> Ur b
alloc f = Unlifted.alloc \t -> f (Token t)

step :: Token s %1 -> ST s a -> (Token s, Ur a)
step (Token t) m = wrap (Unlifted.step t m) where
  wrap :: (# Token# s, Ur a #) %1 -> (Token s, Ur a)
  wrap (# x, y #) = (Token x, y)

-- TODO: typeclass

instance Consumable (Token s) where
  consume t = Unlifted.consume (unToken t)

class Unique a where
  unique :: HasCallStack => a -> a -> b

instance Unique (Token s) where
  unique x y = Unlifted.unique (unToken x) (unToken y)
