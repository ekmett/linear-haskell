{-# Language UnliftedNewtypes #-}
{-# Language LinearTypes #-}
{-# Language RankNTypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language BlockArguments #-}
{-# Language RoleAnnotations #-}
{-# Language ImportQualifiedPost #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}

module Data.Primitive.Linear.Unlifted.Token
  ( Token#(..)
  , alloc
  , step
  , unique
  , consume
  ) where

import Control.Monad.Primitive
import Data.Unrestricted.Linear (Ur(..))
import GHC.Exts qualified as GHC
import GHC.ST
import GHC.Stack
import Unsafe.Linear qualified as Unsafe

type role Token# nominal
newtype Token# s = Token# (GHC.State# s) 

newtype Poly b = Poly (forall s. Token# s %1 -> Ur b)

alloc :: (forall s. Token# s %1 -> Ur b) %1 -> Ur b
alloc f = Unsafe.toLinear go (Poly f) where
  go :: Poly b -> Ur b
  go (Poly f') = GHC.runRW# \st -> f' (Token# st)

step :: Token# s %1 -> ST s a -> (# Token# s, Ur a #)
step = Unsafe.toLinear go where
  go :: Token# s -> ST s a -> (# Token# s, Ur a #)
  go (Token# s) m = case internal m s of
    (# s', a #) -> (# Token# s', Ur a #)

unique :: HasCallStack => Token# s %1 -> Token# s %1 -> a
unique x = error "Token#.unique: invariant broken" x

-- | Unlifted, so we can't be an instance of Consumable
consume :: Token# s %1 -> ()
consume = Unsafe.toLinear go where
  go :: Token# s -> ()
  go _ = ()
