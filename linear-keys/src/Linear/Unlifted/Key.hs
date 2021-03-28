{-# Language RoleAnnotations #-}
{-# Language MagicHash #-}
{-# Language KindSignatures #-}
{-# Language TypeOperators #-}
{-# Language BlockArguments #-}
{-# Language LinearTypes #-}
{-# Language UnliftedNewtypes #-}
{-# Language ScopedTypeVariables #-}
{-# Language UnboxedTuples #-}
{-# Language RankNTypes #-}
{-# Language ImportQualifiedPost #-}
module Linear.Unlifted.Key 
  ( Ref#(..)
  , Key#(..)
  , alloc
  , freeze
  , unique
  , turn
  ) where

import GHC.Stack
import GHC.Exts qualified as GHC
import Data.Unrestricted.Linear
import Unsafe.Coerce qualified as UnsafeNL
import Unsafe.Linear qualified as Unsafe

-- ref's can be passed around unrestrictedly
type role Ref# nominal
newtype Ref# s = Ref# (GHC.MutVar# s GHC.Any)

-- keys allow you to swap the contents of the refs, 0 bytes wide
type role Key# nominal representational
newtype Key# s a = Key# (GHC.State# s)

newtype Poly a b = Poly (forall s. Ref# s -> Key# s a %1 -> Ur b)

alloc :: forall a b. a %1 -> (forall s. Ref# s -> Key# s a %1 -> Ur b) %1 -> Ur b
alloc a1 f1 = Unsafe.toLinear2 go a1 (Poly f1) where
  go :: a -> Poly a b -> Ur b
  go a (Poly f) = GHC.runRW# \st -> case GHC.newMutVar# (UnsafeNL.unsafeCoerce a) st of 
    (# st', p #) -> f (Ref# p) (Key# st')
{-# NOINLINE alloc #-}

freeze :: forall s a. Ref# s -> Key# s a %1 -> a
freeze (Ref# p) = Unsafe.toLinear go where
  go :: Key# s a -> a
  go (Key# s) = case GHC.readMutVar# p s of
    (# _, v #) -> UnsafeNL.unsafeCoerce v

-- a 'proof' that two occurrences of the same Key can't occur at the same time
unique :: HasCallStack => Key# s a %1 -> Key# s b %1 -> r
unique = error "Unlifted.Key.dedup: duplicate key"

urn :: forall s a b. Ref# s -> Key# s a %1 -> (# a, b %1 -> Key# s b #)
turn (Ref# p) = Unsafe.toLinear go where
  go :: Key# s a -> (# a, b %1 -> Key# s b #)
  go (Key# s) = case GHC.readMutVar# p s of
    (# s', a #) -> 
       let k :: b -> Key# s b
           k b = case GHC.writeMutVar# p (UnsafeNL.unsafeCoerce b) s' of
             s'' -> Key# s''
       in (# UnsafeNL.unsafeCoerce a, Unsafe.toLinear k #)
