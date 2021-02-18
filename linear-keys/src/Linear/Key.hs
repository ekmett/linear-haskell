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
{-# Language TypeApplications #-}
{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
module Linear.Key 
  ( Ref(..)
  , Key(..)
  , alloc
  , freeze
  , unique
  , turn
  ) where

import GHC.Stack
import GHC.Exts qualified as GHC
import GHC.Prim
import Control.Optics.Linear.Lens
import Data.Unrestricted.Linear
import Linear.Unlifted.Key (Ref#(..), Key#(..))
import Linear.Unlifted.Key qualified as Unlifted
import Unsafe.Linear qualified as Unsafe

-- ref's can be passed around unrestrictedly
type role Ref nominal
data Ref s = Ref (Ref# s)

class KnownRef s where
  ref :: Ref s

ref# :: forall s. KnownRef s => Ref# s
ref# = case ref @s of
  Ref p -> p

-- unpacks in another structure to something 0 bytes wide, the Ref carries the payload
type role Key nominal representational
data Key s a = Key (Key# s a)

key# :: Key s a %1 -> Key# s a
key# (Key k) = k

data WrapRef s a = WrapRef (KnownRef s => Proxy# s -> a)

withRef :: (KnownRef s => Proxy# s -> a) -> Ref s -> Proxy# s -> a
withRef f x y = GHC.magicDict (WrapRef f) x y
{-# inline withRef #-}

newtype Poly a b = Poly (forall s. KnownRef s => Key s a %1 -> Ur b)

alloc :: forall a b. a %1 -> (forall s. KnownRef s => Key s a %1 -> Ur b) %1 -> Ur b
alloc a0 f0 = Unsafe.toLinear2 go a0 (Poly f0) where
  go :: a -> Poly a b -> Ur b
  go a (Poly f) = Unlifted.alloc a \r# k# -> withRef (\_ -> f) (Ref r#) proxy# (Key k#)

{-# NOINLINE alloc #-}

instance (KnownRef s, Consumable a) => Consumable (Key s a) where
  consume x = consume (freeze x)

freeze :: forall s a. KnownRef s => Key s a %1 -> a
freeze k = Unlifted.freeze (ref# @s) (key# k)

-- TODO: unique1 class
-- a 'proof' that two occurrences of the same Key can't occur at the same time
unique :: HasCallStack => Key s a %1 -> Key s b %1 -> r
unique = error "Unlifted.Key.dedup: duplicate key"

turn :: forall s a b. KnownRef s => Lens (Key s a) (Key s b) a b
turn = lens go where
  go :: Key s a %1 -> (a, b %1 -> Key s b)
  go k = wrap (Unlifted.turn (ref# @s) (key# k))

  wrap :: (# a, b %1 -> Key# s b #) %1 -> (a, b %1 -> Key s b)
  wrap (# a, f #) = (a, \b -> Key (f b))
  

{-
(Ref# p) = Unsafe.toLinear go where
  go :: Key# s a -> (# a, b %1 -> Key# s b #)
  go (Key# s) = case GHC.readMutVar# p s of
    (# s', a #) -> 
       let k :: b -> Key# s b
           k b = case GHC.writeMutVar# p (UnsafeNL.unsafeCoerce b) s' of
             s'' -> Key# s''
       in (# UnsafeNL.unsafeCoerce a, Unsafe.toLinear k #)
-}
