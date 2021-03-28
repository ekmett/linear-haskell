{-# Language LinearTypes #-}
{-# Language StrictData #-}
{-# Language RoleAnnotations #-}
{-# Language PolyKinds #-}
{-# Language DataKinds #-}
{-# Language ImportQualifiedPost #-}
{-# Language MagicHash #-}
{-# Language GADTs #-}
{-# Language BlockArguments #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneKindSignatures #-}
{-# Language FlexibleContexts #-}
{-# Language LambdaCase #-}
{-# Language RankNTypes #-}
{-# Language AllowAmbiguousTypes #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language TypeApplications #-}
{-# Language BangPatterns #-}
module Linear.Range
  ( Range(..)
  , KnownV
  , claim
  , declaim
  , merge
  , VLength

  , vlen
  
  ) where

import Data.Kind
import Data.Type.Equality
import Data.Unrestricted.Linear
import Data.V.Linear
import Data.V.Linear.Internal.V (V(..))
import Data.Vector as Vector
import GHC.Exts (magicDict, Any, Proxy#, proxy#)
import GHC.TypeNats
import Numeric.Natural
import Prelude (Int,($))
import Prelude qualified as P
import Unsafe.Coerce as UnsafeNL
import Unsafe.Linear as Unsafe

-- TODO
-- We can't really use V for this. We want a mutable vector for the backend.
-- that becomes apparent when we go to implement operations that write or map.
--
-- I should rebuild this on a type of Array that can hold linear values with a V n a-like
-- interface. It is just a damn shame that dupV only works for V.

--------------------------------------------------------------------------------
-- * Utilities
--------------------------------------------------------------------------------

data VK n a r = VK (KnownNat n => Int -> V n a %1 -> r)

vlen :: forall n a r. V n a %1 -> (KnownNat n => Int -> V n a %1 -> r) %1 -> r
vlen v0 k0 = Unsafe.toLinear2 go v0 (VK k0) where
  go :: V n a -> VK n a r -> r
  go v@(V v') vk = let !k = P.length v' in 
    magicDict vk (P.fromIntegral k :: Natural) k v where

--------------------------------------------------------------------------------
-- * Ranges
--------------------------------------------------------------------------------

-- start, end, backing size
type role Range nominal nominal nominal representational
type Range :: Type -> Nat -> Nat -> Type -> Type
data Range s i j a = Range {-# unpack #-} !Int {-# unpack #-} !Int

class KnownV s where
  type VLength s :: Nat
  reflectVec :: Vector Any

newtype P n a b = P (forall s. KnownV s => VLength s :~: n -> Range s 0 n a %1 -> Ur b)
data Q r = Q (forall s. KnownV s => Proxy# s -> r)

withQ :: Vector Any -> (forall s. KnownV s => Proxy# s -> r) -> r
withQ v f = magicDict (Q f) v proxy#

claim
  :: forall n a b.
     V n a %1
  -> (forall s. (KnownV s, VLength s ~ n) => Range s 0 n a %1 -> Ur b) %1
  -> Ur b
claim v0 f0 = vlen v0 \ k v1 -> Unsafe.toLinear2 (go k) v1 (P \Refl -> f0) where
  go :: Int -> V n a -> P n a b -> Ur b
  go k (V v) (P p) = withQ (UnsafeNL.unsafeCoerce v)
    \(_ :: Proxy# s) -> let proof = unsafeCoerce (Refl :: n :~: n) :: VLength s :~: n in
       p proof (Range @s 0 k)

-- splitAt :: KnownNat d => Range s i k a %1 %1 -> 
--    (Range s i (Min (i + d) k) a, Range s (n - Min (i + d) n) a)

-- this is the whole reason why we tag the object, really
merge :: forall s i j k a. Range s i j a %1 -> Range s j k a %1 -> Range s i k a
merge = Unsafe.toLinear2 go where
  go :: Range s i j a -> Range s j k a -> Range s i k a
  go (Range i n) (Range _ m) = Range i (n P.+ m)

declaim :: forall s i j a. KnownV s => Range s i j a %1 -> V (j - i) a
declaim = Unsafe.toLinear go where
  go :: Range s i j a -> V (j - i) a
  go (Range k n) = V $ UnsafeNL.unsafeCoerce $ Vector.take n $ Vector.drop k $ reflectVec @s

-- instance Consumable a => Consumable (V n a) where
--   consume = consume (declaim r)

-- instance (KnownV s, Consumable a) => Consumable (Range s i j a) where
--   consume r = consume (declaim r)

-- unique :: Range s i j a -> Range s i j b -> a -- requires i /= j

{-

abs :: Traversal (Range s i j n a) (Range s i j n b) a b

-- are these global or relative indices?
getAbs :: KnownV s => Range s i j n a %1 -> Int -> (a, Range s i j n a)
setAbs :: KnownV s => Range s i j n a %1 -> Int -> a %1 -> Range s i j n a
getRel :: (KnownNat i, KnownV s) => Range s i j n a %1 -> Int -> (Ur a, Range s i j n a)
setRel :: (KnownNat i, KnownV s) => Range s i j n a %1 -> Int -> a -> Range s i j n a


instance Consumable a => Consumable (Range s i j n a)

move :: KnownV s => (a %1 -> b) -> Range s i j n a %1 -> V (j - i) a
copy :: Dupable a => Range s i j n a -> V (j - i) a

instance KnownV s => Functor (Range s i k n) where


-- read only case doesn't need n
alloc :: V n a -> (forall s. KnownSource s => Source s n a %1 -> Ur b) %1 -> Ur b
split :: (i + j ~ k, Sing i) -> Source s k a %1 -> (# Source s i a, Source s j a #)
get :: KnownSource s => Source s n a %1 -> Int -> (Ur a, Source s n a)
instance KnownSource s => Foldable (Source s n)
copy :: KnownSource s => Source s n a %1 -> V n a


-- write only

-}
