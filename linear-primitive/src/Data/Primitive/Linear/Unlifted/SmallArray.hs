{-# Language UnliftedNewtypes #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language ImportQualifiedPost #-}
{-# Language BlockArguments #-}
{-# Language BangPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# Language LinearTypes #-}
{-# Language KindSignatures #-}
{-# Language PolyKinds #-}

module Data.Primitive.Linear.Unlifted.SmallArray
  ( SmallArray#
  , unSmallArray#
  , alloc
  , allocBeside
  , lseq
  , size
  , get
  , set
  , copyInto
  , map
  , toList
  , freeze
  , dup2
  ) where

import Data.Unrestricted.Linear hiding (lseq, dup2)
import Prelude (Int)
import qualified Prelude as Prelude
import qualified Unsafe.Linear as Unsafe
import qualified GHC.Exts as GHC

-- | A mutable array holding @a@s
newtype SmallArray# a = SmallArray# (GHC.SmallMutableArray# GHC.RealWorld a)

-- | Extract the underlying 'GHC.SmallMutableArray#', consuming the 'SmallArray#'
-- in process.
unSmallArray# :: (GHC.SmallMutableArray# GHC.RealWorld a -> b) -> SmallArray# a %1-> Ur b
unSmallArray# f = Unsafe.toLinear \(SmallArray# a) -> Ur (f a)

-- | Consume an 'Array#'.
--
-- Note that we can not implement a 'Consumable' instance because 'SmallArray#'
-- is unlifted.
lseq :: SmallArray# a %1-> b %1-> b
lseq = Unsafe.toLinear2 \_ b -> b

-- | Allocate a mutable array of given size using a default value.
--
-- The size should be non-negative.
alloc :: Int -> a -> (SmallArray# a %1-> Ur b) %1-> Ur b
alloc (GHC.I# s) a f =
  let new = GHC.runRW# \st -> case GHC.newSmallArray# s a st of
        (# _, arr #) -> SmallArray# arr
  in f new
{-# NOINLINE alloc #-}  -- prevents runRW# from floating outwards

-- For the reasoning behind these NOINLINE pragmas, see the discussion at:
-- https://github.com/tweag/linear-base/pull/187#pullrequestreview-489183531

-- | Allocate a mutable array of given size using a default value,
-- using another 'SmallArray#' as a uniqueness proof.
--
-- The size should be non-negative.
--
-- TODO: construct a typeclass, be cause we may wind up with lots of these
-- 'can use x as a proof' types. the issue is such a typeclass is a positive
-- assertion about the fact that you can't construct these things willy-nilly
--
allocBeside :: Int -> a -> SmallArray# b %1-> (# SmallArray# a, SmallArray# b #)
allocBeside (GHC.I# s) a orig =
  let new = GHC.runRW# \st -> case GHC.newSmallArray# s a st of
        (# _, arr #) -> SmallArray# arr
  in (# new, orig #)
{-# NOINLINE allocBeside #-}  -- prevents runRW# from floating outwards

size :: SmallArray# a %1-> (# Ur Int, SmallArray# a #)
size = Unsafe.toLinear go where
  go :: SmallArray# a -> (# Ur Int, SmallArray# a #)
  go (SmallArray# arr) =
    let !s = GHC.sizeofSmallMutableArray# arr
    in (# Ur (GHC.I# s), SmallArray# arr  #)

get :: Int -> SmallArray# a %1-> (# Ur a, SmallArray# a #)
get (GHC.I# i) = Unsafe.toLinear go where
  go :: SmallArray# a -> (# Ur a, SmallArray# a #)
  go (SmallArray# arr) = case GHC.runRW# (GHC.readSmallArray# arr i) of
    (# _, ret #) -> (# Ur ret, SmallArray# arr #)
{-# NOINLINE get #-}  -- prevents the runRW# effect from being reordered

set :: Int -> a -> SmallArray# a %1-> SmallArray# a
set (GHC.I# i) (a :: a) = Unsafe.toLinear go where
  go :: SmallArray# a -> SmallArray# a
  go (SmallArray# arr) = case GHC.runRW# (GHC.writeSmallArray# arr i a) of
    _ -> SmallArray# arr
{-# NOINLINE set #-}  -- prevents the runRW# effect from being reordered

-- | Copy the first mutable array into the second mutable array, starting
-- from the given index of the source array.
--
-- It copies fewer elements if the second array is smaller than the
-- first. 'n' should be within [0..size src).
--
-- @
--  copyInto n src dest:
--   dest[i] = src[n+i] for i < size dest, i < size src + n
-- @
copyInto :: Int -> SmallArray# a %1-> SmallArray# a %1-> (# SmallArray# a, SmallArray# a #)
copyInto start@(GHC.I# start#) = Unsafe.toLinear2 go where
  go :: SmallArray# a -> SmallArray# a -> (# SmallArray# a, SmallArray# a #)
  go (SmallArray# src) (SmallArray# dst) =
    let !(GHC.I# len#) = Prelude.min
          (GHC.I# (GHC.sizeofSmallMutableArray# src) Prelude.- start)
          (GHC.I# (GHC.sizeofSmallMutableArray# dst))
    in case GHC.runRW# (GHC.copySmallMutableArray# src start# dst 0# len#) of
      _ -> (# SmallArray# src, SmallArray# dst #)
{-# NOINLINE copyInto #-}  -- prevents the runRW# effect from being reordered

map :: (a -> b) -> SmallArray# a %1-> SmallArray# b
map (f :: a -> b) arr = size arr `chain2` \(# Ur s, arr' #) -> go 0 s arr' where
  -- When we're mapping an array, we first insert `b`'s
  -- inside an `Array# a` by unsafeCoerce'ing, and then we
  -- unsafeCoerce the result to an `Array# b`.
  go :: Int -> Int -> SmallArray# a %1-> SmallArray# b
  go i s arr'
    | i Prelude.== s = Unsafe.toLinear GHC.unsafeCoerce# arr'
    | Prelude.otherwise = get i arr'
      `chain2` \(# Ur a, arr'' #) -> set i (Unsafe.coerce (f a)) arr''
      `chain` \arr''' -> go (i Prelude.+ 1) s arr'''
{-# NOINLINE map #-}

-- | Return the array elements as a lazy list.
toList :: SmallArray# a %1-> Ur [a]
toList = unSmallArray# \arr -> go 0 (GHC.I# (GHC.sizeofSmallMutableArray# arr)) arr where
  go i len arr
    | i Prelude.== len = []
    | GHC.I# i# <- i = case GHC.runRW# (GHC.readSmallArray# arr i#) of
      (# _, ret #) -> ret : go (i Prelude.+ 1) len arr

-- | /O(1)/ Convert an 'Array#' to an immutable 'GHC.Array#'.
freeze :: (GHC.SmallArray# a -> b) -> SmallArray# a %1-> Ur b
freeze f = unSmallArray# go where
  go mut = case GHC.runRW# (GHC.unsafeFreezeSmallArray# mut) of
    (# _, ret #) -> f ret

-- | Clone an array.
dup2 :: SmallArray# a %1-> (# SmallArray# a, SmallArray# a #)
dup2 = Unsafe.toLinear go where
  go :: SmallArray# a -> (# SmallArray# a, SmallArray# a #)
  go (SmallArray# arr) =
    case GHC.runRW# (GHC.cloneSmallMutableArray# arr 0# (GHC.sizeofSmallMutableArray# arr)) of
      (# _, new #) -> (# SmallArray# arr, SmallArray# new #)
{-# NOINLINE dup2 #-}

-- * Internal library

-- Below two are variants of (&) specialized for taking commonly used
-- unlifted values and returning a levity-polymorphic result.
--
-- They are not polymorphic on their first parameter since levity-polymorphism
-- disallows binding to levity-polymorphic values.

chain
   :: forall (r :: GHC.RuntimeRep) a (b :: GHC.TYPE r).
      SmallArray# a 
 %1-> (SmallArray# a %1-> b)
 %1-> b
chain a f = f a

chain2
   :: forall (r :: GHC.RuntimeRep) a b (c :: GHC.TYPE r).
      (# b, SmallArray# a #)
 %1-> ((# b, SmallArray# a #) %1-> c)
 %1-> c
chain2 a f = f a
infixl 1 `chain`, `chain2`
