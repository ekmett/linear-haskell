{-# Language UnliftedNewtypes #-}
{-# Language TypeApplications #-}
{-# Language MagicHash #-}
{-# Language UnboxedTuples #-}
{-# Language ImportQualifiedPost #-}
{-# Language BlockArguments #-}
{-# Language BangPatterns #-}
{-# Language ScopedTypeVariables #-}
{-# Language LinearTypes #-}
{-# Language KindSignatures #-}
{-# Language PolyKinds #-}

module Data.Primitive.Linear.Unlifted.ByteArray
  ( ByteArray#
  , unByteArray#
  , alloc
  , allocBeside
  , lseq
  , size
  , get
  , set
  , copyInto
  , copy
  , toList
  , freeze
  , dup2
  ) where

import Data.Unrestricted.Linear hiding (lseq, dup2)
import Data.Primitive.Types
import Prelude (Int)
import qualified Prelude as Prelude
import qualified Unsafe.Linear as Unsafe
import qualified GHC.Exts as GHC

-- | A mutable byte array
newtype ByteArray# = ByteArray# (GHC.MutableByteArray# GHC.RealWorld)

-- | Extract the underlying 'GHC.ByteArray#', consuming the 'ByteArray#' in the process.
unByteArray# :: (GHC.MutableByteArray# GHC.RealWorld -> b) -> ByteArray# %1 -> Ur b
unByteArray# f = Unsafe.toLinear \(ByteArray# a) -> Ur (f a)

-- | Consume a 'ByteArray#'.
--
-- Note that we can not implement a 'Consumable' instance because 'ByteArray#' is unlifted.
lseq :: ByteArray# %1 -> b %1 -> b
lseq = Unsafe.toLinear2 \_ b -> b

-- | Allocate a mutable array of given size using a default value.
--
-- The size should be non-negative.
alloc :: Int -> (ByteArray# %1 -> b) %1 -> b
alloc (GHC.I# s) f =
  let new = GHC.runRW# \st -> case GHC.newByteArray# s st of
        (# _, arr #) -> ByteArray# arr
  in f new
{-# NOINLINE alloc #-}  -- prevents runRW# from floating outwards

-- For the reasoning behind these NOINLINE pragmas, see the discussion at:
-- https://github.com/tweag/linear-base/pull/187#pullrequestreview-489183531

-- | Allocate a mutable array of given size using a default value,
-- using another 'ByteArray#' as a uniqueness proof.
--
-- The size should be non-negative.
--
-- TODO: construct a typeclass, be cause we may wind up with lots of these
-- 'can use x as a proof' types. the issue is such a typeclass is a positive
-- assertion about the fact that you can't construct these things willy-nilly
allocBeside :: Int -> ByteArray# %1 -> (# ByteArray#, ByteArray# #)
allocBeside (GHC.I# s) orig =
  let new = GHC.runRW# \st -> case GHC.newByteArray# s st of
        (# _, arr #) -> ByteArray# arr
  in (# new, orig #)
{-# NOINLINE allocBeside #-}  -- prevents runRW# from floating outwards

size :: ByteArray# %1 -> (# Ur Int, ByteArray# #)
size = Unsafe.toLinear go where
  go :: ByteArray# -> (# Ur Int, ByteArray# #)
  go (ByteArray# arr) =
    let !s = GHC.sizeofMutableByteArray# arr
    in (# Ur (GHC.I# s), ByteArray# arr  #)

get :: forall a. Prim a => Int -> ByteArray# %1 -> (# Ur a, ByteArray# #)
get (GHC.I# i) = Unsafe.toLinear go where
  go :: ByteArray# -> (# Ur a, ByteArray# #)
  go (ByteArray# arr) = case GHC.runRW# (readByteArray# @a arr i) of
    (# _, ret #) -> (# Ur ret, ByteArray# arr #)
{-# NOINLINE get #-}  -- prevents the runRW# effect from being reordered

set :: forall a. Prim a => Int -> a -> ByteArray# %1 -> ByteArray#
set (GHC.I# i) (a :: a) = Unsafe.toLinear go where
  go :: ByteArray# -> ByteArray#
  go (ByteArray# arr) = case GHC.runRW# (writeByteArray# @a arr i a) of
    _ -> ByteArray# arr
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
copyInto :: Int -> ByteArray# %1 -> ByteArray# %1 -> (# ByteArray#, ByteArray# #)
copyInto start@(GHC.I# start#) = Unsafe.toLinear2 go where
  go :: ByteArray# -> ByteArray# -> (# ByteArray#, ByteArray# #)
  go (ByteArray# src) (ByteArray# dst) =
    let !(GHC.I# len#) = Prelude.min
          (GHC.I# (GHC.sizeofMutableByteArray# src) Prelude.- start)
          (GHC.I# (GHC.sizeofMutableByteArray# dst))
    in case GHC.runRW# (GHC.copyMutableByteArray# src start# dst 0# len#) of
      _ -> (# ByteArray# src, ByteArray# dst #)
{-# NOINLINE copyInto #-}

copy :: ByteArray# %1 -> Int -> ByteArray# %1 -> Int -> Int -> (# ByteArray#, ByteArray# #)
copy src0 (GHC.I# src_ofs#) dst0 (GHC.I# dst_ofs#) (GHC.I# n#) = Unsafe.toLinear2 go src0 dst0 where
  go :: ByteArray# -> ByteArray# -> (# ByteArray#, ByteArray# #)
  go (ByteArray# src) (ByteArray# dst) =
    case GHC.runRW# (GHC.copyMutableByteArray# src src_ofs# dst dst_ofs# n#) of
      _ -> (# ByteArray# src, ByteArray# dst #)
{-# NOINLINE copy #-}

-- | Return the array elements as a lazy list.
toList :: forall a. Prim a => ByteArray# %1 -> Ur [a]
toList = unByteArray# \arr -> go 0 (GHC.I# (GHC.sizeofMutableByteArray# arr) `Prelude.div` GHC.I# (sizeOf# (Prelude.undefined :: a))) arr where
  go i len arr
    | i Prelude.== len = []
    | GHC.I# i# <- i = case GHC.runRW# (readByteArray# @a arr i#) of
      (# _, ret #) -> ret : go (i Prelude.+ 1) len arr

-- | /O(1)/ Convert an 'Array#' to an immutable 'GHC.Array#'.
freeze :: (GHC.ByteArray# -> b) -> ByteArray# %1 -> Ur b
freeze f = unByteArray# go where
  go mut = case GHC.runRW# (GHC.unsafeFreezeByteArray# mut) of
    (# _, ret #) -> f ret

-- | Clone an array.
dup2 :: ByteArray# %1 -> (# ByteArray#, ByteArray# #)
dup2 = Unsafe.toLinear go where
  go :: ByteArray# -> (# ByteArray#, ByteArray# #)
  go (ByteArray# arr) =
    GHC.runRW# \st -> case GHC.getSizeofMutableByteArray# arr st of
      (# st', n#  #) -> case GHC.newByteArray# n# st' of
        (# st'', cpy #) -> case GHC.copyMutableByteArray# arr 0# cpy 0# n# st'' of
          _ -> (# ByteArray# arr, ByteArray# cpy #)
{-# NOINLINE dup2 #-}

