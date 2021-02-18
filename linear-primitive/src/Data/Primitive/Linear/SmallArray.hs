{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- |
-- This module provides a pure linear interface for arrays with in-place
-- mutation.
--
-- To use these mutable arrays, create a linear computation of type
-- @SmallArray a %1-> Ur b@ and feed it to 'alloc' or 'fromList'.
--
-- == A Tiny Example
--
-- >>> :set -XLinearTypes
-- >>> :set -XNoImplicitPrelude
-- >>> import Prelude.Linear
-- >>> import qualified Data.SmallArray.Mutable.Linear as SmallArray
-- >>> :{
--  isFirstZero :: SmallArray.SmallArray Int %1-> Ur Bool
--  isFirstZero arr =
--    SmallArray.get 0 arr
--      & \(Ur val, arr') -> arr' `lseq` Ur (val == 0)
-- :}
--
-- >>> unur $ SmallArray.fromList [0..10] isFirstZero
-- True
-- >>> unur $ SmallArray.fromList [1,2,3] isFirstZero
-- False
module Data.Primitive.Linear.SmallArray
  ( -- * Mutable Linear SmallArrays
    SmallArray,
    -- * Performing Computations with SmallArrays
    alloc,
    allocBeside,
    fromList,
    -- * Modifications
    set,
    unsafeSet,
    resize,
    map,
    -- * Accessors
    get,
    unsafeGet,
    size,
    slice,
    toList,
    freeze,
    -- * Mutable-style interface
    read,
    unsafeRead,
    write,
    unsafeWrite
  )
where

import Data.Unrestricted.Linear
import GHC.Stack
import Data.Primitive.Linear.Unlifted.SmallArray (SmallArray#)
import qualified Data.Primitive.Linear.Unlifted.SmallArray as Unlifted
import qualified Data.Functor.Linear as Data
import Prelude.Linear ((&), forget)
import qualified Data.Primitive.SmallArray as Prim
import Prelude hiding (read, map)

-- # Data types
-------------------------------------------------------------------------------

data SmallArray a = SmallArray (SmallArray# a)

-- # Creation
-------------------------------------------------------------------------------

-- | Allocate a constant array given a size and an initial value
-- The size must be non-negative, otherwise this errors.
alloc :: HasCallStack => Int -> a -> (SmallArray a %1 -> Ur b) %1-> Ur b
alloc s x f
  | s < 0 =
    (error ("SmallArray.alloc: negative size: " ++ show s) :: x %1-> x)
    (f undefined)
  | otherwise = Unlifted.alloc s x (\arr -> f (SmallArray arr))

-- | Allocate a constant array given a size and an initial value,
-- using another array as a uniqueness proof.
allocBeside :: Int -> a -> SmallArray b %1 -> (SmallArray a, SmallArray b)
allocBeside s x (SmallArray orig)
  | s < 0 = Unlifted.lseq
    orig
    (error ("SmallArray.allocBeside: negative size: " ++ show s))
  | otherwise = wrap (Unlifted.allocBeside s x orig) where
    wrap :: (# SmallArray# a, SmallArray# b #) %1-> (SmallArray a, SmallArray b)
    wrap (# orig, new #) = (SmallArray orig, SmallArray new)

-- | Allocate an array from a list
fromList :: HasCallStack => [a] -> (SmallArray a %1-> Ur b) %1-> Ur b
fromList list (f :: SmallArray a %1-> Ur b) =
  alloc
    (Prelude.length list)
    (error "invariant violation: unintialized array position")
    (\arr -> f (insert arr))
 where
  insert :: SmallArray a %1-> SmallArray a
  insert = doWrites (zip list [0..])

  doWrites :: [(a,Int)] -> SmallArray a %1-> SmallArray a
  doWrites [] arr = arr
  doWrites ((a,ix):xs) arr = doWrites xs (unsafeSet ix a arr)

-- # Mutations and Reads
-------------------------------------------------------------------------------

size :: SmallArray a %1-> (Ur Int, SmallArray a)
size (SmallArray arr) = f (Unlifted.size arr) where
  f :: (# Ur Int, SmallArray# a #) %1-> (Ur Int, SmallArray a)
  f (# s, arr #) = (s, SmallArray arr)

-- | Sets the value of an index. The index should be less than the arrays
-- size, otherwise this errors.
set :: HasCallStack => Int -> a -> SmallArray a %1 -> SmallArray a
set i x arr = unsafeSet i x (assertIndexInRange i arr)

-- | Same as 'set, but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: Int -> a -> SmallArray a %1 -> SmallArray a
unsafeSet ix val (SmallArray arr) = SmallArray (Unlifted.set ix val arr)

-- | Get the value of an index. The index should be less than the arrays 'size',
-- otherwise this errors.
get :: HasCallStack => Int -> SmallArray a %1 -> (Ur a, SmallArray a)
get i arr = unsafeGet i (assertIndexInRange i arr)

-- | Same as 'get', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeGet :: Int -> SmallArray a %1-> (Ur a, SmallArray a)
unsafeGet ix (SmallArray arr) = wrap (Unlifted.get ix arr) where
  wrap :: (# Ur a, SmallArray# a #) %1-> (Ur a, SmallArray a)
  wrap (# ret, arr #) = (ret, SmallArray arr)

-- | Resize an array. That is, given an array, a target size, and a seed
-- value; resize the array to the given size using the seed value to fill
-- in the new cells when necessary and copying over all the unchanged cells.
--
-- Target size should be non-negative.
--
-- @
-- let b = resize n x a,
--   then size b = n,
--   and b[i] = a[i] for i < size a,
--   and b[i] = x for size a <= i < n.
-- @
resize :: HasCallStack => Int -> a -> SmallArray a %1-> SmallArray a
resize newSize seed (SmallArray arr :: SmallArray a)
  | newSize < 0 = Unlifted.lseq arr (error "Trying to resize to a negative size.")
  | otherwise = doCopy (Unlifted.allocBeside newSize seed arr) where
      doCopy :: (# SmallArray# a, SmallArray# a #) %1-> SmallArray a
      doCopy (# new, old #) = wrap (Unlifted.copyInto 0 old new)

      wrap :: (# SmallArray# a, SmallArray# a #) %1-> SmallArray a
      wrap (# src, dst #) = src `Unlifted.lseq` SmallArray dst


-- | Return the array elements as a lazy list.
toList :: SmallArray a %1-> Ur [a]
toList (SmallArray arr) = Unlifted.toList arr

-- | Copy a slice of the array, starting from given offset and copying given
-- number of elements. Returns the pair (oldSmallArray, slice).
--
-- Start offset + target size should be within the input array, and both should
-- be non-negative.
--
-- @
-- let b = slice i n a,
--   then size b = n,
--   and b[j] = a[i+j] for 0 <= j < n
-- @
slice
  :: HasCallStack
  => Int -- ^ Start offset
  -> Int -- ^ Target size
  -> SmallArray a %1-> (SmallArray a, SmallArray a)
slice from targetSize arr =
  size arr & \case
    (Ur s, SmallArray old)
      | s < from + targetSize ->
          Unlifted.lseq
            old
            (error "Slice index out of bounds.")
      | otherwise ->
          doCopy
            (Unlifted.allocBeside
               targetSize
               (error "invariant violation: uninitialized array index")
               old)
  where
    doCopy :: (# SmallArray# a, SmallArray# a #) %1-> (SmallArray a, SmallArray a)
    doCopy (# new, old #) = wrap (Unlifted.copyInto from old new)

    wrap :: (# SmallArray# a, SmallArray# a  #) %1-> (SmallArray a, SmallArray a)
    wrap (# old, new #) = (SmallArray old, SmallArray new)

-- | /O(1)/ Convert an 'SmallArray' to an immutable 'Vector.Vector' (from
-- 'vector' package).
freeze :: SmallArray a %1-> Ur (Prim.SmallArray a)
freeze (SmallArray arr) = Unlifted.freeze Prim.SmallArray arr

map :: (a -> b) -> SmallArray a %1-> SmallArray b
map f (SmallArray arr) = SmallArray (Unlifted.map f arr)

-- # Mutation-style API
-------------------------------------------------------------------------------

-- | Same as 'set', but takes the 'SmallArray' as the first parameter.
write :: HasCallStack => SmallArray a %1-> Int -> a -> SmallArray a
write arr i a = set i a arr

-- | Same as 'unsafeSet', but takes the 'SmallArray' as the first parameter.
unsafeWrite ::  SmallArray a %1-> Int -> a -> SmallArray a
unsafeWrite arr i a = unsafeSet i a arr

-- | Same as 'get', but takes the 'SmallArray' as the first parameter.
read :: HasCallStack => SmallArray a %1-> Int -> (Ur a, SmallArray a)
read arr i = get i arr

-- | Same as 'unsafeGet', but takes the 'SmallArray' as the first parameter.
unsafeRead :: SmallArray a %1-> Int -> (Ur a, SmallArray a)
unsafeRead arr i = unsafeGet i arr

-- # Instances
-------------------------------------------------------------------------------

instance Consumable (SmallArray a) where
  consume :: SmallArray a %1 -> ()
  consume (SmallArray arr) = arr `Unlifted.lseq` ()

instance Dupable (SmallArray a) where
  dup2 :: SmallArray a %1 -> (SmallArray a, SmallArray a)
  dup2 (SmallArray arr) = wrap (Unlifted.dup2 arr) where
    wrap :: (# SmallArray# a, SmallArray# a #) %1-> (SmallArray a, SmallArray a)
    wrap (# a1, a2 #) = (SmallArray a1, SmallArray a2)

instance Data.Functor SmallArray where
  fmap f arr = map (forget f) arr

-- # Internal library
-------------------------------------------------------------------------------

-- | Check if given index is within the SmallArray, otherwise panic.
assertIndexInRange :: HasCallStack => Int -> SmallArray a %1-> SmallArray a
assertIndexInRange i arr =
  size arr & \(Ur s, arr') ->
    if 0 <= i && i < s
    then arr'
    else arr' `lseq` error "SmallArray: index out of bounds"
