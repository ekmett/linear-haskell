{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Primitive.Linear.ByteArray
  ( -- * Mutable Linear Arrays
    ByteArray(ByteArray),
    -- * Performing Computations with Arrays
    alloc,
    allocBeside,
    fromList,
    -- * Modifications
    set,
    unsafeSet,
    resize,
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


import Data.Primitive.Linear.Unlifted.ByteArray (ByteArray#)
import Data.Primitive.Linear.Unlifted.ByteArray qualified as Unlifted
import Data.Primitive.Types
import Data.Unrestricted.Linear
import GHC.Stack
import Prelude hiding (read)
import Prelude.Linear ((&))
import Data.Primitive.ByteArray qualified as Prim

-- # Data types
-------------------------------------------------------------------------------

data ByteArray = ByteArray ByteArray#

-- # Creation
-------------------------------------------------------------------------------

-- | Allocate a constant array given a size and an initial value
-- The size must be non-negative, otherwise this errors.
alloc :: HasCallStack => Int -> (ByteArray %1 -> Ur b) %1 -> Ur b
alloc s f
  | s < 0 =
    (error ("ByteArray.alloc: negative size: " ++ show s) :: x %1-> x)
    (f undefined)
  | otherwise = Unlifted.alloc s (\arr -> f (ByteArray arr))

-- | Allocate a constant array given a size and an initial value,
-- using another array as a uniqueness proof.
allocBeside :: Int -> ByteArray %1 -> (ByteArray, ByteArray)
allocBeside s (ByteArray orig)
  | s < 0 = Unlifted.lseq
    orig
    (error ("ByteArray.allocBeside: negative size: " ++ show s))
  | otherwise = wrap (Unlifted.allocBeside s orig) where
    wrap :: (# ByteArray#, ByteArray# #) %1-> (ByteArray, ByteArray)
    wrap (# orig', new #) = (ByteArray orig', ByteArray new)

-- | Allocate an array from a list
fromList :: forall a b. (Prim a, HasCallStack) => [a] -> (ByteArray %1 -> Ur b) %1-> Ur b
fromList list (f :: ByteArray %1 -> Ur b) =
  alloc
    (Prelude.length list * sizeOf (undefined :: a))
    (\arr -> f (insert arr))
 where
  insert :: ByteArray %1 -> ByteArray
  insert = doWrites (zip list [0..])

  doWrites :: [(a,Int)] -> ByteArray %1-> ByteArray
  doWrites [] arr = arr
  doWrites ((a,ix):xs) arr = doWrites xs (unsafeSet ix a arr)

-- # Mutations and Reads
-------------------------------------------------------------------------------

size :: ByteArray %1 -> (Ur Int, ByteArray)
size (ByteArray arr) = f (Unlifted.size arr) where
  f :: (# Ur Int, ByteArray# #) %1-> (Ur Int, ByteArray)
  f (# s, a #) = (s, ByteArray a)

-- | Sets the value of an index. The index should be less than the arrays
-- size, otherwise this errors.
set :: forall a. (Prim a, HasCallStack) => Int -> a -> ByteArray %1 -> ByteArray
set i x arr = unsafeSet i x (assertIndexInRange (sizeOf (undefined :: a)) i arr)

-- | Same as 'set, but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeSet :: forall a. Prim a => Int -> a -> ByteArray %1-> ByteArray
unsafeSet ix val (ByteArray arr) = ByteArray (Unlifted.set ix val arr)

-- | Get the value of an index. The index should be less than the arrays 'size',
-- otherwise this errors.
get :: forall a. (Prim a, HasCallStack) => Int -> ByteArray %1-> (Ur a, ByteArray)
get i arr = unsafeGet i (assertIndexInRange (sizeOf (undefined :: a)) i arr)

-- | Same as 'get', but does not do bounds-checking. The behaviour is undefined
-- if an out-of-bounds index is provided.
unsafeGet :: Prim a => Int -> ByteArray %1 -> (Ur a, ByteArray)
unsafeGet ix (ByteArray arr) = wrap (Unlifted.get ix arr) where
  wrap :: (# Ur a, ByteArray# #) %1 -> (Ur a, ByteArray)
  wrap (# ret, arr' #) = (ret, ByteArray arr')

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
--
-- TODO: use shrinkMutableByteArray# if the new size is smaller than the current one
resize :: HasCallStack => Int -> ByteArray %1 -> ByteArray
resize newSize (ByteArray arr :: ByteArray)
  | newSize < 0 = Unlifted.lseq arr (error "Trying to resize to a negative size.")
  | otherwise = doCopy (Unlifted.allocBeside newSize arr) where
      doCopy :: (# ByteArray#, ByteArray# #) %1 -> ByteArray
      doCopy (# new, old #) = wrap (Unlifted.copyInto 0 old new)

      wrap :: (# ByteArray#, ByteArray# #) %1 -> ByteArray
      wrap (# src, dst #) = src `Unlifted.lseq` ByteArray dst

-- | Return the array elements as a lazy list.
toList :: Prim a => ByteArray %1 -> Ur [a]
toList (ByteArray arr) = Unlifted.toList arr

-- | Copy a slice of the array, starting from given offset and copying given
-- number of elements. Returns the pair (oldByteArray, slice).
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
  -> ByteArray %1-> (ByteArray, ByteArray)
slice from targetSize arr =
  size arr & \case
    (Ur s, ByteArray old)
      | s < from + targetSize ->
          Unlifted.lseq
            old
            (error "Slice index out of bounds.")
      | otherwise ->
          doCopy
            (Unlifted.allocBeside
               targetSize
               old)
  where
    doCopy :: (# ByteArray#, ByteArray# #) %1 -> (ByteArray, ByteArray)
    doCopy (# new, old #) = wrap (Unlifted.copyInto from old new)

    wrap :: (# ByteArray#, ByteArray# #) %1 -> (ByteArray, ByteArray)
    wrap (# old, new #) = (ByteArray old, ByteArray new)

-- | /O(1)/ Convert an 'ByteArray' to an immutable 'Vector.Vector' (from
-- 'vector' package).
freeze :: ByteArray %1 -> Ur Prim.ByteArray
freeze (ByteArray arr) = Unlifted.freeze Prim.ByteArray arr

-- # Mutation-style API
-------------------------------------------------------------------------------

-- | Same as 'set', but takes the 'ByteArray' as the first parameter.
write :: (Prim a, HasCallStack) => ByteArray %1 -> Int -> a -> ByteArray
write arr i a = set i a arr

-- | Same as 'unsafeSet', but takes the 'ByteArray' as the first parameter.
unsafeWrite :: Prim a => ByteArray %1 -> Int -> a -> ByteArray
unsafeWrite arr i a = unsafeSet i a arr

-- | Same as 'get', but takes the 'ByteArray' as the first parameter.
read :: (Prim a, HasCallStack) => ByteArray %1 -> Int -> (Ur a, ByteArray)
read arr i = get i arr

-- | Same as 'unsafeGet', but takes the 'ByteArray' as the first parameter.
unsafeRead :: Prim a => ByteArray %1 -> Int -> (Ur a, ByteArray)
unsafeRead arr i = unsafeGet i arr

-- # Instances
-------------------------------------------------------------------------------

instance Consumable ByteArray where
  consume :: ByteArray %1 -> ()
  consume (ByteArray arr) = arr `Unlifted.lseq` ()

instance Dupable ByteArray where
  dup2 :: ByteArray %1 -> (ByteArray, ByteArray)
  dup2 (ByteArray arr) = wrap (Unlifted.dup2 arr) where
    wrap :: (# ByteArray#, ByteArray# #) %1 -> (ByteArray, ByteArray)
    wrap (# a1, a2 #) = (ByteArray a1, ByteArray a2)

-- # Internal library
-------------------------------------------------------------------------------

-- | Check if given index is within the ByteArray, otherwise panic.
assertIndexInRange :: HasCallStack => Int -> Int -> ByteArray %1 -> ByteArray
assertIndexInRange by i arr =
  size arr & \(Ur s, arr') ->
    if 0 <= i && i < div s by
    then arr'
    else arr' `lseq` error "ByteArray: index out of bounds"
