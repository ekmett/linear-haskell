{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Same API as @Data.Array.Mutable.Linear@, but freeze exports a Prim.Array
-- rather than a Vector, and the constructor is exposed to match the 
-- @primitive@ API's style
module Data.Primitive.Linear.Array
  ( -- * Mutable Linear Arrays
    Array(Array),
    -- * Performing Computations with Arrays
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
import Data.Array.Mutable.Linear hiding (freeze)
import Data.Array.Mutable.Linear.Internal (Array(Array))
import Data.Array.Mutable.Unlifted.Linear qualified as Unlifted
import Data.Primitive.Array qualified as Prim

freeze :: (Prim.Array a -> b) -> Array a %1 -> Ur b
freeze f (Array arr) = Unlifted.freeze (\m -> f (Prim.Array m)) arr
