module Data.Buffer.Index

import public Data.DPair
import public Data.Nat
import Data.Nat.BSExtra

%default total

--------------------------------------------------------------------------------
--          Index
--------------------------------------------------------------------------------

||| An efficient alternative to `Fin n`.
||| This allows for safe and efficient indexing into
||| length indexed arrays and buffers.
public export
0 Index : Nat -> Type
Index n = Subset Nat (`LT` n)

public export
refineIndex : {n : Nat} -> (k : Nat) -> Maybe (Index n)
refineIndex k with (compare k n) proof eq
  _ | LT = Just (Element k $ compLTisLT k n eq)
  _ | _  = Nothing

public export
toIndex : (k : Nat) -> (0 lt : LT k n) => Index n
toIndex k = Element k lt

||| Calculates the complement of an `Index`.
||| This allows us to index into a container
||| "from the other end".
public export
complement : {n : _} -> Index n -> Index n
complement (Element k lt) = Element (n `minus` S k) (minusLT k n lt)

||| This type is used to cut off a portion of
||| a `ByteString`. It must be no larger than the number
||| of elements in the ByteString
public export
0 SubLength : Nat -> Type
SubLength n = Subset Nat (`LTE` n)

public export
sublength : (k : Nat) -> (0 lte : LTE k n) => SubLength n
sublength k = Element k lte

public export
fromIndex : Index n -> SubLength n
fromIndex (Element k _) = Element k %search
