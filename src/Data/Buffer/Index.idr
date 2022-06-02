module Data.Buffer.Index

import public Data.DPair
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Lemmata
--------------------------------------------------------------------------------

0 lteMinus : (n : Nat) -> LTE (S (minus n 0)) (S n)
lteMinus 0     = LTESucc LTEZero
lteMinus (S k) = reflexive

0 minusLT : (m,n : Nat) -> (lt : LT m n) -> LT (minus n (S m)) n
minusLT 0     (S l) lt           = lteMinus l
minusLT (S k) (S l) (LTESucc lt) =
  let lt' = minusLT k l lt in lteSuccRight lt'
minusLT 0     0     lt = absurd lt

%hint
0 refl : LTE n n
refl = reflexive

%hint
0 lsl : (p : LTE (S m) n) => LTE m n
lsl = lteSuccLeft p 

export
0 ltePlusRight : (o : Nat) -> LT m n -> LT (o + m) (o + n)
ltePlusRight 0     lt = lt
ltePlusRight (S k) lt = LTESucc $ ltePlusRight k lt


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
