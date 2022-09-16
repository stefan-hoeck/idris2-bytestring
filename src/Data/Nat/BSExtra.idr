||| This contains additional proofs on natural number.
module Data.Nat.BSExtra

import Algebra.Solver.Semiring
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

export
Uninhabited (EQ === LT) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.EQ === GT) where
  uninhabited Refl impossible

export
Uninhabited (LT === EQ) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.LT === GT) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.GT === LT) where
  uninhabited Refl impossible

export
Uninhabited (Prelude.GT === EQ) where
  uninhabited Refl impossible

export
0 compLTisLT : (m,n : Nat) -> compare m n === LT -> LT m n
compLTisLT 0 0         prf = absurd prf
compLTisLT 0     (S k) prf = LTESucc LTEZero
compLTisLT (S k) 0     prf = absurd prf
compLTisLT (S k) (S j) prf = LTESucc $ compLTisLT k j prf

export
0 compLT : (m,n : Nat) -> compare m n === LT -> LTE m n
compLT 0 0         prf = absurd prf
compLT 0     (S k) prf = LTEZero
compLT (S k) 0     prf = absurd prf
compLT (S k) (S j) prf = LTESucc $ compLT k j prf

export
0 compEQ : (m,n : Nat) -> compare m n === EQ -> LTE n m
compEQ 0 0         prf = LTEZero
compEQ 0     (S k) prf = absurd prf
compEQ (S k) 0     prf = absurd prf
compEQ (S k) (S j) prf = LTESucc $ compEQ k j prf

export
0 compEQ' : (m,n : Nat) -> compare m n === EQ -> LTE m n
compEQ' 0 0         prf = LTEZero
compEQ' 0     (S k) prf = absurd prf
compEQ' (S k) 0     prf = absurd prf
compEQ' (S k) (S j) prf = LTESucc $ compEQ' k j prf

export
0 compGT : (m,n : Nat) -> compare m n === GT -> LTE n m
compGT 0 0         prf = absurd prf
compGT 0     (S k) prf = absurd prf
compGT (S k) 0     prf = LTEZero
compGT (S k) (S j) prf = LTESucc $ compGT k j prf

||| A data type for holding erased proofs
public export
data Maybe0 : Type -> Type where
  Just0    : (0 v : t) -> Maybe0 t
  Nothing0 : Maybe0 t

export
tryLTE : (m,n : Nat) -> Maybe0 (LTE m n)
tryLTE m n with (compare m n) proof eq
  _ | LT = Just0 (compLT  m n eq)
  _ | EQ = Just0 (compEQ' m n eq)
  _ | GT = Nothing0

--------------------------------------------------------------------------------
--          Lemmata
--------------------------------------------------------------------------------

export
0 lteMinus : (n : Nat) -> LTE (S (minus n 0)) (S n)
lteMinus n = rewrite minusZeroRight n in reflexive

export
0 minusLTE : (m,n : Nat) -> LTE (m `minus` n) m
minusLTE 0 n         = LTEZero
minusLTE (S k) 0     = reflexive
minusLTE (S k) (S j) = lteSuccRight (minusLTE k j)

export
0 minusLT : (m,n : Nat) -> (lt : LT m n) -> LT (minus n (S m)) n
minusLT 0     (S l) lt           = lteMinus l
minusLT (S k) (S l) (LTESucc lt) =
  let lt' := minusLT k l lt in lteSuccRight lt'
minusLT 0     0     lt           = absurd lt

export %hint
0 refl : LTE n n
refl = reflexive

export %hint
0 lsl : (p : LTE (S m) n) => LTE m n
lsl = lteSuccLeft p

export
0 lteAddLeft : (x : Nat) -> LTE m n -> LTE m (x + n)
lteAddLeft 0 y = y
lteAddLeft (S k) y = lteSuccRight $ lteAddLeft k y

export
0 lteAddRight : (x : Nat) -> LTE m n -> LTE m (n + x)
lteAddRight x lt = rewrite plusCommutative n x in lteAddLeft x lt

export
0 ltPlusRight : (o : Nat) -> LT m n -> LT (o + m) (o + n)
ltPlusRight 0     lt = lt
ltPlusRight (S k) lt = LTESucc $ ltPlusRight k lt

export
0 ltPlusLeft : (o : Nat) -> LT m n -> LT (m + o) (n + o)
ltPlusLeft o p =
     rewrite plusCommutative m o
  in rewrite plusCommutative n o
  in ltPlusRight o p

export
0 ltePlusRight : (o : Nat) -> LTE m n -> LTE (o + m) (o + n)
ltePlusRight 0     lt = lt
ltePlusRight (S k) lt = LTESucc $ ltePlusRight k lt

export
0 ltePlusLeft : (o : Nat) -> LTE m n -> LTE (m + o) (n + o)
ltePlusLeft o p =
     rewrite plusCommutative m o
  in rewrite plusCommutative n o
  in ltePlusRight o p

export
0 ltPlusSuccRight : (k,m,n : Nat) -> LTE (k + S m) n -> LT k n
ltPlusSuccRight 0     m     (S z) (LTESucc _) = LTESucc LTEZero
ltPlusSuccRight (S x) m     (S z) (LTESucc p) =
  let p2 = ltPlusSuccRight x m z p in LTESucc p2

export
0 ltePlusSuccRight : {k,m,n : Nat} -> LTE (k + S m) n -> LTE (S $ k + m) n
ltePlusSuccRight p = rewrite plusSuccRightSucc k m in p

export
0 plusMinus : (m,n : Nat) -> LTE m n -> m + (n `minus` m) === n
plusMinus 0 0         _           = Refl
plusMinus 0 (S k)     x           = Refl
plusMinus (S k) 0     x           = absurd x
plusMinus (S k) (S j) (LTESucc p) = cong S $ plusMinus k j p

export
0 plusMinus' : (m,n : Nat) -> LTE m n -> (n `minus` m) + m === n
plusMinus' m n lt = trans (plusCommutative (n `minus` m) m) (plusMinus m n lt)

export
0 plusSuccLT : (k,m,n : Nat) -> LTE (S k + m) n -> LT m n
plusSuccLT 0     m n p = p
plusSuccLT (S x) m n p = plusSuccLT x m n $ lteSuccLeft p

export
0 eqToLTE : {a,b : Nat} -> a === b -> LTE a b
eqToLTE p = rewrite p in reflexive

export
0 sumEqLemma : (k,ix : Nat) -> S k + ix === n -> plus k (plus 1 ix) === n
sumEqLemma k ix prf =
  let pre := solve [k,ix,n] (k .+ (1 +. ix)) (1 + (k .+. ix))
   in trans pre prf

--------------------------------------------------------------------------------
--          Offset
--------------------------------------------------------------------------------

||| Offset lemmata
public export
data Offset : (count, offset, bufLen : Nat) -> Type where
  [search offset bufLen]
  I : {c,o,l : Nat} -> (0 p : LTE (o + c) l) -> Offset c o l
  N : Offset (S c) o l -> Offset c (S o) l

export
0 offsetToLTE : Offset c o l -> LTE (o+c) l
offsetToLTE (I p)  = p
offsetToLTE (N x) =
  let prf := solve [o,c] (o .+ (1 +. c)) (1 + (o .+. c))
      p2  := injective prf
  in rewrite sym p2 in offsetToLTE x

export
0 offsetLTE : (off : Offset (S c) o l) -> LT o l
offsetLTE off = ltPlusSuccRight o c l (offsetToLTE off)
