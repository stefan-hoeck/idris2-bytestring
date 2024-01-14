||| This contains additional proofs on natural number.
module Data.Nat.BSExtra

import Data.Array.Index
import Data.Fin
import Data.Maybe0
import Data.Nat

%default total

export
0 eqLTE : (m,n : Nat) -> m === n -> LTE m n
eqLTE 0     0     Refl = LTEZero
eqLTE (S k) (S k) Refl = LTESucc $ eqLTE k k Refl

export
0 ltPlusRight : {k,m,n : Nat} -> LT m n -> LT (k + m) (k + n)
ltPlusRight {k = 0}   x = x
ltPlusRight {k = S _} x = LTESucc $ ltPlusRight x

export
0 ltePlusSuccRight : {k,m,n : Nat} -> LTE (k + S m) n -> LTE (S $ k + m) n
ltePlusSuccRight p = rewrite plusSuccRightSucc k m in p

export
0 ltePlusRight : (o : Nat) -> LTE m n -> LTE (o + m) (o + n)
ltePlusRight 0     lt = lt
ltePlusRight (S k) lt = LTESucc $ ltePlusRight k lt

export
0 ltPlusSuccRight' : (k : Nat) -> LTE (k + S m) n -> LT m n
ltPlusSuccRight' 0     p           = p
ltPlusSuccRight' (S x) (LTESucc p) =
  lteSuccRight $ ltPlusSuccRight' x p

export
0 plusMinus : (m,n : Nat) -> LTE m n -> m + (n `minus` m) === n
plusMinus 0 0         _           = Refl
plusMinus 0 (S k)     x           = Refl
plusMinus (S k) 0     x           = absurd x
plusMinus (S k) (S j) (LTESucc p) = cong S $ plusMinus k j p

export
0 plusMinusLTE : (m,n : Nat) -> LTE m n -> LTE (m + (n `minus` m)) n
plusMinusLTE m n lte = eqLTE _ _ $ plusMinus m n lte

export
0 plusMinus' : (m,n : Nat) -> LTE m n -> (n `minus` m) + m === n
plusMinus' m n lt = trans (plusCommutative (n `minus` m) m) (plusMinus m n lt)

export
0 lteAddLeft : (x : Nat) -> LTE m n -> LTE m (x + n)
lteAddLeft 0 y = y
lteAddLeft (S k) y = lteSuccRight $ lteAddLeft k y

export
0 lteAddRight : (x : Nat) -> LTE m n -> LTE m (n + x)
lteAddRight x lt = rewrite plusCommutative n x in lteAddLeft x lt

export
tryLTE : {n : _} -> (k : Nat) -> Maybe0 (LT k n)
tryLTE k with (k < n) proof eq
  _ | True  = Just0 $ ltOpReflectsLT k n eq
  _ | False = Nothing0

export
0 concatLemma1 : {0 k,m,n : Nat} -> LTE (k + m) (k + (m+n))
concatLemma1 = rewrite plusAssociative k m n in lteAddRight _

export
0 concatLemma2 : {0 l,k,m,n : Nat} -> l+(k+m) === n -> (l+k)+m === n
concatLemma2 p1 = trans (sym $ plusAssociative l k m) p1

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
