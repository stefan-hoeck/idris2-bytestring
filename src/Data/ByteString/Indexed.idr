module Data.ByteString.Indexed

import Algebra.Solver.Semiring
import Data.Buffer.Indexed
import Data.Nat.BSExtra
import System.File

%default total

--------------------------------------------------------------------------------
--          ByteString
--------------------------------------------------------------------------------

||| Internally represented by a `Data.Buffer` together
||| with its length and offset.
|||
||| The internal buffer is treated as being immutable,
||| so operations modifying a `ByteString` will create
||| and write to a new `Buffer`.
export
data ByteString : Nat -> Type where
  BS :  (buf    : IBuffer bufLen)
     -> (offset : Nat)
     -> (0 lte  : LTE (offset + len) bufLen)
     -> ByteString len

||| Reads the value of a `ByteString` at the given position
export
getByte : (x : Nat) -> (0 lt : LT x n) => ByteString n -> Bits8
getByte x (BS buf o lte) =
  byteAt (o + x) buf {lt = transitive (ltPlusRight o lt) lte}

||| Reads the value of a `ByteString` at the given position
export
getByteFromEnd : {n : _} -> (x : Nat) -> (0 lt : LT x n) => ByteString n -> Bits8
getByteFromEnd x (BS buf o lte) =
  byteFromEnd {end = o+n} x {lt = lteAddLeft o lt} buf

||| Reads the value of a `ByteString` at the given position
export %inline
index : Index n -> ByteString n -> Bits8
index (Element k _) bs = getByte k bs

||| Reads the value of a `ByteString` at the given position
export %inline
indexFromEnd : {n : _} -> Index n -> ByteString n -> Bits8
indexFromEnd (Element x _) bs = getByteFromEnd x bs

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

||| The empty `ByteString`.
export
empty : ByteString 0
empty = BS empty 0 %search

||| Converts a list of values to a `ByteString` using
||| the given conversion function. O(n).
export
fromList : (a -> Bits8) -> (as : List a) -> ByteString (length as)
fromList f as = BS (fromList f as) 0 reflexive

||| Converts a list of `Bits8` values to a `ByteString`.
export %inline
pack : (as : List Bits8) -> ByteString (length as)
pack = fromList id

||| Creates a `ByteString` holding a single `Bits8` value.
export %inline
singleton : Bits8 -> ByteString 1
singleton v = pack [v]

||| Convert a `ByteString` to a list of values using
||| the given conversion function.
export
toList : {n : _} -> (Bits8 -> a) -> ByteString n -> List a
toList f bs     = go Nil n
  where go : List a -> (x : Nat) -> (0 prf : LTE x n) => List a
        go xs 0     = xs
        go xs (S j) = go (f (getByte j bs) :: xs) j

||| Converts a `ByteString` to a list of `Bits8` values. O(n).
export %inline
unpack : {n : _} -> ByteString n -> List Bits8
unpack = toList id

||| Converts a `ByteString` to a String. All characters
||| will be in the range [0,255], so this does not perform
||| any character decoding.
export %inline
{n : Nat} -> Show (ByteString n) where
  showPrec p bs = showCon p "pack" (showArg $ toList id bs)

--------------------------------------------------------------------------------
--          Comparing ByteStrings
--------------------------------------------------------------------------------

||| Lexicographic comparison of `ByteString`s of distinct length
export
hcomp : {m,n : Nat} -> ByteString m -> ByteString n -> Ordering
hcomp (BS {bufLen = bl1} b1 o1 _) (BS {bufLen = bl2} b2 o2 _) = go m o1 n o2
  where go : (c1,o1,c2,o2 : Nat)
           -> (0 _ : Offset c1 o1 bl1)
           => (0 _ : Offset c2 o2 bl2)
           => Ordering
        go 0     _  0     _  = EQ
        go 0     _  (S _) _  = LT
        go (S _) _  0     _  = GT
        go (S k) o1 (S j) o2 = case compare (byteAtO o1 b1) (byteAtO o2 b2) of
          EQ => go k (S o1) j (S o2)
          r  => r

||| Heterogeneous equality for `ByteString`s
export
heq : {m,n : Nat} -> ByteString m -> ByteString n -> Bool
heq bs1 bs2 = hcomp bs1 bs2 == EQ

--------------------------------------------------------------------------------
--          Core Functionality
--------------------------------------------------------------------------------

export
generate : (n : Nat) -> (Index n -> Bits8) -> ByteString n
generate n f = BS (generate n f) 0 refl

export
generateMaybe : (n : Nat) -> (Index n -> Maybe Bits8) -> (k ** ByteString k)
generateMaybe n f =
  let (k ** buf) := Buffer.Indexed.generateMaybe n f
   in (k ** BS buf 0 refl)

export
replicate : (n : Nat) -> Bits8 -> ByteString n
replicate n = generate n . const

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------

||| Concatenate a list of `ByteString`. This allocates
||| a buffer of sufficient size in advance, so it is much
||| faster than `concat`, or `concatMap` for large `ByteString`s.
export
fastConcat :  (bs : List (n ** ByteString n))
           -> ByteString (totLength bs)
fastConcat bs = BS (concatMany bs index) 0 refl

||| Concatenate two `ByteString`s. O(n + m).
export
append : {m,n : _} -> ByteString m  -> ByteString n -> ByteString (m + n)
append b1 b2 =
  let 0 pp := solve [m,n]
                (m .+ (n .+ 0))
                (m .+. n)
   in replace {p = ByteString} pp $ fastConcat [(m ** b1),(n ** b2)]

||| Prepend a single `Bits8` to a `ByteString`. O(n).
export %inline
cons : {n : _} -> Bits8 -> ByteString n -> ByteString (S n)
cons = append . singleton

||| Append a single `Bits8` to a `ByteString`. O(n).
export %inline
snoc : {n : _} -> Bits8 -> ByteString n -> ByteString (n + 1)
snoc w bs = bs `append` singleton w

--------------------------------------------------------------------------------
--          Inspecting ByteStrings
--------------------------------------------------------------------------------

||| Read the first element of a `ByteString`. O(1).
export
head : ByteString (S n) -> Bits8
head = getByte 0

||| Drop the first `Bits8` from a `ByteString`. O(1).
export
tail : ByteString (S n) -> ByteString n
tail (BS buf o p) = BS buf (S o) (ltePlusSuccRight p)

||| Split the first `Bits8` from a `ByteString`. O(1).
export
uncons : ByteString (S n) -> (Bits8, ByteString n)
uncons bs = (head bs, tail bs)

||| Read the last `Bits8` from a `ByteString`. O(1).
export
last : {n : _} -> ByteString (S n) -> Bits8
last = getByte n

||| Drop the last `Bits8` from a `ByteString`. O(1).
export
init : ByteString (S n) -> ByteString n
init (BS buf o p) = BS buf o (lteSuccLeft $ ltePlusSuccRight p)

||| The last `Bits8` from a `ByteString`. O(1).
export
unsnoc : {n : _} -> ByteString (S n) -> (Bits8, ByteString n)
unsnoc bs = (last bs, init bs)

--------------------------------------------------------------------------------
--          Mapping ByteStrings
--------------------------------------------------------------------------------

||| Converts every `Bits8` in a `ByteString` by applying the given
||| function. O(n).
export
map : {n : _} -> (Bits8 -> Bits8) -> ByteString n -> ByteString n
map f bs = generate n (\x => f $ index x bs)

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every lower-case character to its upper-case form.
export
toUpper : {n : _} -> ByteString n -> ByteString n
toUpper = map (cast . Prelude.toUpper . cast)

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every upper-case character to its lower-case form.
export
toLower : {n : _} -> ByteString n -> ByteString n
toLower = map (cast . Prelude.toLower . cast)

export
reverse : {n : _} -> ByteString n -> ByteString n
reverse bs = generate n (\x => indexFromEnd x bs)

||| True, if the predicate holds for all bytes in the given `ByteString`
export
all : {n : _} -> (Bits8 -> Bool) -> ByteString n -> Bool
all p (BS {bufLen} buf off lte) = go n off
  where go : (c, o : Nat) -> (0 off : Offset c o bufLen) => Bool
        go 0     o = True
        go (S k) o = if p (byteAtO o buf) then go k (S o) else False

||| True, if the predicate holds for at least one byte
||| in the given `ByteString`
export
any : {n : _} -> (Bits8 -> Bool) -> ByteString n -> Bool
any p (BS {bufLen} buf off lte) = go n off
  where go : (c, o : Nat) -> (0 _ : Offset c o bufLen) => Bool
        go 0     o = False
        go (S k) o = if p (byteAtO o buf) then True else go k (S o)


||| True, if the given `Bits8` appears in the `ByteString`.
export %inline
elem : {n : _} -> Bits8 -> ByteString n -> Bool
elem b = any (b ==)

export
foldl : {n : _} -> (a -> Bits8 -> a) -> a -> ByteString n -> a
foldl f ini (BS {bufLen} buf off lte) = go n off ini
  where go : (c,o : Nat) -> (v : a) -> (0 _ : Offset c o bufLen) => a
        go 0     o v = v
        go (S k) o v = go k (S o) (f v $ byteAtO o buf)

export
foldr : {n : _} -> (Bits8 -> a -> a) -> a -> ByteString n -> a
foldr f ini bs = go n ini
  where go : (k : Nat) -> (v : a) -> (0 lt : LTE k n) => a
        go 0     v = v
        go (S k) v = go k (f (getByte k bs) v)

||| The `findIndex` function takes a predicate and a `ByteString` and
||| returns the index of the first element in the ByteString
||| satisfying the predicate.
export
findIndex :  {n : _}
          -> (Bits8 -> Bool)
          -> ByteString n
          -> Maybe (Subset Nat (`LT` n))
findIndex p (BS {bufLen} buf off _) = go n off
  where go :  (c,o : Nat)
           -> (0 _ : Offset c o bufLen)
           => (0 _ : LTE c n)
           => Maybe (Index n)
        go 0     _ = Nothing
        go (S k) o = case p (byteAtO o buf) of
          True  => Just $ toEndIndex k
          False => go k (S o)

||| Return the index of the first occurence of the given
||| byte in the `ByteString`, or `Nothing`, if the byte
||| does not appear in the ByteString.
export
elemIndex : {n : _} -> Bits8 -> ByteString n -> Maybe (Index n)
elemIndex c = findIndex (c ==)

export
find : {n : _} -> (Bits8 -> Bool) -> ByteString n -> Maybe Bits8
find p bs = (`index` bs) <$> findIndex p bs

--------------------------------------------------------------------------------
--          Substrings
--------------------------------------------------------------------------------

findIndexOrLength :  {n : _}
                  -> (Bits8 -> Bool)
                  -> ByteString n
                  -> SubLength n
findIndexOrLength p (BS {bufLen} buf off _) = go n off
  where go :  (c,o : Nat)
           -> (0 _ : Offset c o bufLen)
           => (0 _ : LTE c n)
           => SubLength n
        go 0     o = sublength n
        go (S k) o =
          if p (byteAtO o buf) then fromIndex (toEndIndex k) else go k (S o)

findIndexOrLengthNL : {n : _} -> ByteString n -> SubLength n
findIndexOrLengthNL (BS {bufLen} buf off _) = go n off
  where go :  (c,o : Nat)
           -> (0 _ : Offset c o bufLen)
           => (0 _ : LTE c n)
           => SubLength n
        go 0     o = sublength n
        go (S k) o = case byteAtO o buf of
          10 => fromIndex (toEndIndex k)
          _  => go k (S o)

findFromEndUntil : {n : _} -> (Bits8 -> Bool) -> ByteString n -> SubLength n
findFromEndUntil p bs = go n
  where go : (k : Nat) -> (0 lt : LTE k n) => SubLength n
        go 0     = Element 0 LTEZero
        go (S k) = if p (getByte k bs) then (Element (S k) lt) else go k

0 substrPrf : LTE (s + l) n -> LTE (o + n) n2 -> LTE ((o + s) + l) n2
substrPrf p q =
  let pp := rewrite sym (plusAssociative o s l) in ltePlusRight o p
   in transitive pp q

||| Like `substr` for `String`, this extracts a substring
||| of the given `ByteString` at the given start position
||| and of the given length. O(1).
export
substring :  (start,length : Nat)
          -> ByteString n
          -> (0 inBounds : LTE (start + length) n)
          => ByteString length
-- inBounds : start + len       <= n
-- p        : o + n             <= bufLen
-- required : (o + start) + len <= bufLen
substring start len (BS buf o p) =
  BS buf (o + start) (substrPrf inBounds p)

export
mapMaybe :  {n : _}
         -> (Bits8 -> Maybe Bits8)
         -> ByteString n
         -> (k ** ByteString k)
mapMaybe f bs = generateMaybe n (\x => f $ index x bs)

export
filter :  {n : _}
       -> (Bits8 -> Bool)
       -> ByteString n
       -> (k ** ByteString k)
filter p = mapMaybe (\b => if p b then Just b else Nothing)

||| Return a `ByteString` with the first `n` values of
||| the input string. O(1)
export
take : (0 k : Nat) -> (0 lt : LTE k n) => ByteString n -> ByteString k
take k (BS buf o p) =
  -- p        : o + n <= bufLen
  -- lt       : k     <= n
  -- required : o + k <= bufLen
  BS buf o (transitive (ltePlusRight o lt) p)

||| Return a `ByteString` with the last `n` values of
||| the input string. O(1)
export
takeEnd :  {n : _}
        -> (k : Nat)
        -> (0 lt : LTE k n)
        => ByteString n
        -> ByteString k
takeEnd k (BS buf o p) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : ((o + n) - k) + k <= bufLen
  let 0 q := plusMinus' k (o + n) (lteAddLeft o lt)
   in BS buf ((o + n) `minus` k) (rewrite q in p)

||| Remove the first `n` values from a `ByteString`. O(1)
export
drop :  (k : Nat)
     -> (0 lt : LTE k n)
     => ByteString n
     -> ByteString (n `minus` k)
drop k (BS buf o p) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : (o + k) + (n - k) <= bufLen
  let 0 q := cong (o +) (plusMinus k n lt)
      0 r := plusAssociative o k (n `minus` k)
   in BS buf (o + k) (rewrite (trans (sym r) q) in p)

||| Remove the last `n` values from a `ByteString`. O(1)
export
dropEnd :  (0 k : Nat)
        -> (0 lt : LTE k n)
        => ByteString n
        -> ByteString (n `minus` k)
dropEnd k (BS buf o p) =
  -- p        : o + n       <= bufLen
  -- lt       : k           <= n
  -- required : o + (n - k) <= bufLen
  BS buf o (transitive (ltePlusRight o $ minusLTE n k) p)

export
splitAt :  {n : _}
        -> (k : Nat)
        -> (0 lte : LTE k n)
        => ByteString n
        -> (ByteString k, ByteString (n `minus` k))
splitAt k bs = (take k bs, drop k bs)

||| Extracts the longest prefix of elements satisfying the
||| predicate.
export
takeWhile : {n : _} -> (Bits8 -> Bool) -> ByteString n -> (k ** ByteString k)
takeWhile p bs =
  let Element k _ = findIndexOrLength (not . p) bs
   in (k ** take k bs)

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate.
export
takeWhileEnd :  {n : _}
             -> (Bits8 -> Bool)
             -> ByteString n
             -> (k ** ByteString k)
takeWhileEnd f bs =
  let Element k _ = findFromEndUntil (not . f) bs
   in (_ ** drop k bs)

||| Drops the longest (possibly empty) prefix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhile :  {n : _}
          -> (Bits8 -> Bool)
          -> ByteString n
          -> (k ** ByteString k)
dropWhile f bs =
  let Element k _ = findIndexOrLength (not . f) bs
   in (_ ** drop k bs)

||| Drops the longest (possibly empty) suffix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhileEnd :  {n : _}
             -> (Bits8 -> Bool)
             -> ByteString n
             -> (k ** ByteString k)
dropWhileEnd f bs =
  let Element k _ = findFromEndUntil (not . f) bs
   in (k ** take k bs)

public export
record BreakRes (n : Nat) where
  constructor MkBreakRes
  lenFst : Nat
  lenSnd : Nat
  fst    : ByteString lenFst
  snd    : ByteString lenSnd
  0 prf  : lenFst + lenSnd === n

||| Returns the longest (possibly empty) prefix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
break :  {n : _}
      -> (Bits8 -> Bool)
      -> ByteString n
      -> BreakRes n
break p bs =
  let Element k _ = findIndexOrLength p bs
      bs1 = take k bs
      bs2 = drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinus k n %search)

||| Returns the longest (possibly empty) prefix before the first newline character
export
breakNL : {n : _} -> ByteString n -> BreakRes n
breakNL bs =
  let Element k _ = findIndexOrLengthNL bs
      bs1 = take k bs
      bs2 = drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinus k n %search)

||| Returns the longest (possibly empty) suffix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
breakEnd :  {n : _}
         -> (Bits8 -> Bool)
         -> ByteString n
         -> BreakRes n
breakEnd  p bs =
  let Element k _ = findFromEndUntil p bs
      bs1 = take k bs
      bs2 = drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinus k n %search)

||| Returns the longest (possibly empty) prefix of elements
||| satisfying the predicate and the remainder of the string.
export %inline
span :  {n : _}
     -> (Bits8 -> Bool)
     -> ByteString n
     -> BreakRes n
span p = break (not . p)

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate and the remainder of the string.
export
spanEnd :  {n : _}
        -> (Bits8 -> Bool)
        -> ByteString n
        -> BreakRes n
spanEnd p bs =
  let Element k _ = findFromEndUntil (not . p) bs
      bs1 = take k bs
      bs2 = drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinus k n %search)

0 splitWithLemma : (k,m,n : Nat) -> k + m === n -> LTE m n
splitWithLemma 0     0     0     p = LTEZero
splitWithLemma 0     (S x) (S y) p =
  LTESucc $ splitWithLemma 0 x y (injective p)
splitWithLemma (S k) m     (S y) p =
  lteSuccRight $ splitWithLemma k m y (injective p)
splitWithLemma 0     0     (S y) p impossible
splitWithLemma 0     (S x) 0     p impossible
splitWithLemma (S k) m     0     p impossible

||| Splits a 'ByteString' into components delimited by
||| separators, where the predicate returns True for a separator element.
||| The resulting components do not contain the separators. Two adjacent
||| separators result in an empty component in the output. eg.
export
splitWith :  {n : _}
          -> (Bits8 -> Bool)
          -> ByteString n
          -> List (k ** ByteString k)
splitWith p bs = go n 0 0 (plusZeroRightNeutral n) Lin
  where go :  (x,o,l : Nat)
           -> (0 prf : x + (o + l) === n)
           -> (0 lt  : LTE x n)
           => SnocList (k ** ByteString k)
           -> List (k ** ByteString k)
        go 0     o l prf sb =
          let 0 lemma := splitWithLemma 0 (o + l) n prf
           in sb <>> [(_ ** substring o l bs)]
        go (S k) o l prf sb = case p (getByteFromEnd k bs) of
          False =>
            let 0 pp := solve [o, l, k]
                         (k .+ (o .+ (1 +. l)))
                         (1 + (k .+ (o .+. l)))
             in go k o (S l) (trans pp prf) sb
          True  =>
            let 0 lemma := splitWithLemma (S k) (o + l) n prf
                0 pp := solve [o, l, k]
                         (k .+ ((o .+ (1 +. l)) + 0))
                         (1 + (k .+ (o .+. l)))
             in go k (o + S l) 0 (trans pp prf) (sb :< (_ ** substring o l bs))

||| Break a `ByteString` into pieces separated by the byte
||| argument, consuming the delimiter.
|||
||| As for all splitting functions in this library, this function does
||| not copy the substrings, it just constructs new `ByteString`s that
||| are slices of the original.
export
split : {n : _} -> Bits8 -> ByteString n -> List (k ** ByteString k)
split b = splitWith (b ==)

--------------------------------------------------------------------------------
--          Reading and Writing from and to Files
--------------------------------------------------------------------------------

export
readByteString :  HasIO io
               => Nat
               -> File
               -> io (Either FileError (k ** ByteString k))
readByteString max f = do
  Right (k ** buf) <- readBuffer max f | Left err => pure (Left err)
  pure $ Right (k ** BS buf 0 refl)

export
writeByteString :  {n : _}
                -> HasIO io
                => File
                -> ByteString n
                -> io (Either (FileError,Int) ())
writeByteString h (BS buf o _) = writeBuffer h o n buf
