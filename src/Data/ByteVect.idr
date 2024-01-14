module Data.ByteVect

import Control.WellFounded
import Data.Buffer
import Data.Buffer.Mutable
import Data.Nat.BSExtra

import public Data.Buffer.Core
import public Data.Buffer.Indexed
import public Data.Byte

%default total

||| An immutable, length-indexed byte vector.
|||
||| Internally represented by a `Data.Buffer` together
||| with its length and offset.
|||
||| The internal buffer is treated as being immutable,
||| so operations modifying a `ByteVect` will create
||| and write to a new `Buffer`.
public export
data ByteVect : Nat -> Type where
  BV :  (buf    : IBuffer bufLen)
     -> (offset : Nat)
     -> (0 lte  : LTE (offset + len) bufLen)
     -> ByteVect len

||| An immutable string of raw bytes. For an length-indexed version,
||| see module `ByteVect` and `Data.ByteVect`.
public export
record ByteString where
  constructor BS
  size : Nat
  repr : ByteVect size

%inline
conv : {n : _} -> Ur (IBuffer n) -@ Ur ByteString
conv (MkBang v) = MkBang $ BS n (BV v 0 reflexive)

||| Safely wrap a mutable buffer in a `ByteString`.
export
freezeByteString : {n : _} -> MBuffer n -@ Ur ByteString
freezeByteString mb = conv $ freeze mb

||| Safely wrap a mutable buffer in a `ByteString`.
export
freezeByteStringLTE : (m : Nat) -> (0 _ : LTE m n) => MBuffer n -@ Ur ByteString
freezeByteStringLTE m mb = conv $ freezeLTE m mb

||| Reads the value of a `ByteVect` at the given position
export %inline
at : ByteVect n -> Fin n -> Bits8
at (BV buf o lte) x =
  atNat buf (o + finToNat x) @{transitive (ltPlusRight $ finToNatLT x) lte}

||| Safely access a value in an array at position `n - m`.
export %inline
ix : ByteVect n -> (0 m : Nat) -> {auto x: Ix (S m) n} -> Bits8
ix bv _ = at bv (ixToFin x)

||| Safely access a value in an array at the given position.
export %inline
atNat : ByteVect n -> (m : Nat) -> {auto 0 lt : LT m n} -> Bits8
atNat bv x = at bv (natToFinLT x)

export
fromEnd : {n : _} -> ByteVect n -> (m : Nat) -> {auto 0 lt : LT m n} -> Bits8
fromEnd bs m = atNat bs (n `minus` S m) @{minusLT _ _ lt}

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

||| The empty `ByteVect`.
export
empty : ByteVect 0
empty = BV empty 0 %search

||| Converts a list of values to a `ByteVect` using
||| the given conversion function. O(n).
export
pack : (as : List Bits8) -> ByteVect (length as)
pack as = BV (bufferL as) 0 reflexive

||| Converts a `String` to a `ByteVect`. Note: This will
||| correctly decode the corresponding UTF-8 string.
export
fromString : (s : String) -> ByteVect (cast $ stringByteLength s)
fromString s = BV (fromString s) 0 reflexive

||| Converts a `ByteVect` to a UTF-8 encoded string
export
toString : {n : _} -> ByteVect n -> String
toString (BV buf o _) = toString buf o n

||| Creates a `ByteVect` holding a single `Bits8` value.
export %inline
singleton : Bits8 -> ByteVect 1
singleton v = pack [v]

||| Convert a `ByteVect` to a list of values using
||| the given conversion function.
export
toList : {n : _} -> (Bits8 -> a) -> ByteVect n -> List a
toList f bs     = go Nil n

  where
    go : List a -> (x : Nat) -> (0 prf : LTE x n) => List a
    go xs 0     = xs
    go xs (S j) = go (f (atNat bs j) :: xs) j

||| Converts a `ByteVect` to a list of `Bits8` values. O(n).
export %inline
unpack : {n : _} -> ByteVect n -> List Bits8
unpack = toList id

||| Converts a `ByteVect` to a String. All characters
||| will be in the range [0,255], so this does not perform
||| any character decoding.
export %inline
{n : Nat} -> Show (ByteVect n) where
  showPrec p bs = showCon p "pack" (showArg $ toList id bs)

--------------------------------------------------------------------------------
--          Comparing ByteStrings
--------------------------------------------------------------------------------

||| Lexicographic comparison of `ByteVect`s of distinct length
export
hcomp : {m,n : Nat} -> ByteVect m -> ByteVect n -> Ordering
hcomp b1 b2 = go m n

  where
    go : (k,l : Nat) -> {auto a1 : Ix k m} -> {auto a2 : Ix l n} -> Ordering
    go 0     0     = EQ
    go 0     (S _) = LT
    go (S _) 0     = GT
    go (S k) (S j) = case compare (ix b1 k) (ix b2 j) of
      EQ => go k j
      r  => r

||| Heterogeneous equality for `ByteVect`s
export
heq : {m,n : Nat} -> ByteVect m -> ByteVect n -> Bool
heq bs1 bs2 = hcomp bs1 bs2 == EQ

--------------------------------------------------------------------------------
--          Core Functionality
--------------------------------------------------------------------------------

export
generate : (n : Nat) -> (Fin n -> Bits8) -> ByteVect n
generate n f = BV (generate n f) 0 refl

export
replicate : (n : Nat) -> Bits8 -> ByteVect n
replicate n = generate n . const

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------

||| Concatenate two `ByteVect`s. O(n + m).
export
append : {m,n : _} -> ByteVect m -> ByteVect n -> ByteVect (m + n)
append (BV src1 o1 lte1) (BV src2 o2 lte2) =
  let buf := unrestricted $ Buffer.Core.alloc (m+n) $ \b1 =>
              let b2 := copy src1 o1 0 m @{lte1} @{lteAddRight _} b1
                  b3 := copy src2 o2 m n @{lte2} @{reflexive} b2
               in freeze b3
   in BV buf 0 reflexive

||| Prepend a single `Bits8` to a `ByteVect`. O(n).
export %inline
cons : {n : _} -> Bits8 -> ByteVect n -> ByteVect (S n)
cons = append . singleton

||| Append a single `Bits8` to a `ByteVect`. O(n).
export %inline
snoc : {n : _} -> Bits8 -> ByteVect n -> ByteVect (n + 1)
snoc w bs = bs `append` singleton w

--------------------------------------------------------------------------------
--          Inspecting ByteStrings
--------------------------------------------------------------------------------

||| Read the first element of a `ByteVect`. O(1).
export
head : ByteVect (S n) -> Bits8
head bv = atNat bv 0

||| Drop the first `Bits8` from a `ByteVect`. O(1).
export
tail : ByteVect (S n) -> ByteVect n
tail (BV buf o p) = BV buf (S o) (ltePlusSuccRight p)

||| Split the first `Bits8` from a `ByteVect`. O(1).
export
uncons : ByteVect (S n) -> (Bits8, ByteVect n)
uncons bs = (head bs, tail bs)

||| Read the last `Bits8` from a `ByteVect`. O(1).
export
last : {n : _} -> ByteVect (S n) -> Bits8
last bs = atNat bs n

||| Drop the last `Bits8` from a `ByteVect`. O(1).
export
init : ByteVect (S n) -> ByteVect n
init (BV buf o p) = BV buf o (lteSuccLeft $ ltePlusSuccRight p)

||| Split a `ByteVect` at the last byte. O(1).
export
unsnoc : {n : _} -> ByteVect (S n) -> (Bits8, ByteVect n)
unsnoc bs = (last bs, init bs)

--------------------------------------------------------------------------------
--          Mapping ByteStrings
--------------------------------------------------------------------------------

||| Converts every `Bits8` in a `ByteVect` by applying the given
||| function. O(n).
export
map : {n : _} -> (Bits8 -> Bits8) -> ByteVect n -> ByteVect n
map f bs = generate n (\x => f $ at bs x)

||| Interpreting the values stored in a `ByteVect` as 8 bit characters,
||| convert every lower-case character to its upper-case form. O(n)
export %inline
toUpper : {n : _} -> ByteVect n -> ByteVect n
toUpper = map toUpper

||| Interpreting the values stored in a `ByteVect` as 8 bit characters,
||| convert every upper-case character to its lower-case form. O(n)
export %inline
toLower : {n : _} -> ByteVect n -> ByteVect n
toLower = map toLower

||| Inverse the order of bytes in a `ByteVect`. O(n)
export
reverse : {n : _} -> ByteVect n -> ByteVect n
reverse bs = generate n (\x => fromEnd bs (finToNat x) @{finToNatLT _})

||| True, if the predicate holds for all bytes
||| in the given `ByteVect`. O(n)
export
all : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> Bool
all p bv = go n

  where
    go : (c : Nat) -> (x : Ix c n) => Bool
    go 0     = True
    go (S k) = if p (ix bv k) then go k else False

||| True, if the predicate holds for at least one byte
||| in the given `ByteVect`. O(n)
export
any : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> Bool
any p bv = go n

  where
    go : (c : Nat) -> (x : Ix c n) => Bool
    go 0     = False
    go (S k) = if p (ix bv k) then True else go k

||| True, if the given `Bits8` appears in the `ByteVect`. O(n)
export %inline
elem : {n : _} -> Bits8 -> ByteVect n -> Bool
elem b = any (b ==)

||| Fold a `ByteVect` from the left. O(n)
export
foldl : {n : _} -> (a -> Bits8 -> a) -> a -> ByteVect n -> a
foldl f ini bv = go n ini

  where
    go : (c : Nat) -> (v : a) -> (x : Ix c n) => a
    go 0     v = v
    go (S k) v = go k (f v $ ix bv k)

||| Fold a `ByteVect` from the right. O(n)
export
foldr : {n : _} -> (Bits8 -> a -> a) -> a -> ByteVect n -> a
foldr f ini bs = go n ini

  where
    go : (k : Nat) -> (v : a) -> (0 lt : LTE k n) => a
    go 0     v = v
    go (S k) v = go k (f (atNat bs k) v)

||| The `findIndex` function takes a predicate and a `ByteVect` and
||| returns the index of the first element in the ByteVect
||| satisfying the predicate. O(n)
export
findIndex : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> Maybe (Fin n)
findIndex p bv = go n

  where
    go : (c : Nat) -> {auto x : Ix c n} -> Maybe (Fin n)
    go 0     = Nothing
    go (S k) = if p (ix bv k) then Just (ixToFin x) else go k

||| Return the index of the first occurence of the given
||| byte in the `ByteVect`, or `Nothing`, if the byte
||| does not appear in the ByteVect. O(n)
export
elemIndex : {n : _} -> Bits8 -> ByteVect n -> Maybe (Fin n)
elemIndex c = findIndex (c ==)

||| Returns the first value byte in a `ByteVect` fulfilling
||| the given predicate. O(n)
export
find : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> Maybe Bits8
find p bs = at bs <$> findIndex p bs

export
isPrefixOf : {m,n : _} -> ByteVect m -> ByteVect n -> Bool
isPrefixOf bv1 bv2 = go m n

  where
    go : (c1,c2 : Nat) -> {auto _ : Ix c1 m} -> {auto _ : Ix c2 n} -> Bool
    go 0     _     = True
    go _     0     = False
    go (S x) (S y) = if ix bv1 x == ix bv2 y then go x y else False

export
isSuffixOf : {m,n : _} -> ByteVect m -> ByteVect n -> Bool
isSuffixOf bv1 bv2 = go m n

  where
    go : (o1,o2 : Nat) -> (0 _ : LTE o1 m) => (0 _ : LTE o2 n) => Bool
    go 0     _     = True
    go _     0     = False
    go (S x) (S y) = if atNat bv1 x == atNat bv2 y then go x y else False

--------------------------------------------------------------------------------
--          Substrings
--------------------------------------------------------------------------------

findIndexOrLength : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> SubLength n
findIndexOrLength p bv = go n

  where
    go : (c : Nat) -> {auto x : Ix c n} -> SubLength n
    go 0     = fromIx x
    go (S k) = if p (ix bv k) then fromIx x else go k

findIndexOrLengthNL : {n : _} -> ByteVect n -> SubLength n
findIndexOrLengthNL bv = go n

  where
    go : (c : Nat) -> {auto x : Ix c n} -> SubLength n
    go 0     = fromIx x
    go (S k) = case ix bv k of 10 => fromIx x; _ => go k

findFromEndUntil : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> SubLength n
findFromEndUntil p bv = go n

  where
    go : (k : Nat) -> (0 lt : LTE k n) => SubLength n
    go 0     = Element 0 LTEZero
    go (S k) = if p (atNat bv k) then (Element (S k) lt) else go k

0 substrPrf : LTE (s + l) n -> LTE (o + n) n2 -> LTE ((o + s) + l) n2
substrPrf p q =
  let pp := rewrite sym (plusAssociative o s l) in ltePlusRight o p
   in transitive pp q

||| Like `substr` for `String`, this extracts a substring
||| of the given `ByteVect` at the given start position
||| and of the given length. O(1).
export %inline
substring :
     (start,length : Nat)
  -> ByteVect n
  -> {auto 0 inBounds : LTE (start + length) n}
  -> ByteVect length
-- inBounds : start + len       <= n
-- p        : o + n             <= bufLen
-- required : (o + start) + len <= bufLen
substring start len (BV buf o p) =
  BV buf (o + start) (substrPrf inBounds p)

export
generateMaybe : (n : Nat) -> (Fin n -> Maybe Bits8) -> ByteString
generateMaybe n f = unrestricted $ alloc n (go n n)

  where
    go : (k,m : Nat) -> (x : Ix k n) => (y : Ix m n) => MBuffer n -@ Ur ByteString
    go (S k) (S m) m1 =
      case f (ixToFin x) of
        Nothing => go k (S m) m1
        Just v  => let m2 := setIx m v m1 in go k m m2
    go _ _ m1 = freezeByteStringLTE (ixToNat y) @{ixLTE y} m1

export
mapMaybe : {n : _} -> (Bits8 -> Maybe Bits8) -> ByteVect n -> ByteString
mapMaybe f bv = generateMaybe n (f . at bv)

export
filter : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> ByteString
filter p = mapMaybe (\b => if p b then Just b else Nothing)

||| Return a `ByteVect` with the first `n` values of
||| the input string. O(1)
export
take : (0 k : Nat) -> (0 lt : LTE k n) => ByteVect n -> ByteVect k
take k (BV buf o p) =
  -- p        : o + n <= bufLen
  -- lt       : k     <= n
  -- required : o + k <= bufLen
  BV buf o (transitive (ltePlusRight o lt) p)

||| Return a `ByteVect` with the last `n` values of
||| the input string. O(1)
export
takeEnd :
     {n : _}
  -> (k : Nat)
  -> {auto 0 lt : LTE k n}
  -> ByteVect n
  -> ByteVect k
takeEnd k (BV buf o p) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : ((o + n) - k) + k <= bufLen
  let 0 q := plusMinus' k (o + n) (lteAddLeft o lt)
   in BV buf ((o + n) `minus` k) (rewrite q in p)

||| Remove the first `n` values from a `ByteVect`. O(1)
export
drop : (k : Nat) -> (0 lt : LTE k n) => ByteVect n -> ByteVect (n `minus` k)
drop k (BV buf o p) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : (o + k) + (n - k) <= bufLen
  let 0 q := cong (o +) (plusMinus k n lt)
      0 r := plusAssociative o k (n `minus` k)
   in BV buf (o + k) (rewrite (trans (sym r) q) in p)

||| Remove the last `n` values from a `ByteVect`. O(1)
export
dropEnd :
     (0 k : Nat)
  -> {auto 0 lt : LTE k n}
  -> ByteVect n
  -> ByteVect (n `minus` k)
dropEnd k (BV buf o p) =
  -- p        : o + n       <= bufLen
  -- lt       : k           <= n
  -- required : o + (n - k) <= bufLen
  BV buf o (transitive (ltePlusRight o $ minusLTE n k) p)

export
splitAt :
     {n : _}
  -> (k : Nat)
  -> {auto 0 lte : LTE k n}
  -> ByteVect n
  -> (ByteVect k, ByteVect (n `minus` k))
splitAt k bs = (take k bs, drop k bs)

||| Extracts the longest prefix of elements satisfying the
||| predicate.
export
takeWhile : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> ByteString
takeWhile p bs =
  let Element k _ = findIndexOrLength (not . p) bs
   in BS k $ take k bs

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate.
export
takeWhileEnd : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> ByteString
takeWhileEnd f bs =
  let Element k _ = findFromEndUntil (not . f) bs
   in BS _ $ drop k bs

||| Drops the longest (possibly empty) prefix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhile : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> ByteString
dropWhile f bs =
  let Element k _ = findIndexOrLength (not . f) bs
   in BS _ $ drop k bs

||| Drops the longest (possibly empty) suffix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhileEnd : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> ByteString
dropWhileEnd f bs =
  let Element k _ = findFromEndUntil (not . f) bs
   in BS k $ take k bs

||| Remove leading whitespace from a `ByteString`
export
trimLeft : {n : _} -> ByteVect n -> ByteString
trimLeft = dropWhile isSpace

||| Remove trailing whitespace from a `ByteString`
export
trimRight : {n : _} -> ByteVect n -> ByteString
trimRight = dropWhileEnd isSpace

||| Remove all leading and trailing whitespace from a `ByteString`
export
trim : {n : _} -> ByteVect n -> ByteString
trim bs = let BS k bs' := trimLeft bs in trimRight bs'

public export
record BreakRes (n : Nat) where
  constructor MkBreakRes
  lenFst : Nat
  lenSnd : Nat
  fst    : ByteVect lenFst
  snd    : ByteVect lenSnd
  0 prf  : LTE (lenFst + lenSnd) n

||| Returns the longest (possibly empty) prefix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
break : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> BreakRes n
break p bs =
  let Element k p := findIndexOrLength p bs
      bs1 := take k bs
      bs2 := drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinusLTE k n p)

||| Returns the longest (possibly empty) prefix before the first newline character
export
breakNL : {n : _} -> ByteVect n -> BreakRes n
breakNL bs =
  let Element k p := findIndexOrLengthNL bs
      bs1 := take k bs
      bs2 := drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinusLTE k n p)

||| Returns the longest (possibly empty) suffix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
breakEnd : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> BreakRes n
breakEnd  p bs =
  let Element k p := findFromEndUntil p bs
      bs1 := take k bs
      bs2 := drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinusLTE k n p)

||| Returns the longest (possibly empty) prefix of elements
||| satisfying the predicate and the remainder of the string.
export %inline
span : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> BreakRes n
span p = break (not . p)

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate and the remainder of the string.
export
spanEnd : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> BreakRes n
spanEnd p bs =
  let Element k p := findFromEndUntil (not . p) bs
      bs1 := take k bs
      bs2 := drop k bs
   in MkBreakRes k (n `minus` k) bs1 bs2 (plusMinusLTE k n p)

||| Splits a 'ByteVect' into components delimited by
||| separators, where the predicate returns True for a separator element.
||| The resulting components do not contain the separators. Two adjacent
||| separators result in an empty component in the output. eg.
export
splitWith : {n : _} -> (Bits8 -> Bool) -> ByteVect n -> List ByteString
splitWith p bs = go Lin n bs (sizeAccessible n)

  where
    go :
         SnocList ByteString
      -> (m : Nat)
      -> ByteVect m
      -> (0 acc : SizeAccessible m)
      -> List ByteString
    go sb m bs' (Access rec) = case break p bs' of
      MkBreakRes l1 0      b1 _  p => sb <>> [BS l1 b1]
      MkBreakRes l1 (S l2) b1 b2 p =>
        go (sb :< BS l1 b1) l2 (tail b2) (rec l2 $ ltPlusSuccRight' _ p)

||| Break a `ByteVect` into pieces separated by the byte
||| argument, consuming the delimiter.
|||
||| As for all splitting functions in this library, this function does
||| not copy the substrings, it just constructs new `ByteString`s that
||| are slices of the original.
export %inline
split : {n : _} -> Bits8 -> ByteVect n -> List ByteString
split b = splitWith (b ==)

export
lines : {n : _} -> ByteVect n -> List ByteString
lines bs = go Lin n bs (sizeAccessible n)

  where
    go :
         SnocList ByteString
      -> (m : Nat)
      -> ByteVect m
      -> (0 acc : SizeAccessible m)
      -> List ByteString
    go sb m bs' (Access rec) = case breakNL bs' of
      MkBreakRes l1 0      b1 _  p => sb <>> [BS l1 b1]
      MkBreakRes l1 (S l2) b1 b2 p =>
        go (sb :< BS l1 b1) l2 (tail b2) (rec l2 $ ltPlusSuccRight' _ p)

export
isInfixOf : {m,n : _} -> ByteVect m -> ByteVect n -> Bool
isInfixOf bv1 bv2 = m == 0 || go n

  where
    go : (c : Nat) -> (x : Ix c n) => Bool
    go 0     = False
    go (S k) = isPrefixOf bv1 (drop (ixToNat x) @{ixLTE x} bv2) || go k

--------------------------------------------------------------------------------
--          Parsing Numbers
--------------------------------------------------------------------------------

||| Parse a natural number in the given base.
export
parseAnyNat :
     {n : _}
  -> (base : Nat)
  -> {auto 0 p1 : LTE 2 base}
  -> {auto 0 p2 : LTE base 16}
  -> ByteVect n
  -> Maybe Nat
parseAnyNat {n = Z} _    bv = Nothing
parseAnyNat         base bv = go n 0

  where
    go : (c,res : Nat) -> (x : Ix c n) => Maybe Nat
    go 0     res = Just res
    go (S k) res =
      let Just n := fromHexDigit $ ix bv k | Nothing => Nothing
       in if n < base then go k (res * base + n) else Nothing

||| Parses a natural number in decimal notation.
export %inline
parseDecimalNat : {n : _} -> ByteVect n -> Maybe Nat
parseDecimalNat {n = Z} bv = Nothing
parseDecimalNat         bv = go n 0

  where
    go : (c,res : Nat) -> (x : Ix c n) => Maybe Nat
    go 0     res = Just res
    go (S k) res =
      let Just n := fromDigit $ ix bv k | Nothing => Nothing
       in go k (res * 10 + n)

export %inline
parseHexadecimalNat : {n : _} -> ByteVect n -> Maybe Nat
parseHexadecimalNat = parseAnyNat 10

export %inline
parseOctalNat : {n : _} -> ByteVect n -> Maybe Nat
parseOctalNat = parseAnyNat 8

export %inline
parseBinaryNat : {n : _} -> ByteVect n -> Maybe Nat
parseBinaryNat = parseAnyNat 2

export
parseInteger : {n : _} -> ByteVect n -> Maybe Integer
parseInteger {n = Z}   _  = Nothing
parseInteger {n = S _} bv = case head bv of
  43 => cast          <$> parseDecimalNat (tail bv) -- '+'
  45 => negate . cast <$> parseDecimalNat (tail bv) -- '-'
  _  => cast <$> parseDecimalNat bv


-- parsing Double

isE : Bits8 -> Bool
isE 69  = True
isE 101 = True
isE _   = False

fract : {n : _} -> ByteVect n -> Maybe Double
fract bv =
  let Just k := parseDecimalNat bv | Nothing => Nothing
   in Just (cast k / (pow 10 $ cast n))

exp : {n : _} -> ByteVect n -> Maybe Double
exp bv =
  let Just exp := parseInteger bv | Nothing => Nothing
   in Just $ pow 10.0 (cast exp)

parseDotted : {n : _} -> ByteVect n -> Maybe Double
parseDotted bv = go 0 0 n
  where
    go : (v,exp,c : Nat) -> (x : Ix c n) => Maybe Double
    go v exp 0     = case exp of
      0 => Just $ cast v
      _ => Just $ cast v / cast exp
    go v exp (S k) =
      case ix bv k of
        48 => go (v * 10 + 0) (exp * 10) k
        49 => go (v * 10 + 1) (exp * 10) k
        50 => go (v * 10 + 2) (exp * 10) k
        51 => go (v * 10 + 3) (exp * 10) k
        52 => go (v * 10 + 4) (exp * 10) k
        53 => go (v * 10 + 5) (exp * 10) k
        54 => go (v * 10 + 6) (exp * 10) k
        55 => go (v * 10 + 7) (exp * 10) k
        56 => go (v * 10 + 8) (exp * 10) k
        57 => go (v * 10 + 9) (exp * 10) k
        46 => case exp of
          0 => go v 1 k
          _ => Nothing
        _  => Nothing

parsePosDbl : {n : _} -> ByteVect n -> Maybe Double
parsePosDbl bv = case parseDotted bv of
  Just v  => Just v
  Nothing => case break isE bv of
    MkBreakRes lf (S _) dotStr expStr _ =>
      let Just fract := parseDotted dotStr | Nothing => Nothing
          Just e     := exp (tail expStr)  | Nothing => Nothing
       in Just $ fract * e
    MkBreakRes _ 0 _ _ _ => Nothing

export
parseDouble : {n : _} -> ByteVect n -> Maybe Double
parseDouble {n = Z}   _  = Nothing
parseDouble {n = S _} bv = case head bv of
  43 => parsePosDbl (tail bv)             -- '+'
  45 => negate  <$> parsePosDbl (tail bv) -- '-'
  _  => parsePosDbl bv
