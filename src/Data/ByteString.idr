||| Immutable strings of raw bytes.
module Data.ByteString

import Data.Buffer
import Data.Buffer.Mutable
import Data.List
import Data.Maybe0
import Data.Nat.BSExtra

import System.File

import public Data.ByteVect as BV

%default total

--------------------------------------------------------------------------------
--          ByteString
--------------------------------------------------------------------------------

export
null : ByteString -> Bool
null (BS Z _) = True
null _        = False

export %inline
length : ByteString -> Nat
length (BS n _) = n

||| Tries to read the value of a `ByteString` at the given position
export
index : (x : Nat) -> ByteString -> Maybe Bits8
index x (BS n repr) = at repr <$> tryNatToFin x

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

||| The empty `ByteString`.
export %inline
empty : ByteString
empty = BS 0 empty

||| Converts a list of `Bits8` values to a `ByteString`.
export %inline
pack : (as : List Bits8) -> ByteString
pack as = BS _ $ pack as

||| Creates a `ByteString` holding a single `Bits8` value.
export %inline
singleton : Bits8 -> ByteString
singleton v = pack [v]

||| Convert a `ByteString` to a list of values using
||| the given conversion function.
export %inline
toList : (Bits8 -> a) -> ByteString -> List a
toList f (BS _ bs) = toList f bs

||| Converts a `ByteString` to a list of `Bits8` values. O(n).
export %inline
unpack : ByteString -> List Bits8
unpack = toList id

||| Converts a `ByteString` to a UTF-8 encoded string
export
toString : ByteString -> String
toString (BS _ bs) = toString bs

||| Converts a `ByteString` to a String. All characters
||| will be in the range [0,255], so this does not perform
||| any character decoding.
export %inline
Show ByteString where
  show (BS _ bs) = show bs

export %inline
Eq ByteString where
  BS _ bs1 == BS _ bs2 = heq bs1 bs2

export %inline
Ord ByteString where
  compare (BS _ bs1) (BS _ bs2) = hcomp bs1 bs2

export
FromString ByteString where
  fromString s = BS _ $ fromString s

--------------------------------------------------------------------------------
--          Core Functionality
--------------------------------------------------------------------------------

export %inline
generate : (n : Nat) -> (Fin n -> Bits8) -> ByteString
generate n f = BS n (generate n f)

export
replicate : (n : Nat) -> Bits8 -> ByteString
replicate n = generate n . const

export
unsafeByteString : (n : Nat) -> Buffer -> ByteString
unsafeByteString n buf = BS n (BV (unsafeMakeBuffer buf) 0 reflexive)

||| Copy the given `ByteString` and write its content to a freshly
||| allocated buffer.
export
toBuffer : ByteString -> IO Buffer
toBuffer (BS n (BV b o lt)) =
  create n $ \r,t => let _ # t := copy b o 0 n r t in toIO r t

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------

public export
TotLength : List ByteString -> Nat
TotLength []             = 0
TotLength (BS n _ :: xs) = n + TotLength xs

export
copyMany :
     (ps  : List ByteString)
  -> (pos : Nat)
  -> {auto 0 prf : pos + TotLength ps === n}
  -> (r   : MBuffer n)
  -> {auto 0 p : Res r rs}
  -> F1' rs
copyMany []                      pos r t = () # t
copyMany (BS k (BV b o lt):: xs) pos r t =
  let _ # t := copy b o pos k @{lt} @{rewrite sym prf in concatLemma1} r t
   in copyMany xs (pos + k) @{concatLemma2 prf} r t

||| Concatenate a list of `ByteString`. This allocates
||| a buffer of sufficient size in advance, so it is much
||| faster than `concat`, or `concatMap` for large `ByteString`s.
export
fastConcat :  (bs : List ByteString) -> ByteString
fastConcat bs =
  create (TotLength bs) $ \r,t =>
    let _ # t := copyMany bs 0 r t in freezeByteString r t

||| Concatenates a list of bytestrings, separating them with the
||| given separator `sep`.
export %inline
concatSep : (sep : ByteString) -> (bs : List ByteString) -> ByteString
concatSep sep = fastConcat . intersperse sep

||| Concatenates a list of bytestrings, using the given byte to
||| separate them.
export %inline
concatSep1 : (sep : Bits8) -> (bs : List ByteString) -> ByteString
concatSep1 = concatSep . singleton

||| Concatenates the given list of bytestring by interspersing them
||| with Unix linebreaks (byte `0x0A`).
export %inline
unixUnlines : List ByteString -> ByteString
unixUnlines = concatSep1 0x0A

||| Concatenate two `ByteString`s. O(n + m).
export %inline
append : ByteString -> ByteString -> ByteString
append (BS 0 _)   b2         = b2
append b1         (BS 0 _)   = b1
append (BS m bv1) (BS n bv2) = BS _ $ append bv1 bv2

||| Prepend a single `Bits8` to a `ByteString`. O(n).
export %inline
cons : Bits8 -> ByteString -> ByteString
cons = append . singleton

||| Append a single `Bits8` to a `ByteString`. O(n).
export %inline
snoc : Bits8 -> ByteString -> ByteString
snoc w bs = bs `append` singleton w

export %inline
Semigroup ByteString where
  (<+>) = append

export %inline
Monoid ByteString where
  neutral = empty

--------------------------------------------------------------------------------
--          Inspecting ByteStrings
--------------------------------------------------------------------------------

||| Read the first element of a `ByteString`. O(1).
export %inline
head : ByteString -> Maybe Bits8
head = index 0

||| Drop the first `Bits8` from a `ByteString`. O(1).
export
tail : ByteString -> Maybe ByteString
tail (BS (S k) bs) = Just (BS k $ tail bs)
tail _             = Nothing

||| Split the first `Bits8` from a `ByteString`. O(1).
export
uncons : ByteString -> Maybe (Bits8, ByteString)
uncons (BS (S k) bs) = let (b,bs2) := uncons bs in Just (b, BS k bs2)
uncons _             = Nothing

||| Read the last `Bits8` from a `ByteString`. O(1).
export
last : ByteString -> Maybe Bits8
last (BS (S k) bs) = Just $ last bs
last _             = Nothing

||| Drop the last `Bits8` from a `ByteString`. O(1).
export
init : ByteString -> Maybe ByteString
init (BS (S k) bs) = Just (BS k $ init bs)
init _             = Nothing

||| Split the last `Bits8` from a `ByteString`. O(1).
export
unsnoc : ByteString -> Maybe (Bits8, ByteString)
unsnoc (BS (S k) bs) = let (b,bs2) := unsnoc bs in Just (b, BS k bs2)
unsnoc _             = Nothing

--------------------------------------------------------------------------------
--          Mapping ByteStrings
--------------------------------------------------------------------------------

||| Converts every `Bits8` in a `ByteString` by applying the given
||| function. O(n).
export %inline
map : (Bits8 -> Bits8) -> ByteString -> ByteString
map f (BS n bs) = BS n $ map f bs

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every lower-case character to its upper-case form.
export %inline
toUpper : ByteString -> ByteString
toUpper = map toUpper

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every upper-case character to its lower-case form.
export %inline
toLower : ByteString -> ByteString
toLower = map toLower

export %inline
reverse : ByteString -> ByteString
reverse (BS n bs) = BS n $ reverse bs

||| True, if the predicate holds for all bytes in the given `ByteString`
export %inline
all : (Bits8 -> Bool) -> ByteString -> Bool
all p (BS n bs) = all p bs

||| True, if the predicate holds for at least one byte
||| in the given `ByteString`
export %inline
any : (Bits8 -> Bool) -> ByteString -> Bool
any p (BS n bs) = any p bs

||| True, if the given `Bits8` appears in the `ByteString`.
export %inline
elem : Bits8 -> ByteString -> Bool
elem b = any (b ==)

export %inline
foldl : (a -> Bits8 -> a) -> a -> ByteString -> a
foldl f ini (BS n bs) = foldl f ini bs

export %inline
foldr : (Bits8 -> a -> a) -> a -> ByteString -> a
foldr f ini (BS n bs) = foldr f ini bs

||| The `findIndex` function takes a predicate and a `ByteString` and
||| returns the index of the first element in the ByteString
||| satisfying the predicate.
export %inline
findIndex : (Bits8 -> Bool) -> ByteString -> Maybe Nat
findIndex p (BS n bs) = finToNat <$> findIndex p bs

||| Return the index of the first occurence of the given
||| byte in the `ByteString`, or `Nothing`, if the byte
||| does not appear in the ByteString.
export %inline
elemIndex : Bits8 -> ByteString -> Maybe Nat
elemIndex c = findIndex (c ==)

export %inline
find : (Bits8 -> Bool) -> ByteString -> Maybe Bits8
find p (BS n bs) = find p bs

export %inline
isInfixOf : ByteString -> ByteString -> Bool
isInfixOf (BS _ bv1) (BS _ bv2) = isInfixOf bv1 bv2

export %inline
isPrefixOf : ByteString -> ByteString -> Bool
isPrefixOf (BS _ bv1) (BS _ bv2) = isPrefixOf bv1 bv2

export %inline
isSuffixOf : ByteString -> ByteString -> Bool
isSuffixOf (BS _ bv1) (BS _ bv2) = isSuffixOf bv1 bv2

--------------------------------------------------------------------------------
--          Substrings
--------------------------------------------------------------------------------

||| Like `substr` for `String`, this extracts a substring
||| of the given `ByteString` at the given start position
||| and of the given length.
export
substring : (start,length : Nat) -> ByteString -> ByteString
substring s l (BS n bs) =
  case tryLTE (s+l) of
    Just0 p  => BS l (substring s l bs)
    Nothing0 => case tryLTE s of
      Just0 p  => BS (n `minus` s) (drop s bs)
      Nothing0 => empty

export
mapMaybe : (Bits8 -> Maybe Bits8) -> ByteString -> ByteString
mapMaybe f (BS n bs) = mapMaybe f bs

export
filter : (Bits8 -> Bool) -> ByteString -> ByteString
filter p (BS n bs) = filter p bs

||| Return a `ByteString` with the first `n` values of
||| the input string. Returns the whole string if
||| `k` is larger than the bytestring. O(1)
export
take : Nat -> ByteString -> ByteString
take k (BS n bs) =
  case tryLTE k of
    Just0 p  => BS k (take k bs)
    Nothing0 => BS n bs

||| Return a `ByteString` with the last `n` values of
||| the input string. O(1)
export
takeEnd : Nat -> ByteString -> ByteString
takeEnd k (BS n bs) =
  case tryLTE k of
    Just0 p  => BS k (takeEnd k bs)
    Nothing0 => BS n bs

||| Remove the first `n` values from a `ByteString`. O(1)
export
drop : Nat -> ByteString -> ByteString
drop k (BS n bs) =
  case tryLTE k of
    Just0 p  => BS (n `minus` k) (drop k bs)
    Nothing0 => empty

||| Remove the last `n` values from a `ByteString`. O(1)
export
dropEnd : Nat -> ByteString -> ByteString
dropEnd k (BS n bs) =
  case tryLTE k of
    Just0 p  => BS (n `minus` k) (dropEnd k bs)
    Nothing0 => empty

export
splitAt : (k : Nat) -> ByteString -> Maybe (ByteString,ByteString)
splitAt k (BS n bs) =
  case tryLTE k of
    Just0 p  =>
      let (bs1,bs2) := splitAt k bs
       in Just (BS k bs1, BS (n `minus` k) bs2)
    Nothing0 => Nothing

||| Extracts the longest prefix of elements satisfying the
||| predicate.
export %inline
takeWhile : (Bits8 -> Bool) -> ByteString -> ByteString
takeWhile p (BS n bs) = takeWhile p bs

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate.
export %inline
takeWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
takeWhileEnd p (BS n bs) = takeWhileEnd p bs

||| Drops the longest (possibly empty) prefix of elements
||| satisfying the predicate and returns the remainder.
export %inline
dropWhile : (Bits8 -> Bool) -> ByteString -> ByteString
dropWhile p (BS n bs) = dropWhile p bs

||| Drops the longest (possibly empty) suffix of elements
||| satisfying the predicate and returns the remainder.
export %inline
dropWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
dropWhileEnd p (BS n bs) = dropWhileEnd p bs

||| Returns the longest (possibly empty) prefix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
break : (Bits8 -> Bool) -> ByteString -> (ByteString,ByteString)
break p (BS n bs) =
  let MkBreakRes n1 n2 bs1 bs2 _ := break p bs
   in (BS n1 bs1, BS n2 bs2)

||| Returns the longest (possibly empty) suffix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
breakEnd : (Bits8 -> Bool) -> ByteString -> (ByteString,ByteString)
breakEnd p (BS n bs) =
  let MkBreakRes n1 n2 bs1 bs2 _ := breakEnd p bs
   in (BS n1 bs1, BS n2 bs2)

||| Returns the longest (possibly empty) prefix of elements
||| satisfying the predicate and the remainder of the string.
export %inline
span : (Bits8 -> Bool) -> ByteString -> (ByteString,ByteString)
span p = break (not . p)

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate and the remainder of the string.
export
spanEnd : (Bits8 -> Bool) -> ByteString -> (ByteString,ByteString)
spanEnd p (BS n bs) =
  let MkBreakRes n1 n2 bs1 bs2 _ := spanEnd p bs
   in (BS n1 bs1, BS n2 bs2)

||| Remove leading whitespace from a `ByteString`
export %inline
trimLeft : ByteString -> ByteString
trimLeft (BS _ bv) = trimLeft bv

||| Remove trailing whitespace from a `ByteString`
export %inline
trimRight : ByteString -> ByteString
trimRight (BS _ bv) = trimRight bv

||| Remove all leading and trailing whitespace from a `ByteString`
export %inline
trim : ByteString -> ByteString
trim (BS _ bv) = trim bv

||| Splits a 'ByteString' into components delimited by
||| separators, where the predicate returns True for a separator element.
||| The resulting components do not contain the separators. Two adjacent
||| separators result in an empty component in the output. eg.
export
splitWith : (Bits8 -> Bool) -> ByteString -> List ByteString
splitWith p (BS n bs) = splitWith p bs

||| Break a `ByteString` into pieces separated by the byte
||| argument, consuming the delimiter.
|||
||| As for all splitting functions in this library, this function does
||| not copy the substrings, it just constructs new `ByteString`s that
||| are slices of the original.
export %inline
split : Bits8 -> ByteString -> List ByteString
split b = splitWith (b ==)

||| Returns the longest (possibly empty) prefix of a
||| bytestring that does not contain the given substring
||| plus the remainder of the byte vector.
export %inline
breakAtSubstring : (sep,val : ByteString) -> (ByteString,ByteString)
breakAtSubstring (BS _ s) (BS _ v) =
  let MkBreakRes _ _ x y _ := breakAtSubstring s v
   in (BS _ x, BS _ y)

||| Splits the second bytestring whenever the first called
||| `sep` occurs.
|||
||| The bytestrings in the result no longer contain `sep` as
||| a substring.
|||
||| Note: If `sep` is the empty bytestring, `[val]` is returned
|||       as the result.
export %inline
splitAtSubstring : (sep, val : ByteString) -> List ByteString
splitAtSubstring (BS _ s) (BS _ v) = splitAtSubstring s v

||| Breakes the given bytestring at Unix linebreaks (byte `0x0A`).
export %inline
unixLines : ByteString -> List ByteString
unixLines (BS _ bv) = lines bv

--------------------------------------------------------------------------------
--          Parsing Numbers
--------------------------------------------------------------------------------

||| Parse a natural number in the given base.
export %inline
parseAnyNat :
     (base : Nat)
  -> {auto 0 p1 : LTE 2 base}
  -> {auto 0 p2 : LTE base 16}
  -> ByteString
  -> Maybe Nat
parseAnyNat base (BS _ bv) = parseAnyNat base bv

||| Parses a natural number in decimal notation.
export %inline
parseDecimalNat : ByteString -> Maybe Nat
parseDecimalNat (BS _ bv) = parseDecimalNat bv

export %inline
parseHexadecimalNat : ByteString -> Maybe Nat
parseHexadecimalNat (BS _ bv) = parseHexadecimalNat bv

export %inline
parseOctalNat : ByteString -> Maybe Nat
parseOctalNat (BS _ bv) = parseOctalNat bv

export %inline
parseBinaryNat : ByteString -> Maybe Nat
parseBinaryNat (BS _ bv) = parseBinaryNat bv

export %inline
parseInteger : ByteString -> Maybe Integer
parseInteger (BS _ bv) = parseInteger bv

export %inline
parseDouble : ByteString -> Maybe Double
parseDouble (BS _ bv) = parseDouble bv

--------------------------------------------------------------------------------
--          Reading and Writing Files
--------------------------------------------------------------------------------

export
readBytesString :  HasIO io => Nat -> File -> io (Either FileError ByteString)
readBytesString max f = do
  Right (n ** ib) <- readIBuffer max f | Left x => pure (Left x)
  pure . Right $ BS n (BV ib 0 reflexive)

export %inline
writeByteVect :
     {n : _}
  -> {auto _ : HasIO io}
  -> File
  -> ByteVect n
  -> io (Either (FileError,Int) ())
writeByteVect h (BV buf o _) = writeIBuffer h o n buf

export %inline
writeByteString :
     {auto _ : HasIO io}
  -> File
  -> ByteString
  -> io (Either (FileError,Int) ())
writeByteString h (BS n bs) = writeByteVect h bs
