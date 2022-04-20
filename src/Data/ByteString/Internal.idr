module Data.ByteString.Internal

import Data.Buffer
import Data.List
import System.File
import System.File.Support

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "RefC:getBufferByte"
         "node:lambda:(buf,offset)=>buf.readUInt8(offset)"
prim__getBits8 : Buffer -> (offset : Bits32) -> Bits8

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuffer : Bits32 -> Buffer

%foreign "scheme:blodwen-buffer-size"
         "RefC:getBufferSize"
         "node:lambda:b => b.length"
prim__bufferSize : Buffer -> Bits32

%foreign "scheme:blodwen-buffer-setbyte"
         "RefC:setBufferByte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, offset)"
prim__setBits8 : Buffer -> (offset : Bits32) -> (val : Bits8) -> PrimIO Int

%foreign "scheme:blodwen-buffer-copydata"
         "RefC:copyBuffer"
         "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(b2,o2,o1,o1+length)"
prim__copyData : (src : Buffer) -> (srcOffset, len : Bits32) ->
                 (dst : Buffer) -> (dstOffset : Bits32) -> PrimIO Int

%foreign supportC "idris2_readBufferData"
         "node:lambda:(f,b,l,m) => require('fs').readSync(f.fd,b,l,m)"
prim__readBufferData :  FilePtr
                     -> Buffer
                     -> (offset : Bits32)
                     -> (maxbytes : Bits32) -> PrimIO Int

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
record ByteString where
  constructor BS
  buf    : Buffer
  offset : Bits32
  len    : Bits32

--------------------------------------------------------------------------------
--          Unsafe Operations
--------------------------------------------------------------------------------

||| Wraps a `Buffer` in a `ByteString` *without making a copy*.
||| Use this for efficient reading of data from a file or other resource
||| into a `ByteString`, but make sure to not reuse the
||| `Buffer` in question elsewhere.
export %inline
unsafeFromBuffer : Buffer -> ByteString
unsafeFromBuffer b = BS b 0 $ prim__bufferSize b

||| Reads the value of a `ByteString` at the given position
||| *without checking the bounds*.
export %inline
unsafeGetBits8 : Bits32 -> ByteString -> Bits8
unsafeGetBits8 n (BS buf o _) = prim__getBits8 buf (o + n)

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

||| The empty `ByteString`.
export
empty : ByteString
empty = BS (prim__newBuffer 0) 0 0

||| Converts a list of values to a `ByteString` using
||| the given conversion function. O(n).
export
fromList : (a -> Bits8) -> List a -> ByteString
fromList f vs = 
  let len = cast {to = Bits32} $ length vs
   in unsafePerformIO $ fromPrim $ go vs 0 (prim__newBuffer len)
  where go : List a -> Bits32 -> Buffer -> PrimIO ByteString
        go []        ix buf w = MkIORes (BS buf 0 ix) w
        go (b :: bs) ix buf w =
          case prim__setBits8 buf ix (f b) w of
            -- this is a hack: Without this (completely useless) pattern
            -- match, the call to `prim__setBits8` is erased and ignored
            MkIORes 0 w2 => go bs (ix+1) buf w2
            MkIORes _ w2 => go bs (ix+1) buf w2

||| Converts a list of `Bits8` values to a `ByteString`.
export %inline
pack : List Bits8 -> ByteString
pack = fromList id

||| Creates a `ByteString` holding a single `Bits8` value.
export %inline
singleton : Bits8 -> ByteString
singleton = pack . (::[])

||| Converts a `String` to a `ByteString`. O(n).
|||
||| Note: All characters are truncated to 8 bits in the
||| process, so this will mangle UTF-8 encoded strings.
export %inline
FromString ByteString where
  fromString = fromList cast . fastUnpack

||| Converts a `ByteString` to a list of values using
||| the given conversion function.
export
toList : (Bits8 -> a) -> ByteString -> List a
toList f bs = go Nil bs.len
  where go : List a -> Bits32 -> List a
        go as 0 = as
        go as n = 
          let ix = assert_smaller n (n-1)
           in go (f (unsafeGetBits8 ix bs) :: as) ix

||| Converts a `ByteString` to a list of `Bits8` values. O(n).
export %inline
unpack : ByteString -> List Bits8
unpack = toList id

||| Converts a `ByteString` to a String. All characters
||| will be in the range [0,255], so this does not perform
||| any character decoding.
export %inline
Show ByteString where
  show = show . fastPack . toList cast

--------------------------------------------------------------------------------
--          Comparing ByteStrings
--------------------------------------------------------------------------------

comp : ByteString -> ByteString -> Ordering
comp (BS _ _ 0) (BS _ _ 0)      = EQ  -- short cut for empty strings
comp bs1      bs2 = go 0 (min bs1.len bs2.len)
  where go : (pos, maxPos : Bits32) -> Ordering
        go pos maxPos =
          if pos == maxPos then compare bs1.len bs2.len
          else case compare (unsafeGetBits8 pos bs1) (unsafeGetBits8 pos bs2) of
                 EQ => go (assert_smaller pos $ pos + 1) maxPos         
                 o  => o

export %inline
Eq ByteString where
  a == b = case comp a b of
             EQ => True
             _  => False

export %inline
Ord ByteString where
  compare = comp

--------------------------------------------------------------------------------
--          Core Functionality
--------------------------------------------------------------------------------

||| Length (number of `Bits8`) of the `ByteString`. O(1).
export %inline
length : ByteString -> Bits32
length = len

||| `True` if the given `ByteString` has zero length. O(1).
export %inline
null : ByteString -> Bool
null = (== 0) . length

export
generate : Bits32 -> (Bits32 -> Bits8) -> ByteString
generate 0 _ = empty
generate l f = unsafePerformIO $ fromPrim $ go l (prim__newBuffer l)
  where go : Bits32 -> Buffer -> PrimIO ByteString
        go 0 buf w = MkIORes (BS buf 0 l) w
        go n buf w =
          let ix = n - 1
           in case prim__setBits8 buf ix (f ix) w of
                MkIORes 0 w2 => go (assert_smaller n ix) buf w2
                MkIORes _ w2 => go (assert_smaller n ix) buf w2

export
replicate : Bits32 -> Bits8 -> ByteString
replicate n = generate n . const

export
getBits8 : Bits32 -> ByteString -> Maybe Bits8
getBits8 n bs = if bs.len > n then Just (unsafeGetBits8 n bs) else Nothing

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------

||| Concatenate a list of `ByteString`. This allocates
||| a buffer of sufficient size in advance, so it is much
||| faster than `concat`, or `concatMap` for large `ByteString`s.
export
fastConcat : List ByteString -> ByteString
fastConcat bs = case filter ((> 0) . len) bs of
  Nil => empty
  [b] => b
  bs2 =>
    let tot = foldl (\a,b => a + b.len) 0 bs2
     in unsafePerformIO $ fromPrim $ go bs2 (prim__newBuffer tot) 0
      where go :  List ByteString
               -> Buffer
               -> (offset : Bits32)
               -> PrimIO ByteString
            go []        buf o w = MkIORes (BS buf 0 o) w
            go (BS src so sl :: bs) buf o w =
              case prim__copyData src so sl buf o w of
                -- this is a hack: Without this (completely useless) pattern
                -- match, the call to `prim__setBits8` is erased and ignored
                MkIORes 0 w2 => go bs buf (o + sl) w2
                MkIORes _ w2 => go bs buf (o + sl) w2

||| Concatenate two `ByteString`s. O(n + m).
export %inline
append : ByteString -> ByteString -> ByteString
append b1 b2 = fastConcat [b1,b2]

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

||| Try to read the first element of a `ByteString`. O(1).
export
head : ByteString -> Maybe Bits8
head (BS _ _ 0)   = Nothing
head (BS buf o l) = Just (prim__getBits8 buf o)

||| Try to drop the first `Bits8` from a `ByteString`. O(1).
export
tail : ByteString -> Maybe ByteString
tail (BS _ _ 0)   = Nothing
tail (BS buf o l) = Just (BS buf (o+1) (l-1))

||| Try to split the first `Bits8` from a `ByteString`. O(1).
export
uncons : ByteString -> Maybe (Bits8, ByteString)
uncons (BS _ _ 0)   = Nothing
uncons (BS buf o l) = Just (prim__getBits8 buf o, BS buf (o+1) (l-1))

||| Try to read the last `Bits8` from a `ByteString`. O(1).
export
last : ByteString -> Maybe Bits8
last (BS _ _ 0)   = Nothing
last (BS buf o l) = Just (prim__getBits8 buf (o + l-1))

||| Try to drop the last `Bits8` from a `ByteString`. O(1).
export
init : ByteString -> Maybe ByteString
init (BS _ _ 0)   = Nothing
init (BS buf o l) = Just (BS buf o (l-1))

||| Try to split the last `Bits8` from a `ByteString`. O(1).
export
unsnoc : ByteString -> Maybe (Bits8, ByteString)
unsnoc (BS _ _ 0)   = Nothing
unsnoc (BS buf o l) = Just (prim__getBits8 buf (o + l-1), BS buf o (l-1))

--------------------------------------------------------------------------------
--          Mapping ByteStrings
--------------------------------------------------------------------------------

||| Converts every `Bits8` in a `ByteString` by applying the given
||| function. O(n).
export
map : (Bits8 -> Bits8) -> ByteString -> ByteString
map f bs = generate bs.len (\b => f $ unsafeGetBits8 b bs)

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every lower-case character to its upper-case form.
export
toUpper : ByteString -> ByteString
toUpper = map (cast . Prelude.toUpper . cast)

||| Interpreting the values stored in a `ByteString` as 8 bit characters,
||| convert every upper-case character to its lower-case form.
export
toLower : ByteString -> ByteString
toLower = map (cast . Prelude.toLower . cast)

export
reverse : ByteString -> ByteString
reverse bs = generate bs.len (\n => unsafeGetBits8 (bs.len - 1 - n) bs)

--------------------------------------------------------------------------------
--          Folding
--------------------------------------------------------------------------------

||| True, if the predicate holds for all bytes in the given `ByteString`
export
all : (Bits8 -> Bool) -> ByteString -> Bool
all p bs = go bs.len
  where go : Bits32 -> Bool
        go 0 = True
        go n =
          let n2 = n-1
           in if p (unsafeGetBits8 n2 bs)
              then go (assert_smaller n n2) else False

||| True, if the predicate holds for at least one byte in the given `ByteString`
export
any : (Bits8 -> Bool) -> ByteString -> Bool
any p bs = go bs.len
  where go : Bits32 -> Bool
        go 0 = False
        go n =
          let n2 = n-1
           in if p (unsafeGetBits8 n2 bs)
              then True else go (assert_smaller n n2)

||| True, if the given `Bits8` appears in the `ByteString`.
export %inline
elem : Bits8 -> ByteString -> Bool
elem b = any (b ==)

export
foldl : (a -> Bits8 -> a) -> a -> ByteString -> a
foldl f ini bs = go 0 ini
  where go : Bits32 -> a -> a
        go n acc = case getBits8 n bs of
          Nothing => acc
          Just v  => go (assert_smaller n (n+1)) (f acc v)

export
foldr : (Bits8 -> a -> a) -> a -> ByteString -> a
foldr f ini bs = go bs.len ini
  where go : Bits32 -> a -> a
        go 0 acc = acc
        go n acc =
          let ix = n - 1
           in go (assert_smaller n ix) (f (unsafeGetBits8 ix bs) acc)

||| The `findIndex` function takes a predicate and a `ByteString` and
||| returns the index of the first element in the ByteString
||| satisfying the predicate.
export
findIndex : (Bits8 -> Bool) -> ByteString -> Maybe Bits32
findIndex p bs = go 0 bs.len
  where go : Bits32 -> Bits32 -> Maybe Bits32
        go n l =
          if n >= l then Nothing
          else if p (unsafeGetBits8 n bs) then Just n
          else go (assert_smaller n (n+1)) l

||| Return the index of the first occurence of the given
||| byte in the `ByteString`, or `Nothing`, if the byte
||| does not appear in the ByteString.
export
elemIndex : Bits8 -> ByteString -> Maybe Bits32
elemIndex c = findIndex (c ==)

export
find : (Bits8 -> Bool) -> ByteString -> Maybe Bits8
find p bs = (`unsafeGetBits8` bs) <$> findIndex p bs

--------------------------------------------------------------------------------
--          Substrings
--------------------------------------------------------------------------------

findIndexOrLength : (Bits8 -> Bool) -> ByteString -> Bits32
findIndexOrLength p bs = go 0 bs.len
  where go : Bits32 -> Bits32 -> Bits32
        go n l = if n >= l then l
                 else if p (unsafeGetBits8 n bs) then n
                 else go (assert_smaller n (n+1)) l

findFromEndUntil : (Bits8 -> Bool) -> ByteString -> Bits32
findFromEndUntil p bs = go bs.len
  where go : Bits32 -> Bits32
        go 0 = 0
        go n =
          let n2 = n - 1
           in if p (unsafeGetBits8 n2 bs) then n else go (assert_smaller n n2)

||| Like `substr` for `String`, this extracts a substring
||| of the given `ByteString` at the given start position
||| and of the given length. If the `start` position is out
||| of bounds, the empty `ByteString` is returned. If the
||| length is too large, a substring going till the end of
||| the original `ByteString` is returned. O(1).
export
substring : (start,length : Bits32) -> ByteString -> ByteString
substring start length (BS buf o l) =
  if start >= l then empty
  else BS buf (o + start) (min (l - start) length)

generateMaybe : Bits32 -> (Bits32 -> Maybe Bits8) -> ByteString
generateMaybe 0 _ = empty
generateMaybe l f = unsafePerformIO $ fromPrim $ go 0 0 (prim__newBuffer l)
  where go : (ix,at : Bits32) -> Buffer -> PrimIO ByteString
        go ix at buf w =
          if ix >= l then MkIORes (BS buf 0 at) w else
          case f ix of
            Nothing => go (assert_smaller ix $ ix+1) at buf w
            Just b  => case prim__setBits8 buf at b w of
              MkIORes 0 w2 => go (assert_smaller ix $ ix+1) (at + 1) buf w2
              MkIORes _ w2 => go (assert_smaller ix $ ix+1) (at + 1) buf w2

export
mapMaybe : (Bits8 -> Maybe Bits8) -> ByteString -> ByteString
mapMaybe f bs = generateMaybe bs.len (\b => f $ unsafeGetBits8 b bs)

export
filter : (Bits8 -> Bool) -> ByteString -> ByteString
filter p = mapMaybe (\b => if p b then Just b else Nothing)

||| Return a `ByteString` with the first `n` values of
||| the input string. O(1)
export
take : Bits32 -> ByteString -> ByteString
take n (BS buf o l) = BS buf o (min n l)

||| Return a `ByteString` with the last `n` values of
||| the input string. O(1)
export
takeEnd : Bits32 -> ByteString -> ByteString
takeEnd n (BS buf o l) =
  let n' = min n l in BS buf (o + (l - n')) n'

||| Remove the first `n` values from a `ByteString`. O(1)
export
drop : Bits32 -> ByteString -> ByteString
drop n (BS buf o l) = if n >= l then empty else BS buf (o + n) (l - n)

||| Remove the last `n` values from a `ByteString`. O(1)
export
dropEnd : Bits32 -> ByteString -> ByteString
dropEnd n (BS buf o l) = if n >= l then empty else BS buf o (l - n) 

export
splitAt : Bits32 -> ByteString -> (ByteString, ByteString)
splitAt 0 bs           = (empty, bs)
splitAt n (BS buf o l) = 
  if n >= l then (BS buf o l, empty)
  else (BS buf o n, BS buf (o+n) (l -n))

||| Extracts the longest prefix of elements satisfying the
||| predicate.
export
takeWhile : (Bits8 -> Bool) -> ByteString -> ByteString
takeWhile p bs = take (findIndexOrLength (not . p) bs) bs

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate.
export
takeWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
takeWhileEnd f bs = drop (findFromEndUntil (not . f) bs) bs

||| Drops the longest (possibly empty) prefix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhile : (Bits8 -> Bool) -> ByteString -> ByteString
dropWhile f bs = drop (findIndexOrLength (not . f) bs) bs

||| Drops the longest (possibly empty) suffix of elements
||| satisfying the predicate and returns the remainder.
export
dropWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
dropWhileEnd f bs = take (findFromEndUntil (not . f) bs) bs

||| Returns the longest (possibly empty) prefix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
break : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
break p bs = let n = findIndexOrLength p bs in (take n bs, drop n bs)

||| Returns the longest (possibly empty) suffix of elements which do not
||| satisfy the predicate and the remainder of the string.
export
breakEnd : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
breakEnd  p bs = splitAt (findFromEndUntil p bs) bs

||| Returns the longest (possibly empty) prefix of elements
||| satisfying the predicate and the remainder of the string.
export %inline
span : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
span p = break (not . p)

||| Returns the longest (possibly empty) suffix of elements
||| satisfying the predicate and the remainder of the string.
export
spanEnd : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
spanEnd  p bs = splitAt (findFromEndUntil (not . p) bs) bs

||| Splits a 'ByteString' into components delimited by
||| separators, where the predicate returns True for a separator element.
||| The resulting components do not contain the separators. Two adjacent
||| separators result in an empty component in the output. eg.
export
splitWith : (Bits8 -> Bool) -> ByteString -> List ByteString
splitWith _ (BS _ _ 0)   = []
splitWith p (BS buf o l) = go 0 o 0 Nil
  where go :  (index         : Bits32)
           -> (currentOffset : Bits32)
           -> (currentLength : Bits32)
           -> List ByteString
           -> List ByteString
        go ix co cl bs =
          if ix >= l then reverse (BS buf co cl :: bs)
          else if p (prim__getBits8 buf (ix + o)) then
            let nbs = BS buf co cl :: bs
             in go (assert_smaller ix (ix+1)) (co+cl+1) 0 nbs
          else go (assert_smaller ix (ix+1)) co (cl+1) bs

||| Break a `ByteString` into pieces separated by the byte
||| argument, consuming the delimiter.
||| 
||| As for all splitting functions in this library, this function does
||| not copy the substrings, it just constructs new `ByteString`s that
||| are slices of the original.
export
split : Bits8 -> ByteString -> List ByteString
split b = splitWith (b ==)

--------------------------------------------------------------------------------
--          Reading and Writing from and to Files
--------------------------------------------------------------------------------

export
readChunk : HasIO io => Bits32 -> File -> io (Either FileError ByteString)
readChunk max (FHandle h) = do
  let buf = prim__newBuffer max
  read     <- primIO (prim__readBufferData h buf 0 max)
  if read >= 0
     then pure (Right $ BS buf 0 (cast read))
     else pure (Left FileReadError)

export
write : HasIO io => File -> ByteString -> io (Either (FileError,Int) ())
write h (BS buf o l) = writeBufferData h buf (cast o) (cast l)
