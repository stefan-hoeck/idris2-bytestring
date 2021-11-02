module Data.ByteString.Internal

import Data.Buffer
import Data.List

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
   in BS (unsafePerformIO $ go' len) 0 len
  where go : List a -> Bits32 -> Buffer -> PrimIO Buffer
        go []        _  buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          case prim__setBits8 buf ix (f b) w of
            -- this is a hack: Without this (completely useless) pattern
            -- match, the call to `prim__setBits8` is erased and ignored
            MkIORes 0 w2 => go bs (ix+1) buf w2
            MkIORes _ w2 => go bs (ix+1) buf w2

        go' : Bits32 -> IO Buffer
        go' l = fromPrim $ go vs 0 (prim__newBuffer l)

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
generate l f =
  BS (unsafePerformIO $ fromPrim $ go l (prim__newBuffer l)) 0 l
  where go : Bits32 -> Buffer -> PrimIO Buffer
        go 0 buf w = MkIORes buf w
        go n buf w =
          let ix = n - 1
           in case prim__setBits8 buf ix (f ix) w of
                MkIORes 0 w2 => go (assert_smaller n ix) buf w2
                MkIORes _ w2 => go (assert_smaller n ix) buf w2

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
     in BS (unsafePerformIO $ fromPrim $ go bs2 (prim__newBuffer tot) 0) 0 tot
      where go : List ByteString -> Buffer -> (offset : Bits32) -> PrimIO Buffer
            go []        buf o w = MkIORes buf w
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

--------------------------------------------------------------------------------
--          Substrings
--------------------------------------------------------------------------------

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
