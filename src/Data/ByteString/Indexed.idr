module Data.ByteString.Indexed

import Data.Buffer
import Data.DPair
import Data.Nat
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
--          Utilities
--------------------------------------------------------------------------------

Uninhabited (EQ === LT) where
  uninhabited Refl impossible

Uninhabited (Prelude.EQ === GT) where
  uninhabited Refl impossible

Uninhabited (LT === EQ) where
  uninhabited Refl impossible

Uninhabited (Prelude.LT === GT) where
  uninhabited Refl impossible

Uninhabited (Prelude.GT === LT) where
  uninhabited Refl impossible

Uninhabited (Prelude.GT === EQ) where
  uninhabited Refl impossible

0 lteMinus : (n : Nat) -> LTE (S (minus n 0)) (S n)
lteMinus 0     = LTESucc LTEZero
lteMinus (S k) = reflexive

0 minusLT : (m,n : Nat) -> (lt : LT m n) -> LT (minus n (S m)) n
minusLT 0     (S l) lt           = lteMinus l
minusLT (S k) (S l) (LTESucc lt) =
  let lt' = minusLT k l lt in lteSuccRight lt'
minusLT 0     0     lt = absurd lt

0 compLT : (m,n : Nat) -> compare m n === LT -> LTE m n
compLT 0 0         prf = absurd prf
compLT 0     (S k) prf = LTEZero
compLT (S k) 0     prf = absurd prf
compLT (S k) (S j) prf = LTESucc $ compLT k j prf

0 compEQ : (m,n : Nat) -> compare m n === EQ -> LTE n m
compEQ 0 0         prf = LTEZero
compEQ 0     (S k) prf = absurd prf
compEQ (S k) 0     prf = absurd prf
compEQ (S k) (S j) prf = LTESucc $ compEQ k j prf

0 compGT : (m,n : Nat) -> compare m n === GT -> LTE n m
compGT 0 0         prf = absurd prf
compGT 0     (S k) prf = absurd prf
compGT (S k) 0     prf = LTEZero
compGT (S k) (S j) prf = LTESucc $ compGT k j prf


0 minLTE : (m,n : Nat) -> (LTE (min m n) m, LTE (min m n) n)
minLTE m n with (compare m n) proof eq
  _ | LT = (reflexive, compLT m n eq)
  _ | EQ = (compEQ m n eq, reflexive)
  _ | GT = (compGT m n eq, reflexive)

0 ltPlusSuccRight : (k,m,n : Nat) -> LTE (k + S m) n -> LT k n
ltPlusSuccRight 0     m     (S z) (LTESucc _) = LTESucc LTEZero
ltPlusSuccRight (S x) m     (S z) (LTESucc p) =
  let p2 = ltPlusSuccRight x m z p in LTESucc p2

0 ltePlusSuccRight : {k,m,n : Nat} -> LTE (k + S m) n -> LTE (S $ k + m) n
ltePlusSuccRight p = rewrite plusSuccRightSucc k m in p

%hint
0 refl : LTE n n
refl = reflexive

%hint
0 lsl : (p : LTE (S m) n) => LTE m n
lsl = lteSuccLeft p 

--------------------------------------------------------------------------------
--          Index
--------------------------------------------------------------------------------

public export
0 Index : Nat -> Type
Index n = Subset Nat (`LT` n)

public export
toIndex : (k : Nat) -> (0 lt : LT k n) => Index n
toIndex k = Element k lt

public export
fromEnd : {n : _} -> Index n -> Index n
fromEnd (Element k lt) = Element (n `minus` S k) (minusLT k n lt)

public export
0 SubLength : Nat -> Type
SubLength n = Subset Nat (`LTE` n)

public export
sublength : (k : Nat) -> (0 lte : LTE k n) => SubLength n
sublength k = Element k lte

public export
fromIndex : Index n -> SubLength n
fromIndex (Element k _) = Element k %search

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
  BS :  (buf    : Buffer)
     -> (offset : Nat)
     -> ByteString len

||| Wraps a `Buffer` in a `ByteString` *without making a copy*.
||| Use this for efficient reading of data from a file or other resource
||| into a `ByteString`, but make sure to not reuse the
||| `Buffer` in question elsewhere.
export %inline
unsafeFromBuffer : (b : Buffer) -> (n ** ByteString n)
unsafeFromBuffer b = (cast (prim__bufferSize b) ** BS b 0)

||| Reads the value of a `ByteString` at the given position
export %inline
getByte : (x : Nat) -> (0 lt : LT x n) => ByteString n -> Bits8
getByte x (BS buf o) = prim__getBits8 buf (cast $ o + x)

||| Reads the value of a `ByteString` at the given position
export %inline
index : Index n -> ByteString n -> Bits8
index (Element k _) bs = getByte k bs

||| Reads the value of a `ByteString` at the given position
export %inline
indexFromEnd : {n : _} -> Index n -> ByteString n -> Bits8
indexFromEnd x = index (fromEnd x)

||| Reads the value of a `ByteString` at the given position
export %inline
getByteFromEnd : {n : _} -> (x : Nat) -> (0 lt : LT x n) => ByteString n -> Bits8
getByteFromEnd x = indexFromEnd (Element x lt)

--------------------------------------------------------------------------------
--          Making ByteStrings
--------------------------------------------------------------------------------

||| The empty `ByteString`.
export
empty : ByteString 0
empty = BS (prim__newBuffer 0) 0

||| Converts a list of values to a `ByteString` using
||| the given conversion function. O(n).
export
fromList : (a -> Bits8) -> (as : List a) -> ByteString (length as)
fromList f vs =
  let len = cast {to = Bits32} $ length vs
      buf = unsafePerformIO $ fromPrim $ go vs 0 (prim__newBuffer len)
   in BS buf 0
  where go :  (as : List a) -> Bits32 -> Buffer -> PrimIO Buffer
        go []        ix buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          case prim__setBits8 buf ix (f b) w of
            -- this is a hack: Without this (completely useless) pattern
            -- match, the call to `prim__setBits8` is erased and ignored
            MkIORes 0 w2 => go bs (ix+1) buf w2
            MkIORes _ w2 => go bs (ix+1) buf w2

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
  show = show . fastPack . toList cast

--------------------------------------------------------------------------------
--          Comparing ByteStrings
--------------------------------------------------------------------------------

||| Lexicographic comparison of `ByteString`s of distinct length
export
hcomp : {m,n : Nat} -> ByteString m -> ByteString n -> Ordering
hcomp bs1  bs2 = go 0 (min m n) (fst $ minLTE m n) (snd $ minLTE m n)
  where go : (pos, stps : Nat)
           -> (0 p1 : LTE (pos + stps) m)
           -> (0 p2 : LTE (pos + stps) n)
           -> Ordering
        go pos 0     p1 p2 = compare m n
        go pos (S k) p1 p2 =
          let 0 lt1 = ltPlusSuccRight pos k m p1
              0 lt2 = ltPlusSuccRight pos k n p2
           in case compare (getByte pos bs1) (getByte pos bs2) of
                EQ => go (S pos) k (ltePlusSuccRight p1) (ltePlusSuccRight p2)
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
generate n f =
  unsafePerformIO $ fromPrim $ go n (prim__newBuffer $ cast n)
  where go : (k : Nat) -> (0 lt : LTE k n) => Buffer -> PrimIO (ByteString n)
        go 0     buf w = MkIORes (BS buf 0) w
        go (S k) buf w =
          case prim__setBits8 buf (cast k) (f $ toIndex k) w of
            MkIORes 0 w2 => go k buf w2
            MkIORes _ w2 => go k buf w2

export
replicate : (n : Nat) -> Bits8 -> ByteString n
replicate n = generate n . const

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------

public export
totLength : List (n ** ByteString n) -> Nat
totLength []               = 0
totLength [(n ** _)]       = n
totLength ((n ** _) :: xs) = n + totLength xs


||| Concatenate a list of `ByteString`. This allocates
||| a buffer of sufficient size in advance, so it is much
||| faster than `concat`, or `concatMap` for large `ByteString`s.
export
fastConcat : (bs : List (n ** ByteString n)) -> ByteString (totLength bs)
-- fastConcat bs = case filter ((> 0) . len) bs of
--  Nil => empty
--  [b] => b
--  bs2 =>
--    let tot = foldl (\a,b => a + b.len) 0 bs2
--     in unsafePerformIO $ fromPrim $ go bs2 (prim__newBuffer tot) 0
--      where go :  List ByteString
--               -> Buffer
--               -> (offset : Bits32)
--               -> PrimIO ByteString
--            go []        buf o w = MkIORes (BS buf 0 o) w
--            go (BS src so sl :: bs) buf o w =
--              case prim__copyData src so sl buf o w of
--                -- this is a hack: Without this (completely useless) pattern
--                -- match, the call to `prim__setBits8` is erased and ignored
--                MkIORes 0 w2 => go bs buf (o + sl) w2
--                MkIORes _ w2 => go bs buf (o + sl) w2

||| Concatenate two `ByteString`s. O(n + m).
export %inline
append : {m,n : _} -> ByteString m  -> ByteString n -> ByteString (m + n)
append b1 b2 = fastConcat [(m ** b1),(n ** b2)]

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
tail (BS buf o) = BS buf (o+1)

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
init (BS buf o) = BS buf o

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
all p bs = go n
  where go : (k : Nat) -> (0 lt : LTE k n) => Bool
        go 0     = True
        go (S k) = if p (getByte k bs) then go k else False

||| True, if the predicate holds for at least one byte
||| in the given `ByteString`
export
any : {n : _} -> (Bits8 -> Bool) -> ByteString n -> Bool
any p bs = go n
  where go : (k : Nat) -> (0 lt : LTE k n) => Bool
        go 0     = False
        go (S k) = if p (getByte k bs) then True else go k

||| True, if the given `Bits8` appears in the `ByteString`.
export %inline
elem : {n : _} -> Bits8 -> ByteString n -> Bool
elem b = any (b ==)

export
foldl : {n : _} -> (a -> Bits8 -> a) -> a -> ByteString n -> a
foldl f ini bs = go n ini
  where go : (k : Nat) -> (v : a) -> (0 lt : LTE k n) => a
        go 0     v = v
        go (S k) v = go k (f v $ getByteFromEnd k bs)

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
findIndex p bs = go n
  where go : (k : Nat) -> (0 lt : LTE k n) => Maybe (Index n)
        go 0     = Nothing
        go (S k) = case p (getByteFromEnd k bs) of
          True  => Just $ toIndex k
          False => go k

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
findIndexOrLength p bs = go n
  where go : (k : Nat) -> (0 lt : LTE k n) => SubLength n
        go 0     = sublength n
        go (S k) = 
          let x = fromEnd (toIndex k)
           in if p (index x bs) then fromIndex x else go k

-- findFromEndUntil : (Bits8 -> Bool) -> ByteString -> Bits32
-- findFromEndUntil p bs = go bs.len
--   where go : Bits32 -> Bits32
--         go 0 = 0
--         go n =
--           let n2 = n - 1
--            in if p (unsafeGetBits8 n2 bs) then n else go (assert_smaller n n2)
-- 
-- ||| Like `substr` for `String`, this extracts a substring
-- ||| of the given `ByteString` at the given start position
-- ||| and of the given length. If the `start` position is out
-- ||| of bounds, the empty `ByteString` is returned. If the
-- ||| length is too large, a substring going till the end of
-- ||| the original `ByteString` is returned. O(1).
-- export
-- substring : (start,length : Bits32) -> ByteString -> ByteString
-- substring start length (BS buf o l) =
--   if start >= l then empty
--   else BS buf (o + start) (min (l - start) length)
-- 
-- generateMaybe : Bits32 -> (Bits32 -> Maybe Bits8) -> ByteString
-- generateMaybe 0 _ = empty
-- generateMaybe l f = unsafePerformIO $ fromPrim $ go 0 0 (prim__newBuffer l)
--   where go : (ix,at : Bits32) -> Buffer -> PrimIO ByteString
--         go ix at buf w =
--           if ix >= l then MkIORes (BS buf 0 at) w else
--           case f ix of
--             Nothing => go (assert_smaller ix $ ix+1) at buf w
--             Just b  => case prim__setBits8 buf at b w of
--               MkIORes 0 w2 => go (assert_smaller ix $ ix+1) (at + 1) buf w2
--               MkIORes _ w2 => go (assert_smaller ix $ ix+1) (at + 1) buf w2
-- 
-- export
-- mapMaybe : (Bits8 -> Maybe Bits8) -> ByteString -> ByteString
-- mapMaybe f bs = generateMaybe bs.len (\b => f $ unsafeGetBits8 b bs)
-- 
-- export
-- filter : (Bits8 -> Bool) -> ByteString -> ByteString
-- filter p = mapMaybe (\b => if p b then Just b else Nothing)
-- 
-- ||| Return a `ByteString` with the first `n` values of
-- ||| the input string. O(1)
-- export
-- take : Bits32 -> ByteString -> ByteString
-- take n (BS buf o l) = BS buf o (min n l)
-- 
-- ||| Return a `ByteString` with the last `n` values of
-- ||| the input string. O(1)
-- export
-- takeEnd : Bits32 -> ByteString -> ByteString
-- takeEnd n (BS buf o l) =
--   let n' = min n l in BS buf (o + (l - n')) n'
-- 
-- ||| Remove the first `n` values from a `ByteString`. O(1)
-- export
-- drop : Bits32 -> ByteString -> ByteString
-- drop n (BS buf o l) = if n >= l then empty else BS buf (o + n) (l - n)
-- 
-- ||| Remove the last `n` values from a `ByteString`. O(1)
-- export
-- dropEnd : Bits32 -> ByteString -> ByteString
-- dropEnd n (BS buf o l) = if n >= l then empty else BS buf o (l - n) 
-- 
-- export
-- splitAt : Bits32 -> ByteString -> (ByteString, ByteString)
-- splitAt 0 bs           = (empty, bs)
-- splitAt n (BS buf o l) = 
--   if n >= l then (BS buf o l, empty)
--   else (BS buf o n, BS buf (o+n) (l -n))
-- 
-- ||| Extracts the longest prefix of elements satisfying the
-- ||| predicate.
-- export
-- takeWhile : (Bits8 -> Bool) -> ByteString -> ByteString
-- takeWhile p bs = take (findIndexOrLength (not . p) bs) bs
-- 
-- ||| Returns the longest (possibly empty) suffix of elements
-- ||| satisfying the predicate.
-- export
-- takeWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
-- takeWhileEnd f bs = drop (findFromEndUntil (not . f) bs) bs
-- 
-- ||| Drops the longest (possibly empty) prefix of elements
-- ||| satisfying the predicate and returns the remainder.
-- export
-- dropWhile : (Bits8 -> Bool) -> ByteString -> ByteString
-- dropWhile f bs = drop (findIndexOrLength (not . f) bs) bs
-- 
-- ||| Drops the longest (possibly empty) suffix of elements
-- ||| satisfying the predicate and returns the remainder.
-- export
-- dropWhileEnd : (Bits8 -> Bool) -> ByteString -> ByteString
-- dropWhileEnd f bs = take (findFromEndUntil (not . f) bs) bs
-- 
-- ||| Returns the longest (possibly empty) prefix of elements which do not
-- ||| satisfy the predicate and the remainder of the string.
-- export
-- break : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- break p bs = let n = findIndexOrLength p bs in (take n bs, drop n bs)
-- 
-- ||| Returns the longest (possibly empty) suffix of elements which do not
-- ||| satisfy the predicate and the remainder of the string.
-- export
-- breakEnd : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- breakEnd  p bs = splitAt (findFromEndUntil p bs) bs
-- 
-- ||| Returns the longest (possibly empty) prefix of elements
-- ||| satisfying the predicate and the remainder of the string.
-- export %inline
-- span : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- span p = break (not . p)
-- 
-- ||| Returns the longest (possibly empty) suffix of elements
-- ||| satisfying the predicate and the remainder of the string.
-- export
-- spanEnd : (Bits8 -> Bool) -> ByteString -> (ByteString, ByteString)
-- spanEnd  p bs = splitAt (findFromEndUntil (not . p) bs) bs
-- 
-- ||| Splits a 'ByteString' into components delimited by
-- ||| separators, where the predicate returns True for a separator element.
-- ||| The resulting components do not contain the separators. Two adjacent
-- ||| separators result in an empty component in the output. eg.
-- export
-- splitWith : (Bits8 -> Bool) -> ByteString -> List ByteString
-- splitWith _ (BS _ _ 0)   = []
-- splitWith p (BS buf o l) = go 0 o 0 Nil
--   where go :  (index         : Bits32)
--            -> (currentOffset : Bits32)
--            -> (currentLength : Bits32)
--            -> List ByteString
--            -> List ByteString
--         go ix co cl bs =
--           if ix >= l then reverse (BS buf co cl :: bs)
--           else if p (prim__getBits8 buf (ix + o)) then
--             let nbs = BS buf co cl :: bs
--              in go (assert_smaller ix (ix+1)) (co+cl+1) 0 nbs
--           else go (assert_smaller ix (ix+1)) co (cl+1) bs
-- 
-- ||| Break a `ByteString` into pieces separated by the byte
-- ||| argument, consuming the delimiter.
-- ||| 
-- ||| As for all splitting functions in this library, this function does
-- ||| not copy the substrings, it just constructs new `ByteString`s that
-- ||| are slices of the original.
-- export
-- split : Bits8 -> ByteString -> List ByteString
-- split b = splitWith (b ==)
-- 
-- --------------------------------------------------------------------------------
-- --          Reading and Writing from and to Files
-- --------------------------------------------------------------------------------
-- 
-- export
-- readChunk : HasIO io => Bits32 -> File -> io (Either FileError ByteString)
-- readChunk max (FHandle h) = do
--   let buf = prim__newBuffer max
--   read     <- primIO (prim__readBufferData h buf 0 max)
--   if read >= 0
--      then pure (Right $ BS buf 0 (cast read))
--      else pure (Left FileReadError)
-- 
-- export
-- write : HasIO io => File -> ByteString -> io (Either (FileError,Int) ())
-- write h (BS buf o l) = writeBufferData h buf (cast o) (cast l)
