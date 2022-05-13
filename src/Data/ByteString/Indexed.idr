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
getByteFromEnd : {n : _} -> (x : Nat) -> (0 lt : LT x n) => ByteString n -> Bits8
getByteFromEnd x =
  getByte (n `minus` S x) {lt = minusLT x n lt}

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
toList f bs     = go Nil n reflexive
  where go : List a -> (x : Nat) -> (0 prf : LTE x n) -> List a
        go xs 0     _ = xs
        go xs (S j) p = go (f (getByte j bs) :: xs) j (lteSuccLeft p)

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
generate : (n : Nat) -> (Nat -> Bits8) -> ByteString n
-- generate l f = unsafePerformIO $ fromPrim $ go l (prim__newBuffer l)
--   where go : Bits32 -> Buffer -> PrimIO ByteString
--         go 0 buf w = MkIORes (BS buf 0 l) w
--         go n buf w =
--           let ix = n - 1
--            in case prim__setBits8 buf ix (f ix) w of
--                 MkIORes 0 w2 => go (assert_smaller n ix) buf w2
--                 MkIORes _ w2 => go (assert_smaller n ix) buf w2

export
replicate : (n : Nat) -> Bits8 -> ByteString n
replicate n = generate n . const

--------------------------------------------------------------------------------
--          Concatenating ByteStrings
--------------------------------------------------------------------------------
