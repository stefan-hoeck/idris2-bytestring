module Data.Buffer.Indexed

import Algebra.Solver.Semiring
import public Data.Buffer.Index
import Data.Nat.BSExtra
import Data.Buffer
import System.File

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "node:lambda:(buf,offset)=>buf.readUInt8(Number(offset))"
prim__getByte : Buffer -> (offset : Integer) -> Bits8

%foreign "scheme:blodwen-buffer-setbyte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, Number(offset))"
prim__setByte : Buffer -> (offset : Integer) -> (val : Bits8) -> PrimIO ()

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> Buffer

%inline
unsafe : PrimIO a -> a
unsafe io = unsafePerformIO $ fromPrim io

--------------------------------------------------------------------------------
--          IBuffer
--------------------------------------------------------------------------------

||| An immutable `Buffer` indexed over its size.
export
data IBuffer : Nat -> Type where
  Buf : (buf : Buffer) -> IBuffer len

||| Reads the value of a `ByteString` at the given position
export %inline
byteAt : (x : Nat) -> (0 lt : LT x n) => IBuffer n -> Bits8
byteAt x (Buf buf) = prim__getByte buf (cast x)

||| Reads the value of a `ByteString` at the given position
export %inline
byteAtO : (o : Nat) -> IBuffer n -> (0 off : Offset (S c) o n) => Bits8
byteAtO o buf = byteAt o buf {lt = offsetLTE off}

||| Reads the value of a `ByteString` conting from the end of the buffer
export %inline
byteFromEnd :  {end : _}
            -> (x : Nat)
            -> (0 lt : LT x end)
            => IBuffer n
            -> (0 lte : LTE end n)
            => Bits8
byteFromEnd x (Buf buf) =
  prim__getByte buf (natToInteger end - natToInteger x - 1)

%inline
writeByte :  (x : Nat) -> (v : Bits8) -> Buffer -> PrimIO ()
writeByte x v buf = prim__setByte buf (cast x) v

||| The empty `Buffer`.
export
empty : IBuffer 0
empty = Buf (prim__newBuf 0)

||| Converts a list of values to an `IBuffer` using
||| the given conversion function. O(n).
export
fromList : (a -> Bits8) -> (as : List a) -> IBuffer (length as)
fromList f vs = Buf $ unsafe $ go vs 0 (prim__newBuf $ cast $ length vs)
  where go : (as : List a) -> (x  : Nat) -> Buffer -> PrimIO Buffer
        go []        ix buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          let MkIORes () w2 = writeByte ix (f b) buf w
           in go bs (ix+1) buf w2

export
generate : (n : Nat) -> (Index n -> Bits8) -> IBuffer n
generate n f = unsafe $ go n (prim__newBuf $ cast n)
  where go : (k : Nat) -> (0 lt : LTE k n) => Buffer -> PrimIO (IBuffer n)
        go 0     buf w = MkIORes (Buf buf) w
        go (S k) buf w =
          let MkIORes () w2 = writeByte k (f $ toIndex k) buf w
           in go k buf w2

public export
totLength : {0 p : Nat -> Type} -> List (n ** p n) -> Nat
totLength []               = 0
totLength ((n ** _) :: xs) = n + totLength xs

export
concatMany :  {0 p : Nat -> Type}
           -> (ps  : List (n ** p n))
           -> (f   : forall n . Index n -> p n -> Bits8)
           -> IBuffer (totLength ps)
concatMany ps f =
  unsafe $ go ps 0 (prim__newBuf $ cast $ totLength ps) Refl
  where copy :  p n
             -> (ix : Nat)
             -> (0 prf : LT ix n)
             => (o : Nat)
             -> Buffer
             -> PrimIO ()
        copy pn ix o buf w =
          let MkIORes () w2 := writeByte (ix + o) (f (Element ix prf) pn) buf w
           in case ix of
                Z     => MkIORes () w2
                (S k) => copy pn k o buf w2

        go :  (qs : List (n ** p n))
           -> (o  : Nat)
           -> Buffer
           -> (0 prf : (o + totLength qs) === totLength ps)
           -> PrimIO (IBuffer m)
        go []                   o buf prf w = MkIORes (Buf buf) w
        go ((0   ** snd) :: xs) o buf prf w = go xs o buf prf w
        go ((S k ** snd) :: xs) o buf prf w =
          let MkIORes () w2 := copy snd k o buf w
              0 pp := solve [k, o, totLength xs]
                       (1 + ((k .+. o)+. totLength xs))
                       (o .+ (1 + (k .+. totLength xs)))
           in go xs (S k + o) buf (trans pp prf) w2

export
generateMaybe : (n : Nat) -> (Index n -> Maybe Bits8) -> (k ** IBuffer k)
generateMaybe n f = unsafe $ go n 0 (plusZeroRightNeutral n) 0 (prim__newBuf $ cast n)
  where go :  (c,ix : Nat)
           -> (0 prf : c + ix === n)
           -> (pos  : Nat)
           -> Buffer
           -> PrimIO (k ** IBuffer k)
        go 0     ix prf pos buf w = MkIORes (pos ** Buf buf) w
        go (S k) ix prf pos buf w = case f (toIndexLT ix $ eqToLTE prf) of
          Nothing => go k (S ix) (sumEqLemma k ix prf) pos buf w
          Just b  => let MkIORes () w2 := writeByte pos b buf w
                      in go k (S ix) (sumEqLemma k ix prf) (pos + 1) buf w2

export
readBuffer :  HasIO io => Nat -> File -> io (Either FileError (k ** IBuffer k))
readBuffer max f =
  let buf  := prim__newBuf (cast max)
   in do
    Right read <- readBufferData f buf 0 (cast max)
      | Left err => pure (Left err)
    if read >= 0
       then pure (Right (cast read ** Buf buf))
       else pure (Left FileReadError)

export
writeBuffer : HasIO io
            => File
            -> (offset,size : Nat)
            -> IBuffer n
            -> io (Either (FileError,Int) ())
writeBuffer h o s (Buf buf) = writeBufferData h buf (cast o) (cast s)
