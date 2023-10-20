module Data.Buffer.Indexed

import Algebra.Solver.Semiring
import Network.FFI
import Network.Socket.Raw
import System.File
import public Data.Buffer
import public Data.Buffer.Index
import public Data.Nat.BSExtra

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
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> Buffer

%foreign "scheme:blodwen-buffer-getstring"
         "node:lambda:(buf,offset,len)=>buf.slice(Number(offset), Number(offset+len)).toString('utf-8')"
prim__getString : Buffer -> (offset,len : Integer) -> String

%foreign "scheme:blodwen-buffer-copydata"
         "node:lambda:(b1,o1,length,b2,o2)=>b1.copy(Number(b2),Number(o2),Number(o1),Number(o1+length))"
prim__copy : (src : Buffer) -> (srcOffset, len : Integer) ->
             (dst : Buffer) -> (dstOffset : Integer) -> PrimIO ()

%inline
unsafe : PrimIO a -> a
unsafe io = unsafePerformIO $ fromPrim io

--------------------------------------------------------------------------------
--          Types
--------------------------------------------------------------------------------

||| An immutable `Buffer` indexed over its size.
export
data IBuffer : Nat -> Type where
  Buf : (buf : Buffer) -> IBuffer len

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

||| Copy the given `ByteString` and write its content to a freshly
||| allocated buffer.
export
toBuffer : ByteString -> IO Buffer
toBuffer (BS s $ BV (Buf buf) o _) = do
  b2 <- pure $ prim__newBuf (cast s)
  fromPrim $ prim__copy buf (cast o) (cast s) b2 0
  pure b2

--------------------------------------------------------------------------------
--          IBuffer
--------------------------------------------------------------------------------

export
toString : IBuffer n -> (off,len : Nat) -> (0 _ : LTE (off + len) n) => String
toString (Buf buf) off len = prim__getString buf (cast off) (cast len)

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
byteFromEnd :
     {end : _}
  -> (x : Nat)
  -> {auto 0 lt : LT x end}
  -> IBuffer n
  -> {auto 0 lte : LTE end n}
  -> Bits8
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

  where
    go : (as : List a) -> (x  : Nat) -> Buffer -> PrimIO Buffer
    go []        ix buf w = MkIORes buf w
    go (b :: bs) ix buf w =
      let MkIORes () w2 = writeByte ix (f b) buf w
       in go bs (ix+1) buf w2

||| Convert an UTF-8 string to a buffer
export
fromString : (s : String) -> IBuffer (cast $ stringByteLength s)
fromString s =
  Buf $ unsafe $ \w =>
    let buf            := prim__newBuf (cast $ stringByteLength s)
        MkIORes () w2  := toPrim (setString buf 0 s) w
     in MkIORes buf w2

export
generate : (n : Nat) -> (Index n -> Bits8) -> IBuffer n
generate n f = unsafe $ go n (prim__newBuf $ cast n)

  where
    go : (k : Nat) -> (0 lt : LTE k n) => Buffer -> PrimIO (IBuffer n)
    go 0     buf w = MkIORes (Buf buf) w
    go (S k) buf w =
      let MkIORes () w2 = writeByte k (f $ toIndex k) buf w
       in go k buf w2

public export
totLength : List ByteString -> Nat
totLength []             = 0
totLength (BS n _ :: xs) = n + totLength xs

export
concatBuffer : (ps  : List ByteString) -> IBuffer (totLength ps)
concatBuffer ps =
  unsafe $ go ps 0 (prim__newBuf $ cast $ totLength ps) Refl
  where
    go :
         (qs : List ByteString)
      -> (o  : Nat)
      -> Buffer
      -> (0 prf : (o + totLength qs) === totLength ps)
      -> PrimIO (IBuffer $ totLength ps)
    go []                               o buf prf w = MkIORes (Buf buf) w
    go (BS 0 _                   :: xs) o buf prf w = go xs o buf prf w
    go (BS k (BV (Buf src) so _) :: xs) o buf prf w =
      let MkIORes () w2 := prim__copy src (cast so) (cast k) buf (cast o) w
          0 pp := solveNat [k, o, totLength xs]
                   ((k .+. o) +. totLength xs)
                   (o .+ (k .+. totLength xs))
       in go xs (k + o) buf (trans pp prf) w2

export
generateMaybe : (n : Nat) -> (Index n -> Maybe Bits8) -> ByteString
generateMaybe n f =
  unsafe $ go n 0 (plusZeroRightNeutral n) 0 (prim__newBuf $ cast n)

  where
    go :
         (c,ix : Nat)
      -> (0 prf : c + ix === n)
      -> (pos  : Nat)
      -> Buffer
      -> PrimIO ByteString
    go 0     ix prf pos buf w = MkIORes (BS pos $ BV (Buf buf) 0 refl) w
    go (S k) ix prf pos buf w = case f (toIndexLT ix $ eqToLTE prf) of
      Nothing => go k (S ix) (sumEqLemma k ix prf) pos buf w
      Just b  => let MkIORes () w2 := writeByte pos b buf w
                  in go k (S ix) (sumEqLemma k ix prf) (pos + 1) buf w2

--------------------------------------------------------------------------------
--          Reading and Writing from and to Files
--------------------------------------------------------------------------------

||| Wrappes a mutable buffer in an `IBuffer`.
|||
||| Client code is responsible to make sure the original buffer is no longer
||| used.
export
unsafeMakeBuffer : Buffer -> IBuffer k
unsafeMakeBuffer = Buf

||| Wrappes a mutable of known size in a `ByteString`.
|||
||| Client code is responsible to make sure the original buffer is no longer
||| used.
export
unsafeByteString : (k : Nat) -> Buffer -> ByteString
unsafeByteString k b = BS k $ BV (unsafeMakeBuffer {k} b) 0 %search

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
writeBuffer :
     {auto _ : HasIO io}
  -> File
  -> (offset,size : Nat)
  -> IBuffer n
  -> io (Either (FileError,Int) ())
writeBuffer h o s (Buf buf) = writeBufferData h buf (cast o) (cast s)

export
readByteString :
     {auto _ : HasIO io}
  -> Nat
  -> File
  -> io (Either FileError ByteString)
readByteString max f = do
  Right (k ** buf) <- readBuffer max f | Left err => pure (Left err)
  pure $ Right (BS k $ BV buf 0 refl)

export %inline
writeByteVect :
     {n : _}
  -> {auto _ : HasIO io}
  -> File
  -> ByteVect n
  -> io (Either (FileError,Int) ())
writeByteVect h (BV buf o _) = writeBuffer h o n buf

export %inline
writeByteString :
     {auto _ : HasIO io}
  -> File
  -> ByteString
  -> io (Either (FileError,Int) ())
writeByteString h (BS n bs) = writeByteVect h bs

export
recvBuffer :
     {auto _ : HasIO io}
  -> Nat
  -> Socket
  -> io (Either SocketError (k ** IBuffer k))
recvBuffer max sock = do
  Just buffer <- newBuffer (cast max) | Nothing => pure $ Left (-1)
  ret <- primIO $ prim__idrnet_recv_bytes sock.descriptor buffer (cast max) 0
  case ret >= 0 of
    False => pure $ Left ret
    True  => pure $ Right (cast ret ** Buf buffer)

export
recvByteString :
     {auto _ : HasIO io}
  -> Nat
  -> Socket
  -> io (Either SocketError ByteString)
recvByteString max sock = do
  Right (k ** buf) <- recvBuffer max sock | Left err => pure (Left err)
  pure $ Right (BS k $ BV buf 0 refl)
