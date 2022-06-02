module Data.Buffer.Indexed

import public Data.Buffer.Index
import Data.Buffer
import System.File

%default total

--------------------------------------------------------------------------------
--          FFI
--------------------------------------------------------------------------------

%foreign "scheme:blodwen-buffer-getbyte"
         "RefC:getBufferByte"
         "node:lambda:(buf,offset)=>buf.readUInt8(offset)"
prim__getByte : Buffer -> (offset : Bits32) -> Bits8

%foreign "scheme:blodwen-buffer-setbyte"
         "RefC:setBufferByte"
         "node:lambda:(buf,offset,value)=>buf.writeUInt8(value, offset)"
prim__setByte : Buffer -> (offset : Bits32) -> (val : Bits8) -> PrimIO Int

%foreign "scheme:blodwen-new-buffer"
         "RefC:newBuffer"
         "node:lambda:s=>Buffer.alloc(s)"
prim__newBuf : Bits32 -> Buffer

%hint
0 refl : LTE n n
refl = reflexive

%hint
0 lsl : (p : LTE (S m) n) => LTE m n
lsl = lteSuccLeft p 

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

mapPrimIO : (a -> b) -> PrimIO a -> PrimIO b
mapPrimIO f g w = let MkIORes va w2 = g w in MkIORes (f va) w2

writeByte :  (x : Bits32) -> (v : Bits8) -> Buffer -> PrimIO Buffer
writeByte x v buf =
  mapPrimIO (\_ => buf) $ prim__setByte buf x v

||| The empty `Buffer`.
export
empty : IBuffer 0
empty = Buf (prim__newBuf 0)

||| Converts a list of values to an `IBuffer` using
||| the given conversion function. O(n).
export
fromList : (a -> Bits8) -> (as : List a) -> IBuffer (length as)
fromList f vs = Buf $ unsafe $ go vs 0 (prim__newBuf $ cast $ length vs)
  where go : (as : List a) -> (x  : Bits32) -> Buffer -> PrimIO Buffer
        go []        ix buf w = MkIORes buf w
        go (b :: bs) ix buf w =
          let MkIORes buf2 w2 = writeByte ix (f b) buf w
           in go bs (ix+1) buf2 w2

export
generate : (n : Nat) -> (Index n -> Bits8) -> IBuffer n
generate n f = unsafe $ go n (prim__newBuf $ cast n)
  where go : (k : Nat) -> (0 lt : LTE k n) => Buffer -> PrimIO (IBuffer n)
        go 0     buf w = MkIORes (Buf buf) w
        go (S k) buf w =
          let MkIORes buf2 w2 = writeByte (cast k) (f $ toIndex k) buf w
           in go k buf2 w2

export
generateMaybe : (n : Nat) -> (Index n -> Maybe Bits8) -> (k ** IBuffer k)
generateMaybe n f = unsafe $ go 0 0 (prim__newBuf $ cast n)
  where go :  (m    : Nat)
           -> (0 lt : LTE m n)
           => (pos  : Bits32)
           -> Buffer
           -> PrimIO (k ** IBuffer k)
        go 0     pos buf w = MkIORes (cast pos ** Buf buf) w
        go (S k) pos buf w = case f (complement $ toIndex k) of
          Nothing => go k pos buf w
          Just b  => let MkIORes buf2 w2 = writeByte pos b buf w
                      in go k (pos + 1) buf2 w2

-- export
-- readBuffer :  HasIO io
--            => Bits32
--            -> File
--            -> io (Either FileError (k ** Buffer k))
-- readBuffer max f = do
--   buf   = fromPrim $ prim__newBuffer (cast max)
--   read     <- primIO (prim__readBufferData h buf 0 max)
--   if read >= 0
--      then pure (Right $ (cast read ** BS buf 0))
--      else pure (Left FileReadError)
-- 
-- export
-- write :  {n : _}
--       -> HasIO io
--       => File
--       -> ByteString n
--       -> io (Either (FileError,Int) ())
-- write h (BS buf o) = writeBufferData h buf (cast o) (cast n)
