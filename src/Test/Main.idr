module Test.Main

import Data.ByteString
import Data.SOP
import Data.Vect
import Hedgehog

--------------------------------------------------------------------------------
--          Generator
--------------------------------------------------------------------------------

smallBits32 : Gen Bits32
smallBits32 = bits32 (linear 0 10)

byte : Gen Bits8
byte = bits8 $ linear 0 0xff

byteList : Gen (List Bits8)
byteList = list (linear 0 30) byte

bytestring : Gen ByteString
bytestring = 
  let bs1         = pack <$> byteList
      bs2         = [| substring smallBits32 smallBits32 bs1 |]
   in choice [bs1, bs2]

latinString : Gen String
latinString = string (linear 0 30) latin

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

unpackPack : Property
unpackPack = property $ do
  bs <- forAll byteList
  bs === unpack (pack bs)

packUnpack : Property
packUnpack = property $ do
  bs <- forAll bytestring
  bs === pack (unpack bs)

singletonHead : Property
singletonHead = property $ do
  b <- forAll byte
  Just b === head (singleton b)

packNull : Property
packNull = property $ do
  bs <- forAll byteList
  null bs === null (pack bs)

packLength : Property
packLength = property $ do
  bs <- forAll byteList
  length bs === cast (length $ pack bs)

consUncons : Property
consUncons = property $ do
  [b,bs] <- forAll $ np [byte,bytestring]
  Just (b,bs) === uncons (cons b bs)

unconsCons : Property
unconsCons = property $ do
  [b,bs] <- forAll $ np [byte,bytestring]
  let bs' = cons b bs
  Just bs' === map (uncurry cons) (uncons bs')

snocUnsnoc : Property
snocUnsnoc = property $ do
  [b,bs] <- forAll $ np [byte,bytestring]
  Just (b,bs) === unsnoc (snoc b bs)

unsnocSnoc : Property
unsnocSnoc = property $ do
  [b,bs] <- forAll $ np [byte,bytestring]
  let bs' = snoc b bs
  Just bs' === map (uncurry snoc) (unsnoc bs')

appendNeutralLeft : Property
appendNeutralLeft = property $ do
  bs <- forAll bytestring
  bs === (neutral <+> bs)

appendNeutralRight : Property
appendNeutralRight = property $ do
  bs <- forAll bytestring
  bs === (bs <+> neutral)

appendAssociative : Property
appendAssociative = property $ do
  [bs1,bs2,bs3] <- forAll $ np [bytestring,bytestring,bytestring]
  ((bs1 <+> bs2) <+> bs3) === (bs1 <+> (bs2 <+> bs3))

prop_fastConcat : Property
prop_fastConcat = property $ do
  bss <- forAll (list (linear 0 10) byteList)
  fastConcat (pack <$> bss) === pack (concat bss)

consHead : Property
consHead = property $ do
  [b,bs] <- forAll $ np [byte, bytestring]
  Just b === head (cons b bs)

snocLast : Property
snocLast = property $ do
  [b,bs] <- forAll $ np [byte, bytestring]
  Just b === last (snoc b bs)

consTail : Property
consTail = property $ do
  [b,bs] <- forAll $ np [byte, bytestring]
  Just bs === tail (cons b bs)

snocInit : Property
snocInit = property $ do
  [b,bs] <- forAll $ np [byte, bytestring]
  Just bs === init (snoc b bs)

prop_substring : Property
prop_substring = property $ do
  [start,len,str] <- forAll $ np [smallBits32,smallBits32,latinString]
  let ss = substring start len (fromString str)

  fromString (substr (cast start) (cast len) str) ===
  substring start len (fromString str)

main : IO ()
main = test . pure $ MkGroup "ByteString"
  [ ("unpackPack", unpackPack)
  , ("packUnpack", packUnpack)
  , ("consUncons", consUncons)
  , ("unsnocSnoc", unsnocSnoc)
  , ("snocUnsnoc", snocUnsnoc)
  , ("unconsCons", unconsCons)
  , ("singletonHead", singletonHead)
  , ("packNull", packNull)
  , ("packLength", packLength)
  , ("appendNeutralRight", appendNeutralRight)
  , ("appendNeutralLeft", appendNeutralLeft)
  , ("appendAssociative", appendAssociative)
  , ("prop_fastConcat", prop_fastConcat)
  , ("consHead", consHead)
  , ("consTail", consTail)
  , ("snocLast", snocLast)
  , ("snocInit", snocInit)
  , ("prop_substring", prop_substring)
  ]
