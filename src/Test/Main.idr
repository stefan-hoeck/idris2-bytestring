module Test.Main

import Data.ByteString
import Data.List
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

-- we make sure to not only generate `ByteString`s with
-- an offset of 0.
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

reverseReverse : Property
reverseReverse = property $ do
  bs <- forAll bytestring
  bs === reverse (reverse bs)

fun : Bits8 -> Maybe Bits8
fun b = if b < 128 then Just (128 - b) else Nothing

prop_mapMaybe : Property
prop_mapMaybe = property $ do
  bs <- forAll byteList
  mapMaybe fun (pack bs) === pack (mapMaybe fun bs)

prop_filter : Property
prop_filter = property $ do
  bs <- forAll byteList
  filter (< 100) (pack bs) === pack (filter (< 100) bs)

prop_take : Property
prop_take = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), byteList]
  take (cast n) (pack bs) === pack (take n bs)

prop_takeEnd : Property
prop_takeEnd = property $ do
  [n,bs] <- forAll $ np [bits32 (linear 0 30), bytestring]
  takeEnd n bs === reverse (take n $ reverse bs)

prop_drop : Property
prop_drop = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), byteList]
  drop (cast n) (pack bs) === pack (drop n bs)

prop_dropEnd : Property
prop_dropEnd = property $ do
  [n,bs] <- forAll $ np [bits32 (linear 0 30), bytestring]
  dropEnd n bs === reverse (drop n $ reverse bs)

prop_takeWhile : Property
prop_takeWhile = property $ do
  bs <- forAll byteList
  takeWhile (< 100) (pack bs) ===
  pack (takeWhile (< 100) bs)

prop_takeWhileEnd : Property
prop_takeWhileEnd = property $ do
  bs <- forAll bytestring
  takeWhileEnd (< 100) bs ===
  reverse (takeWhile (< 100) $ reverse bs)

prop_dropWhileEnd : Property
prop_dropWhileEnd = property $ do
  bs <- forAll bytestring
  dropWhileEnd (< 100) bs ===
  reverse (dropWhile (< 100) $ reverse bs)

prop_breakAppend : Property
prop_breakAppend = property $ do
  bs <- forAll bytestring
  let (a,b) = break (< 100) bs
  bs === (a <+> b)

prop_breakFirst : Property
prop_breakFirst = property $ do
  bs <- forAll bytestring
  let (a,b) = break (< 100) bs
  assert $ all (>= 100) a


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
  , ("reverseReverse", reverseReverse)
  , ("prop_mapMaybe", prop_mapMaybe)
  , ("prop_filter", prop_filter)
  , ("prop_drop", prop_drop)
  , ("prop_take", prop_take)
  , ("prop_takeWhile", prop_takeWhile)
  , ("prop_takeWhileEnd", prop_takeWhileEnd)
  , ("prop_dropWhileEnd", prop_dropWhileEnd)
  , ("prop_breakAppend", prop_breakAppend)
  , ("prop_breakFirst", prop_breakFirst)
  ]
