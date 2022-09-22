module Test.Main

import Data.Buffer.Indexed
import Data.ByteString
import Data.List
import Data.Maybe
import Data.SOP
import Data.Vect
import Hedgehog

--------------------------------------------------------------------------------
--          Generator
--------------------------------------------------------------------------------

smallNat : Gen Nat
smallNat = nat (linear 0 10)

byte : Gen Bits8
byte = bits8 $ linear 0 0xff

byteList : Gen (List Bits8)
byteList = list (linear 0 30) byte

-- we make sure to not only generate `ByteString`s with
-- an offset of 0.
bytestring : Gen ByteString
bytestring =
  let bs1 := pack <$> byteList
      bs2 := [| substring smallNat smallNat bs1 |]
   in choice [bs1, bs2]

asciiString : Gen String
asciiString = string (linear 0 30) ascii

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
  [start,len,str] <- forAll $ np [smallNat,smallNat,asciiString]
  let ss = substring start len (fromString str)

  fromString (substr (cast start) (cast len) str) ===
  substring start len (fromString str)

reverseReverse : Property
reverseReverse = property $ do
  bs <- forAll bytestring
  bs === reverse (reverse bs)

fun : Bits8 -> Maybe Bits8
fun b = if b < 128 then Just (128 - b) else Nothing

prop_mapMaybeId : Property
prop_mapMaybeId = property $ do
  bs <- forAll byteList
  mapMaybe Just (pack bs) === pack bs

prop_mapMaybe : Property
prop_mapMaybe = property $ do
  bs <- forAll byteList
  footnote "pack bs = \{show $ pack bs}"
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
  [n,bs] <- forAll $ np [nat (linear 0 30), bytestring]
  takeEnd n bs === reverse (take n $ reverse bs)

prop_drop : Property
prop_drop = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), byteList]
  drop (cast n) (pack bs) === pack (drop n bs)

prop_dropEnd : Property
prop_dropEnd = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), bytestring]
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

prop_infix : Property
prop_infix = property $ do
  [bs1,bs2] <- forAll $ np [bytestring,bytestring]
  isInfixOf bs1 bs2 === isInfixOf (unpack bs1) (unpack bs2)

prop_prefix : Property
prop_prefix = property $ do
  [bs1,bs2] <- forAll $ np [bytestring,bytestring]
  isPrefixOf bs1 bs2 === isPrefixOf (unpack bs1) (unpack bs2)

prop_suffix : Property
prop_suffix = property $ do
  [bs1,bs2] <- forAll $ np [bytestring,bytestring]
  isSuffixOf bs1 bs2 === isSuffixOf (unpack bs1) (unpack bs2)


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
  , ("prop_mapMaybeId", prop_mapMaybeId)
  , ("prop_mapMaybe", prop_mapMaybe)
  , ("prop_filter", prop_filter)
  , ("prop_drop", prop_drop)
  , ("prop_take", prop_take)
  , ("prop_takeWhile", prop_takeWhile)
  , ("prop_takeWhileEnd", prop_takeWhileEnd)
  , ("prop_dropWhileEnd", prop_dropWhileEnd)
  , ("prop_breakAppend", prop_breakAppend)
  , ("prop_breakFirst", prop_breakFirst)
  , ("prop_infix", prop_infix)
  , ("prop_prefix", prop_prefix)
  , ("prop_suffix", prop_suffix)
  ]
