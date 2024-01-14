module Test.Main

import Data.Buffer.Indexed
import Data.Byte
import Data.ByteString as BS
import Data.List
import Data.Maybe
import Data.String
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

digit : Gen Bits8
digit = bits8 $ linear byte_0 byte_9

digit1 : Gen Bits8
digit1 = bits8 $ linear (byte_0 + 1) byte_9

natString : Gen (List Bits8)
natString = [| digit1 :: list (linear 0 20) digit |]

intString : Gen (List Bits8)
intString =
  let pre : Gen (List Bits8)
      pre = element [[], [43], [45]]
   in [| pre ++ natString |]

expString : Gen (List Bits8)
expString =
  let pre : Gen (List Bits8)
      pre =
        element $ map (map cast . Prelude.unpack)
          ["", "E", "E+", "E-", "e", "e+", "e-", "+", "-"]

      nat : Gen (List Bits8)
      nat = [| digit1 :: list (linear 0 1) digit |]
   in [| pre ++ nat |]

dblString : Gen (List Bits8)
dblString =
  let dot : List Bits8 -> List Bits8 -> List Bits8
      dot xs ys = xs ++ [46] ++ ys

      exp : List Bits8 -> List Bits8 -> List Bits8
      exp xs es = xs ++ es

      dotExp : List Bits8 -> List Bits8 -> List Bits8 -> List Bits8
      dotExp xs ys ex = xs ++ [46] ++ ys ++ ex
   in choice
        [ intString
        , [| dot    intString natString |]
        , [| exp    intString expString |]
        , [| dotExp intString natString expString |]
        ]

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

unpackPack : Property
unpackPack = property $ do
  bs <- forAll byteList
  bs === unpack (ByteString.pack bs)

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
--
-- prop_fastConcat : Property
-- prop_fastConcat = property $ do
--   bss <- forAll (list (linear 0 10) byteList)
--   ByteString.fastConcat (pack <$> bss) === pack (concat bss)

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

  the ByteString (fromString (substr (cast start) (cast len) str)) ===
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
  BS.mapMaybe Just (pack bs) === BS.pack bs

prop_mapMaybe : Property
prop_mapMaybe = property $ do
  bs <- forAll byteList
  footnote "pack bs = \{show $ BS.pack bs}"
  BS.mapMaybe fun (pack bs) === BS.pack (mapMaybe fun bs)

prop_filter : Property
prop_filter = property $ do
  bs <- forAll byteList
  BS.filter (< 100) (pack bs) === BS.pack (filter (< 100) bs)

prop_take : Property
prop_take = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), byteList]
  BS.take (cast n) (pack bs) === BS.pack (take n bs)

prop_takeEnd : Property
prop_takeEnd = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), bytestring]
  takeEnd n bs === reverse (take n $ reverse bs)

prop_drop : Property
prop_drop = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), byteList]
  BS.drop (cast n) (pack bs) === BS.pack (drop n bs)

prop_dropEnd : Property
prop_dropEnd = property $ do
  [n,bs] <- forAll $ np [nat (linear 0 30), bytestring]
  dropEnd n bs === reverse (drop n $ reverse bs)

prop_takeWhile : Property
prop_takeWhile = property $ do
  bs <- forAll byteList
  BS.takeWhile (< 100) (pack bs) ===
  BS.pack (takeWhile (< 100) bs)

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

prop_parseDecimalNat : Property
prop_parseDecimalNat = property $ do
  bits <- forAll natString
  BS.parseDecimalNat (BS.pack bits) === parsePositive (pack $ map cast bits)

prop_parseInteger : Property
prop_parseInteger = property $ do
  bits <- forAll intString
  BS.parseInteger (BS.pack bits) === String.parseInteger (pack $ map cast bits)

doubleEq : Maybe Double -> Maybe Double -> Bool
doubleEq Nothing  Nothing  = True
doubleEq (Just x) (Just y) =
  let div = max (abs x) (abs y)
   in div == 0.0 || abs ((x - y) / div) < 1.0e-14
doubleEq _        _        = False

prop_parseDouble : Property
prop_parseDouble = property $ do
  bits <- forAll dblString
  let str := Prelude.pack $ map cast bits
      mx  := BS.parseDouble (BS.pack bits)
      my  := String.parseDouble str
  footnote "string: \{str}"
  footnote "mx: \{show mx}"
  footnote "my: \{show my}"
  doubleEq mx my === True

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
--  , ("prop_fastConcat", prop_fastConcat)
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
  , ("prop_parseDecimalNat", prop_parseDecimalNat)
  , ("prop_parseInteger", prop_parseInteger)
  , ("prop_parseDouble", prop_parseDouble)
  ]
