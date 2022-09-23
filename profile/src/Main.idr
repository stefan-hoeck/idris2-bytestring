module Main

import Data.Buffer.Index
import Data.Buffer.Indexed
import Data.Nat.BSExtra
import Data.ByteString
import Data.ByteVect
import Data.Byte
import Data.List
import Data.List1
import Data.String
import Profile

toChar : Bits8 -> Char
toChar 10 = '\n'
toChar _  = 'a'

bs : (n : Nat) -> ByteVect (S n)
bs n = generate (S n) $ \case (Element x _) => if x == n then 10 else 0

bl : (n : Nat) -> List Bits8
bl n = unpack $ bs n

str : Nat -> String
str n = pack $ map toChar (bl n)

bs_lines : (n : Nat) -> ByteVect (S n)
bs_lines n =
  generate (S n) $ \ix =>
    case cast (fst ix) `mod` 100 of
      0 => 10
      _ => 0

list_lines : (n : Nat) -> List Bits8
list_lines n = unpack $ bs_lines n

string_lines : (n : Nat) -> String
string_lines n = pack $ map toChar (list_lines n)

bs_digits : (n : Nat) -> ByteVect (S n)
bs_digits n = generate (S n) $ \x => 48 + (cast (fst x) `mod` 10)

list_digits : (n : Nat) -> List Bits8
list_digits n = unpack $ bs_digits n

string_digits : (n : Nat) -> String
string_digits n = pack $ map cast (list_digits n)

bs_trim : (n : Nat) -> ByteString
bs_trim n = ByteString.fastConcat [the ByteString "   ", BS (S n) (bs_digits n), "   "]

list_trim : (n : Nat) -> List Bits8
list_trim n = unpack $ bs_trim n

string_trim : (n : Nat) -> String
string_trim n = pack $ map cast (list_trim n)

stringParseInt : String -> Maybe Integer
stringParseInt = parseInteger

find : Nat -> Benchmark Void
find n = Group "find \{show n}" [
    Single "BS.findIndex"     $ basic (findIndex (10 ==)) (bs  n)
  , Single "List.find"        $ basic (find (10 ==))      (bl  n)
  , Single "String.isInfixOf" $ basic (isInfixOf "\n")    (str n)
  ]

break : Nat -> Benchmark Void
break n = Group "break \{show n}" [
   Single "BS.break"     $ basic (break (10 ==))   (bs  n)
 , Single "List.break"   $ basic (break (10 ==))   (bl  n)
 , Single "String.break" $ basic (break ('\n' ==)) (str n)
 ]

lines : Nat -> Benchmark Void
lines n = Group "break \{show n}" [
   Single "BS.lines"     $ basic lines           (bs  n)
 , Single "List.split"   $ basic (split (10 ==)) (bl  n)
 , Single "String.lines" $ basic lines           (str n)
 ]

foldl : Nat -> Benchmark Void
foldl n = Group "parseNat \{show n}" [
   Single "parseInteger"   $ basic parseInteger (bs_digits n)
 , Single "stringParseInt" $ basic stringParseInt (string_digits n)
 ]

trim : Nat -> Benchmark Void
trim n = Group "parseNat \{show n}" [
   Single "bsTrim"     $ basic trim (bs_trim n)
 , Single "stringTrim" $ basic trim (string_trim n)
 ]

bench : Benchmark Void
bench = Group "bytestring" [
    find 50
  , find 5000
  , find 500000
  , break 50
  , break 5000
  , break 500000
  , lines 50
  , lines 5000
  , lines 500000
  , foldl 5
  , foldl 50
  , foldl 500
  , trim 5
  , trim 50
  , trim 500
  ]

main : IO ()
main = runDefault (const True) Table show bench
