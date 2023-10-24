module Data.Byte

%default total

||| ASCII code of '0'
public export %inline
byte_0 : Bits8
byte_0 = 48

||| ASCII code of '7'
public export %inline
byte_7 : Bits8
byte_7 = 55

||| ASCII code of '9'
public export %inline
byte_9 : Bits8
byte_9 = 57

||| ASCII code of 'a'
public export %inline
byte_a : Bits8
byte_a = 97

||| ASCII code of 'f'
public export %inline
byte_f : Bits8
byte_f = 102

||| ASCII code of 'z'
public export %inline
byte_z : Bits8
byte_z = 122

||| ASCII code of 'A'
public export %inline
byte_A : Bits8
byte_A = 65

||| ASCII code of 'Z'
public export %inline
byte_Z : Bits8
byte_Z = 90

public export
inRange : (lo,hi,scr : Bits8) -> (0 _ : (lo <= hi) === True) => Bool
inRange lo hi scr = case prim__gte_Bits8 scr lo of
  0 => False
  _ => case prim__lte_Bits8 scr hi of
    0 => False
    _ => True

public export %inline
isDigit : Bits8 -> Bool
isDigit x = inRange byte_0 byte_9 x

public export %inline
isLower : Bits8 -> Bool
isLower x = inRange byte_a byte_z x

public export %inline
isUpper : Bits8 -> Bool
isUpper x = inRange byte_A byte_Z x

public export
isAlpha : Bits8 -> Bool
isAlpha x = isLower x || isUpper x

public export
isAlphaNum : Bits8 -> Bool
isAlphaNum x = isDigit x || isAlpha x

||| Returns true if the byte represents an ASCII whitespace character.
public export
isSpace : Bits8 -> Bool
isSpace 32 = True -- ' '
isSpace 10 = True -- '\n'
isSpace  9 = True -- '\t'
isSpace 11 = True -- '\v'
isSpace 12 = True -- '\f'
isSpace 13 = True -- '\r'
isSpace _  = False

||| Returns true if the character represents a new line.
public export
isNL : Bits8 -> Bool
isNL 10 = True
isNL 13 = True
isNL _  = False

||| Convert a letter to the corresponding upper-case letter, if any.
||| Non-letters are ignored.
public export
toUpper : Bits8 -> Bits8
toUpper x = if (isLower x) then x - 32 else x

||| Convert a letter to the corresponding lower-case letter, if any.
||| Non-letters are ignored.
public export
toLower : Bits8 -> Bits8
toLower x = if (isUpper x) then x + 32 else x

||| Returns true if the character is a hexadecimal digit i.e. in the range
||| [0-9][a-f][A-F].
public export
isHexDigit : Bits8 -> Bool
isHexDigit x = isDigit x || inRange byte_a byte_f (toLower x)

||| Returns true if the character is an octal digit.
public export
isOctDigit : Bits8 -> Bool
isOctDigit x = inRange byte_0 byte_7 x

||| Returns true if the character is a control ASCII character.
public export
isControl : Bits8 -> Bool
isControl x = inRange 0 0x1f x

||| Returns true if the character equal the '.' ASCII character
public export
isDot : Bits8 -> Bool
isDot 46 = True
isDot _  = False

||| Returns true if the character equal the ',' ASCII character
public export
isComma : Bits8 -> Bool
isComma 44 = True
isComma _  = False

||| Try to convert a bit digit ('0' or '1') to
||| the natural number `0` or `1`.
public export
fromBitDigit : Bits8 -> Maybe Nat
fromBitDigit 48 = Just 0
fromBitDigit 49 = Just 1
fromBitDigit _  = Nothing

||| Try to convert an ocatal digit to
||| the corresponding natural number.
public export
fromOctDigit : Bits8 -> Maybe Nat
fromOctDigit 48 = Just 0
fromOctDigit 49 = Just 1
fromOctDigit 50 = Just 2
fromOctDigit 51 = Just 3
fromOctDigit 52 = Just 4
fromOctDigit 53 = Just 5
fromOctDigit 54 = Just 6
fromOctDigit 55 = Just 7
fromOctDigit _  = Nothing

||| Try to convert a decimal digit to
||| the corresponding natural number.
|||
||| Implementation note: Profiling showed that a direct
||| pattern match on the input is considerable faster
||| than using subtraction together with `isDigit`.
public export
fromDigit : Bits8 -> Maybe Nat
fromDigit 48 = Just 0
fromDigit 49 = Just 1
fromDigit 50 = Just 2
fromDigit 51 = Just 3
fromDigit 52 = Just 4
fromDigit 53 = Just 5
fromDigit 54 = Just 6
fromDigit 55 = Just 7
fromDigit 56 = Just 8
fromDigit 57 = Just 9
fromDigit _  = Nothing

||| Try to convert a hexadecimal digit to
||| the corresponding natural number.
public export
fromHexDigit : Bits8 -> Maybe Nat
fromHexDigit 48  = Just 0
fromHexDigit 49  = Just 1
fromHexDigit 50  = Just 2
fromHexDigit 51  = Just 3
fromHexDigit 52  = Just 4
fromHexDigit 53  = Just 5
fromHexDigit 54  = Just 6
fromHexDigit 55  = Just 7
fromHexDigit 56  = Just 8
fromHexDigit 57  = Just 9
fromHexDigit 97  = Just 10
fromHexDigit 98  = Just 11
fromHexDigit 99  = Just 12
fromHexDigit 100 = Just 13
fromHexDigit 101 = Just 14
fromHexDigit 102 = Just 15
fromHexDigit 65  = Just 10
fromHexDigit 66  = Just 11
fromHexDigit 67  = Just 12
fromHexDigit 68  = Just 13
fromHexDigit 69  = Just 14
fromHexDigit 70  = Just 15
fromHexDigit _   = Nothing
