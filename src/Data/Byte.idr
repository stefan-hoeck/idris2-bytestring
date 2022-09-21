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

||| ASCII code of 'a'
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
