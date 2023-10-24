module Data.Byte

%default total

||| ASCII code of '0'
public export %inline
byte_0 : Bits8
byte_0 = 48

||| ASCII code of '1'
public export %inline
byte_1 : Bits8
byte_1 = 49

||| ASCII code of '2'
public export %inline
byte_2 : Bits8
byte_2 = 50

||| ASCII code of '3'
public export %inline
byte_3 : Bits8
byte_3 = 51

||| ASCII code of '4'
public export %inline
byte_4 : Bits8
byte_4 = 52

||| ASCII code of '5'
public export %inline
byte_5 : Bits8
byte_5 = 53

||| ASCII code of '6'
public export %inline
byte_6 : Bits8
byte_6 = 54

||| ASCII code of '7'
public export %inline
byte_7 : Bits8
byte_7 = 55

||| ASCII code of '8'
public export %inline
byte_8 : Bits8
byte_8 = 56

||| ASCII code of '9'
public export %inline
byte_9 : Bits8
byte_9 = 57

||| ASCII code of 'a'
public export %inline
byte_a : Bits8
byte_a = 97

||| ASCII code of 'b'
public export %inline
byte_b : Bits8
byte_b = 98

||| ASCII code of 'c'
public export %inline
byte_c : Bits8
byte_c = 99

||| ASCII code of 'd'
public export %inline
byte_d : Bits8
byte_d = 100

||| ASCII code of 'e'
public export %inline
byte_e : Bits8
byte_e = 101

||| ASCII code of 'f'
public export %inline
byte_f : Bits8
byte_f = 102

||| ASCII code of 'g'
public export %inline
byte_g : Bits8
byte_g = 103

||| ASCII code of 'h'
public export %inline
byte_h : Bits8
byte_h = 104

||| ASCII code of 'i'
public export %inline
byte_i : Bits8
byte_i = 105

||| ASCII code of 'j'
public export %inline
byte_j : Bits8
byte_j = 106

||| ASCII code of 'k'
public export %inline
byte_k : Bits8
byte_k = 107

||| ASCII code of 'l'
public export %inline
byte_l : Bits8
byte_l = 108

||| ASCII code of 'm'
public export %inline
byte_m : Bits8
byte_m = 109

||| ASCII code of 'n'
public export %inline
byte_n : Bits8
byte_n = 110

||| ASCII code of 'o'
public export %inline
byte_o : Bits8
byte_o = 111

||| ASCII code of 'p'
public export %inline
byte_p : Bits8
byte_p = 112

||| ASCII code of 'q'
public export %inline
byte_q : Bits8
byte_q = 113

||| ASCII code of 'r'
public export %inline
byte_r : Bits8
byte_r = 114

||| ASCII code of 's'
public export %inline
byte_s : Bits8
byte_s = 115

||| ASCII code of 't'
public export %inline
byte_t : Bits8
byte_t = 116

||| ASCII code of 'u'
public export %inline
byte_u : Bits8
byte_u = 117

||| ASCII code of 'v'
public export %inline
byte_v : Bits8
byte_v = 118

||| ASCII code of 'w'
public export %inline
byte_w : Bits8
byte_w = 119

||| ASCII code of 'x'
public export %inline
byte_x : Bits8
byte_x = 120

||| ASCII code of 'y'
public export %inline
byte_y : Bits8
byte_y = 121

||| ASCII code of 'z'
public export %inline
byte_z : Bits8
byte_z = 122

||| ASCII code of 'A'
public export %inline
byte_A : Bits8
byte_A = 65

||| ASCII code of 'B'
public export %inline
byte_B : Bits8
byte_B = 66

||| ASCII code of 'C'
public export %inline
byte_C : Bits8
byte_C = 67

||| ASCII code of 'D'
public export %inline
byte_D : Bits8
byte_D = 68

||| ASCII code of 'E'
public export %inline
byte_E : Bits8
byte_E = 69

||| ASCII code of 'F'
public export %inline
byte_F : Bits8
byte_F = 70

||| ASCII code of 'G'
public export %inline
byte_G : Bits8
byte_G = 71

||| ASCII code of 'H'
public export %inline
byte_H : Bits8
byte_H = 72

||| ASCII code of 'I'
public export %inline
byte_I : Bits8
byte_I = 73

||| ASCII code of 'J'
public export %inline
byte_J : Bits8
byte_J = 74

||| ASCII code of 'K'
public export %inline
byte_K : Bits8
byte_K = 75

||| ASCII code of 'L'
public export %inline
byte_L : Bits8
byte_L = 76

||| ASCII code of 'M'
public export %inline
byte_M : Bits8
byte_M = 77

||| ASCII code of 'N'
public export %inline
byte_N : Bits8
byte_N = 78

||| ASCII code of 'O'
public export %inline
byte_O : Bits8
byte_O = 79

||| ASCII code of 'P'
public export %inline
byte_P : Bits8
byte_P = 80

||| ASCII code of 'Q'
public export %inline
byte_Q : Bits8
byte_Q = 81

||| ASCII code of 'R'
public export %inline
byte_R : Bits8
byte_R = 82

||| ASCII code of 'S'
public export %inline
byte_S : Bits8
byte_S = 83

||| ASCII code of 'T'
public export %inline
byte_T : Bits8
byte_T = 84

||| ASCII code of 'U'
public export %inline
byte_U : Bits8
byte_U = 85

||| ASCII code of 'V'
public export %inline
byte_V : Bits8
byte_V = 86

||| ASCII code of 'W'
public export %inline
byte_W : Bits8
byte_W = 87

||| ASCII code of 'X'
public export %inline
byte_X : Bits8
byte_X = 88

||| ASCII code of 'Y'
public export %inline
byte_Y : Bits8
byte_Y = 89

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
