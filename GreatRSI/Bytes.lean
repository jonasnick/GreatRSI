import Std

open Std

def zero := List.toByteArray [0]
def one := List.toByteArray [1]

instance : BEq ByteArray where
  beq a b := a.data == b.data

def flatten (l: List ByteArray): ByteArray :=
  l.foldl (fun acc l' => acc ++ l') ByteArray.empty

def ByteArray.xor (b1: ByteArray) (b2: ByteArray): ByteArray :=
  let b := b1.data.zip b2.data
  { data := b.map (fun b => b.1 ^^^ b.2)}

-- little endian
def ByteArray.toNat (ele: ByteArray) : Nat :=
  let e := ele.toList
  List.foldl (fun acc (b: UInt8) => 256*acc + b.toNat) (0: Nat) e

#guard zero.toNat == 0
#guard one.toNat == 1
#guard ByteArray.toNat (List.toByteArray [0, 0]) == 0
#guard ByteArray.toNat (List.toByteArray [1, 0]) == 256
#guard ByteArray.toNat (List.toByteArray [0, 1]) == 1
#guard ByteArray.toNat (List.toByteArray [1, 1]) == 257

-- little endian
partial def Nat.toByteArray (n: Nat) : ByteArray :=
  let rec go (num : Nat) (acc : ByteArray) : ByteArray :=
    if num == 0 then acc
    else go (num / 256) (ByteArray.push acc ((num % 256).toUInt8 : UInt8))
  if n == 0 then List.toByteArray [0]
  else
    -- TODO
    (go n ByteArray.empty).toList.reverse.toByteArray

#guard one.data == (Nat.toByteArray 1).data
#guard one.data == (Nat.toByteArray 1).data

#guard (Nat.toByteArray 0) == zero
#guard (Nat.toByteArray 1) == one
#guard (Nat.toByteArray 2) == (List.toByteArray [2])
#guard (Nat.toByteArray 255) == (List.toByteArray [255])
#guard (Nat.toByteArray 256) == (List.toByteArray [1, 0])
#guard (Nat.toByteArray 257) == (List.toByteArray [1, 1])


def ByteArray.toNatBE (ele: ByteArray) : Nat :=
  let e := ele.toList
  List.foldr (fun (b: UInt8) acc => b.toNat + 256*acc) (0: Nat) e

#guard zero.toNatBE == 0
#guard one.toNatBE == 1
#guard ByteArray.toNatBE (List.toByteArray [0, 0]) == 0
#guard ByteArray.toNatBE (List.toByteArray [1, 0]) == 1
#guard ByteArray.toNatBE (List.toByteArray [0, 1]) == 256
#guard ByteArray.toNatBE (List.toByteArray [1, 1]) == 257

-- Helper function to convert a single hexadecimal digit character to its integer value
def hexDigitToNat (c : Char) : Option Nat :=
  let n := c.toNat
  if '0' ≤ c ∧ c ≤ '9' then
    some (n - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (n - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (n - 'A'.toNat + 10)
  else
    none

-- Helper function to convert a number between 0 and 15 to its corresponding hex character
def digitToChar (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat (n + '0'.toNat)
  else
    Char.ofNat (n - 10 + 'a'.toNat)

-- Function to convert a byte to a two-character hexadecimal string
def byteToHex (b : UInt8) : String :=
  let highNibble := (b.toNat >>> 4) &&& 0xF
  let lowNibble := b.toNat &&& 0xF
  let highChar := digitToChar highNibble
  let lowChar := digitToChar lowNibble
  String.mk [highChar, lowChar]

-- Function to convert ByteArray to hex string
def ByteArray.toHex (ba : ByteArray) : String :=
  ba.data.foldl (fun acc b => acc ++ byteToHex b) ""

#guard (List.toByteArray [0x6a, 0x09, 0xe6, 0x67]).toHex == "6a09e667"

instance : Repr ByteArray where
  reprPrec ba _ := "0x" ++ ba.toHex

-- Function to convert a hexadecimal string to a ByteArray
def fromHex (hexStr : String) : Option ByteArray :=
  if hexStr.length % 2 ≠ 0 then
    none -- Hex string must have even length
  else
    let chars := hexStr.toList
    let rec loop (chars : List Char) (acc : ByteArray) : Option ByteArray :=
      match chars with
      | c1 :: c2 :: rest =>
        match hexDigitToNat c1, hexDigitToNat c2 with
        | some n1, some n2 =>
          let byteVal := UInt8.ofNat ((n1 <<< 4) + n2)
          loop rest (acc.push byteVal)
        | _, _ => none -- Invalid hex digit
      | [] => some acc
      | _ => none -- Should not happen due to even length check
    loop chars ByteArray.empty

instance : BEq ByteArray where
  beq a b := a.data == b.data

#guard (fromHex (List.toByteArray [0xab, 0x09, 0x00, 0xff]).toHex) == some (List.toByteArray [0xab, 0x09, 0x00, 0xff])
