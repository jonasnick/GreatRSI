import GreatRSI.Script
import GreatRSI.Winternitz
import GreatRSI.MerkleTree
import GreatRSI.Schnorr

def List.repeat {α : Type} (n: Nat) (x: List α): List α :=
  List.foldl (fun acc _ => acc ++ x) [] (List.range n)

namespace MerkleTree
/- Assumes Stack is a list of n = 2^m elements with the same length-/
def computeRoot (m : Nat) : List Op :=
  let n := 2 ^ m
  match m with
  | 0 => []
  | m' + 1 =>
    let n2 := n / 2
    let hash_pairs := [Op.CAT, Op.SHA256, Op.TOALTSTACK]
    let recover_layer := [Op.FROMALTSTACK]
    if m' == 0 then
      [Op.CAT, Op.SHA256]
    else
      hash_pairs.repeat n2 ++ recover_layer.repeat n2 ++ computeRoot m'

#guard (computeRoot 1).toString
  == "[OP_CAT, OP_SHA256]"
#guard (computeRoot 2).toString
  == "[OP_CAT, OP_SHA256, OP_TOALTSTACK, OP_CAT, OP_SHA256, OP_TOALTSTACK, \
       OP_FROMALTSTACK, OP_FROMALTSTACK, OP_CAT, OP_SHA256]"

def test (m: Nat): Bool :=
  let list: List StackElement := (List.range (2^m)).map (fun x => List.toByteArray [x.toUInt8])
  let stack: Stack := list.reverse
  match Script.run (computeRoot m) (ExecCtx.new stack zero) with
        | none => false
        | some ctx => ctx.stack == [MerkleTree.root list]

#guard test 1
#guard test 2
#guard test 3
#guard test 4
#guard test 5

end MerkleTree


namespace Covenant
-- This script fails if the top stack element is not equal to the Schnorr
-- challenge hash computed from the sighash. Leaves an empty stack.
-- NOTE: CHECKSIG assumes the following stack (top to bottom): `<pk> <R:s>`
def CHALHASH_VERIFY := [Op._1ADD,
                        Op.PUSH Schnorr.G,
                        Op.TUCK,
                        Op.SWAP,
                        Op.CAT,
                        Op.SWAP,
                        Op.CHECKSIGVERIFY]

namespace Test
#guard !Script.verify Covenant.CHALHASH_VERIFY [] zero
#guard !Script.verify Covenant.CHALHASH_VERIFY [[1].toByteArray] [1].toByteArray
def sighash := (List.replicate 32 0xab).toByteArray
def instack := [Schnorr.challenge_cat_trick sighash]
#guard Script.verify (Covenant.CHALHASH_VERIFY ++ [Op.PUSH one]) instack sighash
#guard !Script.verify (Covenant.CHALHASH_VERIFY ++ [Op.PUSH one]) instack (List.replicate 32 0xbb).toByteArray
end Test
end Covenant

namespace WinternitzBuilder

-- before: stack: `<message>`
-- after: altstack: `<reverse message digits>`
def base16 (n: Nat): Script :=
  assert! n < 2^8
  (List.replicate n
    [Op.DUP, Op.PUSH [1].toByteArray, Op.RIGHT, Op.SWAP,
    Op.PUSH [1].toByteArray, Op.LEFT, Op.DUP,
    Op.PUSH [4].toByteArray, Op.DOWNSHIFT, Op.TOALTSTACK,
    Op.PUSH [0x0f].toByteArray, Op.AND, Op.TOALTSTACK]).join
  ++ [Op.DROP]

def M := ((List.range 32).map (fun x => x.toUInt8)).toByteArray

def sighash := (List.replicate 32 0xab).toByteArray
def instack := [[0x12, 0x34].toByteArray]
def expected_altstack := [[4], [3], [2], [1]].map (fun x => x.toByteArray)
#guard Script.run (base16 instack[0].size) (ExecCtx.new instack [].toByteArray)
        == some { sighash := [].toByteArray, stack := [], altstack := expected_altstack, vfExec := [] }
def t := match (Script.run (base16 32) (ExecCtx.new [M] sighash)) with
  | none => false
  | some ctx => ctx.altstack == (Winternitz.base16 M).reverse.map (fun x => [x].toByteArray)
#guard t

-- before: altstack: `<reverse message digits>`
-- after: stack `<checksum digits> <message digits>`
def checksum (n: Nat): Script :=
  let n_digits := 2*n
  let len_2 := if n == 32 then 3 else 2
  [Op.PUSH (15 * n_digits).toByteArray]
  ++ (List.replicate n_digits [Op.FROMALTSTACK, Op.TUCK, Op.SUB]).join
  ++ (base16 2)
  ++ (List.replicate len_2 Op.FROMALTSTACK)
  ++ [Op.FROMALTSTACK, Op.DROP]

def M16 := Winternitz.base16 M
def C16 := Winternitz.checksum M16
-- #eval (Script.run ((base16 32) ++ (checksum 32)) (ExecCtx.new [M] sighash))
def t2 := match (Script.run ((base16 32) ++ (checksum 32)) (ExecCtx.new [M] sighash)) with
  | none => false
  | some ctx => ctx.stack == (C16 ++ M16).map (fun x => [x].toByteArray)
#guard t2

-- stack: `<digit1> <preimage1> <seed> <randomizers> ...`
def chain: Script :=
  ((List.range 15).reverse.map (fun i =>
  [Op.DUP, Op.NOT, Op.IF,
  -- `<digit> <preimage> <seed>`
  Op.SWAP,
  -- `<preimage> <digit> <seed>`
  Op.PUSH [2].toByteArray, Op.PICK,
  -- `<seed> <preimage> <digit> <seed>`
  Op.SWAP,
  -- `<preimage> <seed> <digit> <seed> <randomizer_0> ...`
  Op.PUSH (i + 4).toByteArray,
  Op.PICK,
  Op.XOR,
  -- `<preimage_xored> <seed> <digit> <seed>`
  Op.CAT,
  -- `<seed++preimage_xored> <digit> <seed>`
  Op.SHA256,
  -- `<hash> <digit> <seed>`
  Op.SWAP,
  -- `<digit> <hash> <seed>`
  Op.ELSE, Op._1SUB, Op.ENDIF]
  )).join
  ++ [Op.DROP]
  ++ [Op.TOALTSTACK]

def CHECKWOTS (pk: Winternitz.Pubkey): Script :=
  -- check that the top stack element is sighash (or more precisely, the challenge hash)
  [Op.DUP] ++ Covenant.CHALHASH_VERIFY
  ++ base16 Winternitz.n
  ++ checksum Winternitz.n
  ++ pk.randomization.reverse.foldl (fun acc x => acc ++ [Op.PUSH x]) []
  ++ [Op.PUSH pk.seed]
  -- stack: `<seed> <randomizer_0> ... <randomizer_14> <digit_0> <digit1>... <digit_66> <preimage0> ... <preimage65>`
  ++ ((List.range Winternitz.len).map (fun i =>
      -- obtain preimage
      [Op.PUSH [(15 + 1 + (Winternitz.len - i)).toUInt8].toByteArray, Op.ROLL,
      -- obtain digit
      Op.PUSH [15 + 1 + 1].toByteArray, Op.ROLL]
      -- checksum digits are higher on the stack than message digits
      ++ chain
      )).join
  ++ List.replicate (15 + 1) Op.DROP
  -- altstack `<pk.hashes[63]> ... <pk.hashes[0]> <pk.hashes[66]> ... <pk.hashes[64]>
  ++ List.replicate Winternitz.len Op.FROMALTSTACK
  -- stack `<pk.hashes[64]> ... <pk.hashes[66]> <pk.hashes[0]> ... <pk.hashes[63]>
  ++ List.replicate (Winternitz.len - 1) Op.CAT
  -- stack `<pk.hashes[63] || ... || pk.hashes[0] || pk.hashes[66] || ... || pk.hashes[64]>`
  ++ [Op.SHA256]
  ++ [Op.PUSH (sha256 (flatten ((List.range Winternitz.len).map (fun i =>
        if i < 64 then pk.hashes[63 - i]!
        else pk.hashes[66 + 64 - i]!
        ))))]
  ++ [Op.EQUALVERIFY]
  ++ [Op.PUSH [1].toByteArray]

-- `<M> <sig[64]> ... <sig[66]> <sig[0]> ... <sig[63]>`
def witnessStack (M: ByteArray) (sig: List ByteArray): Stack :=
  assert! M.size == 32
  assert! sig.length == Winternitz.len
  let l := [M] ++ [sig[64]!, sig[65]!, sig[66]!] ++ (sig.take 64)
  l

namespace Test
namespace one
def sighash := Winternitz.Test.one.M
def M := Schnorr.challenge_cat_trick sighash
def sig := Winternitz.sign M Winternitz.Test.one.sk Winternitz.Test.one.randomization Winternitz.Test.one.seed
#guard Script.verify (CHECKWOTS Winternitz.Test.one.pk)
                    (witnessStack M sig)
                    sighash
end one
namespace two
def sighash := Winternitz.Test.two.M
def M := Schnorr.challenge_cat_trick sighash
def sig := Winternitz.sign M Winternitz.Test.two.sk Winternitz.Test.two.randomization Winternitz.Test.two.seed
#guard Script.verify (CHECKWOTS Winternitz.Test.two.pk)
                    (witnessStack M sig)
                    sighash

end two
end Test

end WinternitzBuilder
