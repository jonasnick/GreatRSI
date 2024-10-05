import GreatRSI.Bytes
import GreatRSI.SHA256
import GreatRSI.Schnorr

 inductive Op
| PUSH(a: ByteArray)
| IF
| ELSE
| ENDIF
| TOALTSTACK
| FROMALTSTACK
| DROP
| DUP
| PICK
| ROLL
| SWAP
| TUCK
| CAT
| LEFT
| RIGHT
| AND
| XOR
| EQUAL
| EQUALVERIFY
| _1ADD -- identifiers are not allowed to start with a numerical character
| _1SUB
| NOT
| _0NOTEQUAL
| ADD
| SUB
| DOWNSHIFT
| GREATERTHAN
| SHA256
| CHECKSIGVERIFY
deriving BEq

-- Implement the ToString instance to get the opcode names
instance : ToString Op where
  toString op := match op with
    | Op.PUSH a => "OP_PUSH(" ++ a.toHex ++ ")"
    | Op.IF => "OP_IF"
    | Op.ELSE => "OP_ELSE"
    | Op.ENDIF => "OP_ENDIF"
    | Op.TOALTSTACK => "OP_TOALTSTACK"
    | Op.FROMALTSTACK => "OP_FROMALTSTACK"
    | Op.DROP => "OP_DROP"
    | Op.DUP => "OP_DUP"
    | Op.PICK => "OP_PICK"
    | Op.ROLL => "OP_ROLL"
    | Op.SWAP => "OP_SWAP"
    | Op.TUCK => "OP_TUCK"
    | Op.CAT => "OP_CAT"
    | Op.LEFT => "OP_LEFT"
    | Op.RIGHT => "OP_RIGHT"
    | Op.AND => "OP_AND"
    | Op.XOR => "OP_XOR"
    | Op.EQUAL => "OP_EQUAL"
    | Op.EQUALVERIFY => "OP_EQUALVERIFY"
    | Op._1ADD => "OP_1ADD"
    | Op._1SUB => "OP_1SUB"
    | Op.NOT => "OP_NOT"
    | Op._0NOTEQUAL => "OP_0NOTEQUAL"
    | Op.ADD => "OP_ADD"
    | Op.SUB => "OP_SUB"
    | Op.DOWNSHIFT => "OP_DOWNSHIFT"
    | Op.GREATERTHAN => "OP_GREATERTHAN"
    | Op.SHA256 => "OP_SHA256"
    | Op.CHECKSIGVERIFY => "OP_CHECKSIGVERFIY"


def Op.toUInt8 : Op → List UInt8
  | Op.PUSH a =>
    assert! a.size <= 75
    [a.size.toUInt8] ++ a.toList
  | Op.IF => [0x63]
  | Op.ELSE => [0x67]
  | Op.ENDIF => [0x68]
  | Op.TOALTSTACK   => [0x6b]
  | Op.FROMALTSTACK => [0x6c]
  | Op.DROP => [0x75]
  | Op.DUP => [0x76]
  | Op.PICK => [0x79]
  | Op.ROLL => [0x7a]
  | Op.SWAP => [0x7c]
  | Op.TUCK => [0x7d]
  | Op.CAT => [0x7e]
  | Op.LEFT => [0x80]
  | Op.RIGHT => [0x81]
  | Op.AND => [0x84]
  | Op.XOR => [0x86]
  | Op.EQUAL => [0x87]
  | Op.EQUALVERIFY => [0x88]
  | Op._1ADD => [0x8b]
  | Op._1SUB => [0x8c]
  | Op.NOT => [0x91]
  | Op._0NOTEQUAL => [0x92]
  | Op.ADD => [0x93]
  | Op.SUB => [0x94]
  | Op.DOWNSHIFT => [0x99]
  | Op.GREATERTHAN => [0xa0]
  | Op.SHA256 => [0xa8]
  | Op.CHECKSIGVERIFY => [0xad]

def Op.fromUInt8 (bytes: List UInt8): Option (Op × List UInt8) :=
  match bytes with
  | [] => none
  | b :: bs => match b with
    | 0x63 => some (Op.IF, bs)
    | 0x67 => some (Op.ELSE, bs)
    | 0x68 => some (Op.ENDIF, bs)
    | 0x6b => some (Op.TOALTSTACK, bs)
    | 0x6c => some (Op.FROMALTSTACK, bs)
    | 0x75 => some (Op.DROP, bs)
    | 0x76 => some (Op.DUP, bs)
    | 0x79 => some (Op.PICK, bs)
    | 0x7a => some (Op.ROLL, bs)
    | 0x7c => some (Op.SWAP, bs)
    | 0x7d => some (Op.TUCK, bs)
    | 0x7e => some (Op.CAT, bs)
    | 0x80 => some (Op.LEFT, bs)
    | 0x81 => some (Op.RIGHT, bs)
    | 0x84 => some (Op.AND, bs)
    | 0x86 => some (Op.XOR, bs)
    | 0x87 => some (Op.EQUAL, bs)
    | 0x88 => some (Op.EQUALVERIFY, bs)
    | 0x8b => some (Op._1ADD, bs)
    | 0x8c => some (Op._1SUB, bs)
    | 0x91 => some (Op.NOT, bs)
    | 0x92 => some (Op._0NOTEQUAL, bs)
    | 0x93 => some (Op.ADD, bs)
    | 0x94 => some (Op.SUB, bs)
    | 0x99 => some (Op.DOWNSHIFT, bs)
    | 0xa0 => some (Op.GREATERTHAN, bs)
    | 0xa8 => some (Op.SHA256, bs)
    | 0xad => some (Op.CHECKSIGVERIFY, bs)
    | size =>
      if size <= 75 && bs.length >= size.toNat then
        some (Op.PUSH (bs.take size.toNat).toByteArray, bs.drop size.toNat)
      else
        none

#guard Op.fromUInt8 [0x63] == some (Op.IF, [])
#guard Op.fromUInt8 [1, 1, 2] == some (Op.PUSH [1].toByteArray, [2])
#guard Op.fromUInt8 [76] == none

/- StackElement -/
abbrev StackElement: Type := ByteArray

/- Stack -/
abbrev Stack: Type := List StackElement

instance : Repr Stack where
  reprPrec s _ := s.toString

def Stack.serialize (s: Stack): ByteArray :=
  assert! s.length <= 252
  (s.foldl (fun acc e =>
    assert! e.size <= 252
    acc ++ [e.size.toUInt8] ++ e.toList) [s.length.toUInt8]).toByteArray

partial def Stack.parse (bytes: ByteArray): Option Stack :=
  let bytes := bytes.toList
  match bytes with
  | [] => none
  | length :: rest =>
    let length := length.toNat
    if length > 252 then none else
      let rec parseElements (remaining: List UInt8) (count: Nat): Option (List StackElement) :=
        if count == 0 then some []
        else match remaining with
          | [] => none
          | size :: rest =>
            let size := size.toNat
            if size > 252 || rest.length < size then none
            else
              let (element, rest) := rest.splitAt size
              match parseElements rest (count - 1) with
              | none => none
              | some elements => some (element.toByteArray :: elements)
      parseElements rest length

#guard Stack.parse (Stack.serialize []) == some []
#guard Stack.parse (Stack.serialize [zero]) == some [zero]
#guard Stack.parse (Stack.serialize [[1, 2].toByteArray, zero, one]) == some [[1, 2].toByteArray, zero, one]

def Stack.popraw (s: Stack) : Stack × StackElement :=
  match s with
  | [] => panic! "Cannot pop from an empty stack"
  | y :: ys => (ys, y)

def Stack.pop (s: Stack): Option (Stack × StackElement):=
  if s.length < 1 then
    none
  else
    let (s', a) := Stack.popraw s
    some (s', a)

def Stack.poptwo (s: Stack): Option (Stack × StackElement × StackElement):=
  if s.length < 2 then
    none
  else
    let (s', a) := Stack.popraw s
    let (s'', b) := Stack.popraw s'
    some (s'', a, b)


def Stack.push (s: Stack) (e: StackElement) : Stack :=
  List.cons e s

#guard Stack.push [] zero == [zero]
#guard Stack.push [one, zero] zero == [zero, one, zero]
#guard Stack.pop [one, zero] == ([zero], one)

def uint8_add (a: UInt8) (b: UInt8): UInt8 × UInt8 :=
  let c := a.toNat + b.toNat
  ((c % 256).toUInt8, if c >= 256 then (c - 255).toUInt8 else 0)

/- CHECKSIG -/

def CheckSchnorrSignature (sig: ByteArray) (pk: ByteArray) (sighash: ByteArray): Bool :=
  -- TODO: support 65 byte sigs
  if sig.size != 64 then false else
    Schnorr.verify_dummy pk sighash sig

def EvalChecksigTapscript (sig: ByteArray) (pk: ByteArray) (sighash: ByteArray): Bool :=
  -- TODO: missing weight check
  if pk.size == 0 then false else
    if pk.size == 32 && sig.size != 0 then CheckSchnorrSignature sig pk sighash else
      if sig.size == 0 then false else
      true

-- Execution Context
structure ExecCtx where
  sighash : ByteArray
  stack : Stack
  altstack : Stack
  vfExec : List Bool -- controls conditionals
deriving BEq, Repr


def ExecCtx.new (stack: Stack) (sighash: ByteArray): ExecCtx :=
  { sighash := sighash,
    stack := stack,
    altstack := [],
    vfExec := [] }

def ExecCtx.updateStacks (ctx: ExecCtx) (stack: Stack) (altstack: Stack): ExecCtx :=
  { sighash := ctx.sighash
    stack := stack,
    altstack := altstack,
    vfExec := ctx.vfExec }

def ExecCtx.matchOpcode (ctx: ExecCtx) (op: Op) : Option ExecCtx :=
  match op with
  | Op.PUSH a =>
      some (ctx.updateStacks (ctx.stack.push a) ctx.altstack)
  | Op.IF =>
    match Stack.pop ctx.stack with
    | none => none
    | some (stack, e) =>
      if e != [1].toByteArray && e != [].toByteArray then
        none
      else
        some
        { sighash := ctx.sighash,
          stack := stack,
          altstack := ctx.altstack,
          vfExec := [(e == [1].toByteArray)] ++ ctx.vfExec}
  | Op.ELSE =>
    match ctx.vfExec with
    | [] => none
    | y :: ys =>
      some { sighash := ctx.sighash,
             stack := ctx.stack,
             altstack := ctx.altstack,
             vfExec := (!y) :: ys }
  | Op.ENDIF =>
    match ctx.vfExec with
    | [] => none
    | _ :: ys =>
      some { sighash := ctx.sighash,
             stack := ctx.stack,
             altstack := ctx.altstack,
             vfExec := ys }
  | Op.TOALTSTACK =>
    (Stack.pop ctx.stack).map (fun (stack, e) =>
      let altstack := ctx.altstack.push e
      ctx.updateStacks stack altstack)
  | Op.FROMALTSTACK =>
    (Stack.pop ctx.altstack).map (fun (altstack, e) =>
      let stack := ctx.stack.push e
      ctx.updateStacks stack altstack)
  | Op.DROP =>
    (Stack.pop ctx.stack).map (fun (stack, _) =>
      ctx.updateStacks stack ctx.altstack)
  | Op.DUP =>
    (Stack.pop ctx.stack).map (fun (stack, e) =>
      let stack' := (stack.push e).push e
      ctx.updateStacks stack' ctx.altstack)
  | Op.PICK =>
    match (Stack.pop ctx.stack) with
    | none => none
    | some (stack, e) =>
      let e' := e.toNat
      if stack.length < e' + 1 then none
      else
        let stack' := stack.drop e'
        let stack'' := (stack'.take 1) ++ (stack.take e') ++ stack'
        some (ctx.updateStacks stack'' ctx.altstack)
  | Op.ROLL =>
    match (Stack.pop ctx.stack) with
    | none => none
    | some (stack, e) =>
      let e' := e.toNat
      if stack.length < e' + 1 then none
      else
        let stack' := stack.drop e'
        let stack'' := (stack'.take 1) ++ (stack.take e') ++ (stack'.drop 1)
        some (ctx.updateStacks stack'' ctx.altstack)
  | Op.SWAP =>
    (Stack.poptwo ctx.stack).map (fun (stack, a, b) =>
      let stack' := (stack.push a).push b
      ctx.updateStacks stack' ctx.altstack)
  | Op.TUCK =>
    (Stack.poptwo ctx.stack).map (fun (stack, a, b) =>
      let stack' := ((stack.push a).push b).push a
      ctx.updateStacks stack' ctx.altstack)
  | Op.CAT =>
    (Stack.poptwo ctx.stack).map (fun (stack, b, a) =>
      let stack' := stack.push (ByteArray.append a b)
      ctx.updateStacks stack' ctx.altstack)
  | Op.LEFT =>
    (Stack.poptwo ctx.stack).map (fun (stack, offset, a) =>
      let stack' := stack.push (List.take offset.toNat a.toList).toByteArray
      ctx.updateStacks stack' ctx.altstack)
  | Op.RIGHT =>
    (Stack.poptwo ctx.stack).map (fun (stack, offset, a) =>
      let stack' := stack.push (List.drop offset.toNat a.toList).toByteArray
      ctx.updateStacks stack' ctx.altstack)
  | Op.AND =>
    (Stack.poptwo ctx.stack).map (fun (stack, a, b) =>
      let zipped := a.toList.zip b.toList
      let trailing := if a.size > b.size then a.size - b.size else b.size - a.size
      let res := (zipped.map fun (a, b) => a &&& b).toByteArray
                  ++ (List.replicate trailing 0).toByteArray
      ctx.updateStacks (stack.push res) ctx.altstack)
  | Op.XOR =>
    (Stack.poptwo ctx.stack).map (fun (stack, b, a) =>
      let zipped := a.toList.zip b.toList
      let trailing := if a.size > b.size then (a.toList.drop b.size) else (b.toList.drop a.size)
      let res := (zipped.map fun (a, b) => a ^^^ b).toByteArray
                  ++ trailing.toByteArray
      ctx.updateStacks (stack.push res) ctx.altstack)
  | Op.EQUAL =>
    -- TODO: should this compare bytes?
    (Stack.poptwo ctx.stack).map (fun (stack, a, b) =>
      let stack' := stack.push (if a.toNatBE == b.toNatBE then one else zero)
      ctx.updateStacks stack' ctx.altstack)
  | Op.EQUALVERIFY =>
    match Stack.poptwo ctx.stack with
    | none => none
    | some (stack, a, b) =>
      if a.toNatBE == b.toNatBE
      then some (ctx.updateStacks stack ctx.altstack)
      else none
  | Op._1ADD =>
    (Stack.pop ctx.stack).map (fun (stack, a) =>
      let stack' := stack.push ((a.toNat + 1).toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op._1SUB =>
    match (Stack.pop ctx.stack) with
    | none => none
    | some (stack, a) =>
      if a.toNat >= 1 then
        let stack' := stack.push ((a.toNat - 1).toByteArray)
        some (ctx.updateStacks stack' ctx.altstack)
      else none
  | Op.NOT =>
    (Stack.pop ctx.stack).map (fun (stack, a) =>
      let stack' := stack.push (if (a.toNat == 0) then [1].toByteArray else [].toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op._0NOTEQUAL =>
    (Stack.pop ctx.stack).map (fun (stack, a) =>
      let stack' := stack.push (if (a.toNat != 0) then [1].toByteArray else [].toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op.ADD =>
    (Stack.poptwo ctx.stack).map (fun (stack, b, a) =>
      let stack' := stack.push ((a.toNat + b.toNat).toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op.SUB =>
    match (Stack.poptwo ctx.stack) with
    | none => none
    | some (stack, b, a) =>
      if a.toNat >= b.toNat then
        let stack' := stack.push ((a.toNat - b.toNat).toByteArray)
        some (ctx.updateStacks stack' ctx.altstack)
      else none
  | Op.DOWNSHIFT =>
    (Stack.poptwo ctx.stack).map (fun (stack, bits, a) =>
      -- TODO: I have no idea if this matches the GSR spec
      let stack' := stack.push ((a.toNat >>> bits.toNat).toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op.GREATERTHAN =>
    (Stack.poptwo ctx.stack).map (fun (stack, b, a) =>
      let stack' := stack.push (if a.toNat > b.toNat then [1].toByteArray else [].toByteArray)
      ctx.updateStacks stack' ctx.altstack)
  | Op.SHA256 =>
    (Stack.pop ctx.stack).map (fun (stack, a) =>
      let stack' := stack.push (sha256 a)
      ctx.updateStacks stack' ctx.altstack)
  | Op.CHECKSIGVERIFY =>
    match Stack.poptwo ctx.stack with
    | none => none
    | some (stack, pk, sig) =>
      if EvalChecksigTapscript sig pk ctx.sighash
        then some (ctx.updateStacks stack ctx.altstack)
        else none

def ExecCtx.transition (ctx: ExecCtx) (op: Op) : Option ExecCtx :=
  -- If we're not in a branch or we're in a branch that we're supposed to
  -- execute then execute the op code. Otherwise, no op.
  match ctx.vfExec with
    | [] => ExecCtx.matchOpcode ctx op
    | y :: _ => if y == true || op == Op.ELSE || op == Op.ENDIF
                then ExecCtx.matchOpcode ctx op
                else some ctx

#guard (ExecCtx.new [zero, zero] zero).transition Op.CAT == some (ExecCtx.new [List.toByteArray [0, 0]] zero)
#guard (ExecCtx.new [zero] zero).transition Op.EQUAL == none
#guard (ExecCtx.new [zero, zero] zero).transition Op.EQUAL == some (ExecCtx.new [one] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.EQUAL == some (ExecCtx.new [zero] zero)
#guard (ExecCtx.new [zero] zero).transition Op.DUP == some (ExecCtx.new [zero, zero] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.SWAP == some (ExecCtx.new [one, zero] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.ADD == some (ExecCtx.new [one] zero)
#guard (ExecCtx.new [one] zero).transition Op._1ADD == some (ExecCtx.new [[2].toByteArray] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.LEFT == some (ExecCtx.new [[].toByteArray] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.AND == some (ExecCtx.new [zero] zero)
#guard (ExecCtx.new [one.append one, one] zero).transition Op.AND == some (ExecCtx.new [one.append zero] zero)
#guard (ExecCtx.new [zero, one] zero).transition Op.DOWNSHIFT == some (ExecCtx.new [one] zero)
#guard (ExecCtx.new [one, one] zero).transition Op.DOWNSHIFT == some (ExecCtx.new [zero] zero)
#guard (ExecCtx.new [zero] zero).transition Op.IF == none
#guard (ExecCtx.new [one, zero, one, [2].toByteArray] zero).transition Op.PICK
        == some (ExecCtx.new [one, zero, one, [2].toByteArray] zero)
#guard (ExecCtx.new [one, zero, one, [2].toByteArray] zero).transition Op.ROLL
        == some (ExecCtx.new [one, zero, [2].toByteArray] zero)



/- Script -/
abbrev Script: Type := List Op

def Script.serialize (script: Script): ByteArray :=
  (script.foldl (fun acc op => acc ++ op.toUInt8) []).toByteArray

partial def parseScript (bytes: List UInt8): Option Script :=
  match Op.fromUInt8 bytes with
  | none => none
  | some (op, rest) =>
    match rest with
    | [] => some [op]
    | _ :: _ =>
      let parsed_rest := parseScript rest
      match parsed_rest with
      | none => none
      | some parsed_rest => some (op :: parsed_rest)

namespace ScriptTest
def script: Script := [Op.IF, Op.DROP,  Op.ELSE, Op.PUSH [1].toByteArray, Op.ENDIF]
#guard parseScript (script.serialize.toList) == some script
end ScriptTest

def MAX_STACK_SIZE := 1000

def Script.run (tapscript: Script) (ctx: ExecCtx) : Option ExecCtx :=
  match tapscript with
  | [] => some ctx
  | op :: ops =>
    let ctx' := ctx.transition op
    match ctx' with
    | none => none
    | some ctx' =>
      if (ctx'.stack.length + ctx'.altstack.length > MAX_STACK_SIZE)
        then none
        else Script.run ops ctx'

-- TODO: does not take negative 0 into account as hinted at by BIP GSR
def ByteArray.CastToBool (ele: ByteArray) : Bool :=
  let e := ele.toList
  e.foldl (fun (acc : Bool) b => (acc || (b != 0))) false


def Script.verify (tapscript: Script) (instack: Stack) (sighash: ByteArray): Bool :=
  let ctx := ExecCtx.new instack sighash
  match Script.run tapscript ctx with
  | none => false
  | some ctx' => match ctx'.stack with
    | y :: [] => y.CastToBool && ctx.vfExec.length == 0
    | _ => false

#guard Script.verify [] [] zero == false
#guard Script.verify [Op.CAT] [zero] zero == false
#guard Script.verify [Op.CAT] [zero, zero] zero == false
#guard Script.verify [Op.CAT] [zero, one] zero
#guard Script.verify [Op.CAT] [zero, one, zero] zero == false
#guard Script.verify [Op.IF, Op.DROP, Op.DROP, Op.DROP, Op.ENDIF] [[].toByteArray, one] zero == true
#guard Script.verify [Op.IF, Op.DROP, Op.DROP, Op.DROP, Op.ENDIF, Op.IF, Op.PUSH [1].toByteArray, Op.ENDIF] [[].toByteArray, one] zero == true
#guard Script.verify [Op.IF, Op.PUSH [1].toByteArray, Op.ELSE, Op.DROP, Op.ENDIF] [one] zero == true
#guard Script.verify [Op.IF, Op.DROP,  Op.ELSE, Op.PUSH [1].toByteArray, Op.ENDIF] [[].toByteArray] zero == true
