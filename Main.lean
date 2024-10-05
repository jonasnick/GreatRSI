import GreatRSI.Script
import GreatRSI.ScriptBuilder
import GreatRSI.Winternitz
import GreatRSI.Bytes

def helpMessage : String :=
  "Usage: wots <command> [args]\n\nCommands:\n  seckeygen <outfile> - Draws a Winternitz secret key uniformly at random, writes secret key to file.\n  scriptgen <infile> <outfile> - Creates a Winternitz public key from the secret key in the input file, and writes the corresopnding Bitcoin Script (GRS) to the output file.\n  scriptparse <infile> - Outputs the parsed script in the infile.\n  witnessgen <infile> <sighash> <outfile> - Reads the seckey from the input file, computes the Winternitz signature of the sighash, creates the witness and writes it to the output file.\n  verify <scriptfile> <sighash> <witnessfile> - Executes the script with the given witness and sighash."

-- secfile = seed || randomizer || seckey
def readSecfile (filename: String): IO (ByteArray × List ByteArray × Winternitz.Seckey) := do
  let secfile ← IO.FS.Handle.mk filename IO.FS.Mode.read
  let secbytes ← secfile.readBinToEnd
  let seed := secbytes.extract 0 32
  let randomizer := (List.range 15).map (fun i =>
    let offset := (i+1)*32
    (secbytes.extract offset (offset+32)))
  let seckeyOffset := (1 + 15)*32
  let seckeyBytes := secbytes.extract seckeyOffset (seckeyOffset + (67*32))
  let seckey := Winternitz.ByteArray.parseSeckey seckeyBytes
  return (seed, randomizer, seckey)

def main (args: List String): IO Unit := do
  if h : 0 < args.length then
    let cmd := args[0]'h
    match cmd with
    | "seckeygen" =>
      if h : 1 < args.length then
        let filename := args[1]'h
        let urandom ← IO.FS.Handle.mk "/dev/urandom" IO.FS.Mode.read
        let secbytes ← urandom.read ((1 + 15 + 67) * 32)
        let outFile ← IO.FS.Handle.mk filename IO.FS.Mode.write
        outFile.write secbytes
      else
        IO.println helpMessage
    | "scriptgen" =>
      if h : 2 < args.length then
        let input := args[1]!
        let output := args[2]'h
        let (seed, randomizer, seckey) ← readSecfile input
        let pk := Winternitz.keygen seckey randomizer seed
        let script := WinternitzBuilder.CHECKWOTS pk
        let outFile ← IO.FS.Handle.mk output IO.FS.Mode.write
        outFile.write script.serialize
      else
        IO.println helpMessage
    | "scriptparse" =>
      if h : 1 < args.length then
        let input := args[1]'h
        let scriptFile ← IO.FS.Handle.mk input IO.FS.Mode.read
        let scriptBytes ← scriptFile.readBinToEnd
        let script := parseScript scriptBytes.toList
        assert! scriptBytes == script.get!.serialize
        IO.println s!"{script}"
    | "witnessgen" =>
      if h : 3 < args.length then
        let input := args[1]!
        let msg := Schnorr.challenge_cat_trick (fromHex args[2]!).get!
        let output := args[3]'h
        let (seed, randomizer, seckey) ← readSecfile input
        let sig := Winternitz.sign msg seckey randomizer seed
        let witness := WinternitzBuilder.witnessStack msg sig
        let outFile ← IO.FS.Handle.mk output IO.FS.Mode.write
        assert! Stack.parse (witness.serialize) == some witness
        outFile.write witness.serialize
    | "verify" =>
      -- read script file and witness file, and sighash
      if h : 3 < args.length then
        let scriptFile := args[1]!
        let sighash := (fromHex (args[2]!)).get!
        let witnessFile := args[3]'h
        let scriptFile ← IO.FS.Handle.mk scriptFile IO.FS.Mode.read
        let scriptBytes ← scriptFile.readBinToEnd
        let witnessFile ← IO.FS.Handle.mk witnessFile IO.FS.Mode.read
        let witnessBytes ← witnessFile.readBinToEnd
        match parseScript scriptBytes.toList with
        | none => IO.println "Invalid script"
        | some script =>
          match Stack.parse witnessBytes with
          | none => IO.println "Invalid witness"
          | some witness =>
            if Script.verify script witness sighash then
              IO.println "valid"
            else
              IO.println "invalid"
      else
        IO.println helpMessage
    | _ => IO.println helpMessage
  else
    IO.println helpMessage
