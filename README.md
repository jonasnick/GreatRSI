# Great Restored Script Interpreter

This repository contains an experimental partial interpreter for the [Great Script Restoration](https://github.com/rustyrussell/bips/pull/1) (GSR), a proposal to re-enable and clean up Bitcoin script opcodes. The interpreter is implemented in the Lean 4 programming language. Note that the current implementation lacks a crucial GSR feature: the "varops budget."

Additionally, this repository includes an implementation of the Winternitz One-Time Signature scheme (W-OTS) written in Bitcoin Script using the Great Script Restoration.

## Winternitz One-Time Signatures (W-OTS)

The Great Script Restoration potentially offers a path toward post-quantum security for Bitcoin. As demonstrated here, it enables W-OTS verification in Bitcoin Script and, through a CAT-based covenant, ensures the signed message matches the spending transaction's sighash.

These scripts can be embedded in a taproot tree, and if a post-quantum threat emerges, the Taproot key path can be disabled with a soft-fork. This would enforce spending conditions that require knowledge of the Winternitz secret key.

The W-OTS implementation follows the description in ["W-OTS+ Shorter Signatures for Hash-Based Signature Schemes"](https://eprint.iacr.org/2017/965.pdf).
W-OTS is also standardized as part of [RFC 8391](https://datatracker.ietf.org/doc/html/rfc8391).

The resulting Bitcoin script can be understood as emulating an OPCODE `CHECKWOTS` for some public key that:
1. Pops the spending transaction's sighash and signature from the stack
2. Pushes `1` on the stack if the signature is valid and, otherwise, fails execution

### Limitations

A significant drawback is the substantial increase in witness size for coin spending, approximately 24kB in this implementation—roughly 375 times larger than a Schnorr signature witness. This would likely impact Bitcoin's usability considerably.

### Security Assumptions

Informally speaking, using the W-OTS+ script in Bitcoin is secure against post-quantum attackers under the following assumptions:
- Taproot key path spends are disabled
- SHA256 is collision resistant
- The taproot tweak is collision resistant
- WOTS+ instantiated with SHA256 is unforgeable
- The signer only produces a single signature


### Build
```
lake build
export PATH=$PATH:$(pwd)/.lake/build/bin/
```

### Help
```
wots
```

**Output:**
```
Usage: wots <command> [options]

Commands:
  seckeygen <outfile> - Draws a Winternitz secret key uniformly at random, writes secret key to file.
  scriptgen <infile> <outfile> - Creates a Winternitz public key from the secret key in the input file, and writes the corresopnding Bitcoin Script (GRS) to the output file.
  scriptparse <infile> - Outputs the parsed script in the infile.
  witnessgen <infile> <sighash> <outfile> - Reads the seckey from the input file, computes the Winternitz signature of the sighash, creates the witness and writes it to the output file.
  verify <scriptfile> <sighash> <witnessfile> - Executes the script with the given witness and sighash.
```

### Generate and verify a signature

```
wots seckeygen keyfile
wots scriptgen keyfile scriptfile
export SIGHASH='abababababababababababababababababababababababababababababababab'
wots witnessgen keyfile $SIGHASH witnessfile
wots verify scriptfile $SIGHASH witnessfile 
```

**Output:**
```
valid
```

### Check the size of the files

```
du -h --apparent-size scriptfile witnessfile
```

**Output:**
```
20K	scriptfile
2.2K	witnessfile
```

### Parse a script

```
wots scriptparse scriptfile | head -c 100
```

**Output:**
```
(some [OP_DUP, OP_1ADD, OP_PUSH(79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798),
```
