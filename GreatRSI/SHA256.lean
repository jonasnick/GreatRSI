import GreatRSI.Bytes

-- Initial hash values (H0 to H7)
def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

-- Constants K
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

-- Bitwise functions
def ROTR (x : UInt32) (n : UInt32) : UInt32 :=
  (x.shiftRight n) ||| (x.shiftLeft (32 - n))

def SHR (x : UInt32) (n : UInt32) : UInt32 :=
  x.shiftRight n

def bigSigma0 (x : UInt32) : UInt32 :=
  ROTR x 2 ^^^ ROTR x 13 ^^^ ROTR x 22

def bigSigma1 (x : UInt32) : UInt32 :=
  ROTR x 6 ^^^ ROTR x 11 ^^^ ROTR x 25

def smallSigma0 (x : UInt32) : UInt32 :=
  ROTR x 7 ^^^ ROTR x 18 ^^^ SHR x 3

def smallSigma1 (x : UInt32) : UInt32 :=
  ROTR x 17 ^^^ ROTR x 19 ^^^ SHR x 10

def Ch (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (~~~ x &&& z)

def Maj (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

-- Function to convert UInt32 to ByteArray in big-endian order
def UInt32.toBytesBE (x : UInt32) : ByteArray :=
  let b0 := UInt8.ofNat ((x >>> 24).toNat &&& 0xFF)
  let b1 := UInt8.ofNat ((x >>> 16).toNat &&& 0xFF)
  let b2 := UInt8.ofNat ((x >>> 8).toNat &&& 0xFF)
  let b3 := UInt8.ofNat (x.toNat &&& 0xFF)
  ByteArray.mk #[b0, b1, b2, b3]

-- Function to convert UInt64 to ByteArray in big-endian order
def UInt64.toBytesBE (x : UInt64) : ByteArray :=
  let b0 := UInt8.ofNat ((x >>> 56).toNat &&& 0xFF)
  let b1 := UInt8.ofNat ((x >>> 48).toNat &&& 0xFF)
  let b2 := UInt8.ofNat ((x >>> 40).toNat &&& 0xFF)
  let b3 := UInt8.ofNat ((x >>> 32).toNat &&& 0xFF)
  let b4 := UInt8.ofNat ((x >>> 24).toNat &&& 0xFF)
  let b5 := UInt8.ofNat ((x >>> 16).toNat &&& 0xFF)
  let b6 := UInt8.ofNat ((x >>> 8).toNat &&& 0xFF)
  let b7 := UInt8.ofNat (x.toNat &&& 0xFF)
  ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7]

def padMessage (message : ByteArray) : ByteArray :=
  let ml := message.size * 8  -- Message length in bits
  let lenBytes := UInt64.ofNat ml |>.toBytesBE
  let rem := (message.size + 1) % 64  -- Remainder after adding 0x80
  let padLen := if rem ≤ 56 then 56 - rem else 120 - rem
  let padding := ByteArray.mk #[0x80] ++ ByteArray.mk (Array.mkArray padLen 0x00)
  message ++ padding ++ lenBytes

def processChunk (hash : Array UInt32) (chunk : ByteArray) : Array UInt32 :=
  -- Message schedule array (words)
  let words := Id.run do
    let mut w : Array UInt32 := Array.mkArray 64 0
    -- Initialize first 16 words from the chunk
    for i in [:16] do
      let idx : Nat := i * 4
      let word := if chunk.size > idx + 3 then
        let b0 := chunk.get! idx
        let b1 := chunk.get! (idx + 1)
        let b2 := chunk.get! (idx + 2)
        let b3 := chunk.get! (idx + 3)
        UInt32.ofNat (
          (b0.toNat <<< 24) ||| (b1.toNat <<< 16) |||
          (b2.toNat <<< 8) ||| b3.toNat
        )
      else 0  -- For empty chunk
      w := w.set! i word
    -- Extend the words array from index 16 to 63
    for i in [16:64] do
      let s0 := smallSigma0 (w.get! (i - 15))
      let s1 := smallSigma1 (w.get! (i - 2))
      let newWord := w.get! (i - 16) + s0 + w.get! (i - 7) + s1
      w := w.set! i newWord
    return w

  -- Initialize working variables
  let (a0, b0, c0, d0, e0, f0, g0, h0) := (
    hash.get! 0, hash.get! 1, hash.get! 2, hash.get! 3,
    hash.get! 4, hash.get! 5, hash.get! 6, hash.get! 7
  )

  -- Compression function main loop
  let (a, b, c, d, e, f, g, h) := Id.run do
    let mut a := a0
    let mut b := b0
    let mut c := c0
    let mut d := d0
    let mut e := e0
    let mut f := f0
    let mut g := g0
    let mut h := h0
    for i in [:64] do
      let T1 := h + bigSigma1 e + Ch e f g + K.get! i + words.get! i
      let T2 := bigSigma0 a + Maj a b c
      h := g
      g := f
      f := e
      e := d + T1
      d := c
      c := b
      b := a
      a := T1 + T2
    return (a, b, c, d, e, f, g, h)

  -- Compute the new hash values
  let newHash := #[
    a + a0, b + b0, c + c0, d + d0,
    e + e0, f + f0, g + g0, h + h0
  ]
  newHash

-- Main SHA-256 function
def sha256 (message : ByteArray) : ByteArray :=
  let paddedMessage := padMessage message
  let numChunks := paddedMessage.size / 64  -- Since size is multiple of 64
  let chunks := List.range numChunks |>.map (fun i =>
    paddedMessage.extract (i * 64) ((i + 1) * 64))
  let finalHash := chunks.foldl (fun hash chunk =>
    let newHash := processChunk hash chunk
    newHash
  ) initialHash
  let hashBytes := finalHash.foldl (fun acc h => acc ++ h.toBytesBE) ByteArray.empty
  hashBytes

#guard (sha256 (List.toByteArray [])).toHex == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard (sha256 ("abc".toUTF8)).toHex == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (sha256 ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8)).toHex == "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard (sha256 ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu").toUTF8).toHex == "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"
