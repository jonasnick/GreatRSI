import GreatRSI.SHA256
import GreatRSI.Bytes

-- https://eprint.iacr.org/2017/965.pdf

namespace Winternitz
def n := 32 -- size of message in bytes
def w := 16 -- "Winternitz parameter"
def len_1 := 64 -- ceil(8n / lg(w))
def len_2 := 3 -- floor(lg(len_1 * (w - 1)) / lg(w)) + 1.
def len := len_1 + len_2

-- keyed hash function
def f_k (k: ByteArray) (x: ByteArray): ByteArray :=
  sha256 (k.append x)


-- recursive variant from paper
def chain (x: ByteArray) (steps: Nat) (seed: ByteArray) (randomization: List ByteArray): ByteArray :=
  match steps with
  | 0 => x
  | Nat.succ s' =>
    f_k seed (ByteArray.xor (chain x s' seed (List.drop 1 randomization))
                            randomization[0]!)

namespace ChainTest
def x := [0].toByteArray
def seed := [1].toByteArray
def randomization :=[[0xff].toByteArray, [0xff].toByteArray, [0xfe].toByteArray]
def chain2 := chain x 2 seed (List.drop 1 randomization)
#guard chain x 3 seed randomization == chain chain2 1 seed randomization
end ChainTest

-- size len*n
abbrev Seckey := List ByteArray

def ByteArray.parseSeckey (bytes: ByteArray): Seckey :=
  assert! bytes.size == len*n
  (List.range 67).map (fun i =>
    let offset := i*32
    bytes.extract offset (offset+32))


-- size len*n
structure Pubkey where
  seed : ByteArray
  randomization : List ByteArray
  hashes : List ByteArray
deriving BEq, Repr, Inhabited

def Pubkey.serialize (pk: Pubkey): ByteArray :=
  pk.seed.append ((flatten pk.randomization).append (flatten pk.hashes))

def keygen (sk: Seckey) (randomization: List ByteArray) (seed: ByteArray): Pubkey :=
  assert! sk.length == len
  assert! randomization.length == w - 1
  assert! seed.size == 32
  { seed := seed,
    randomization := randomization,
    hashes := (sk.map (fun x => chain x (w - 1) seed randomization)) }

def base16 (x: ByteArray): List UInt8 :=
  x.foldl (fun acc b => acc ++ ([b >>> 4] ++ [b &&& 0x0F])) []

def base16_test := (match (fromHex "1234") with
  | none => false
  | some x => (base16 x) == [1, 2, 3, 4])
#guard base16_test
#guard (base16 ([0x7A, 0xF3, 0x1E, 0x8C, 0xB2, 0x5D, 0x96, 0x40,
                 0xC1, 0x3A, 0x0F, 0xE7, 0x52, 0x89, 0x6D, 0xA4,
                 0x2B, 0xF8, 0x71, 0xD5, 0x9E, 0x34, 0xC7, 0x0A,
                 0x5F, 0x83, 0x1B, 0xE6, 0x4D, 0x92, 0xA8, 0x60].toByteArray)) ==
                 [7, 10, 15, 3, 1, 14, 8, 12, 11, 2, 5, 13, 9, 6, 4, 0, 12, 1, 3,10, 0, 15, 14, 7, 5, 2, 8, 9, 6, 13, 10, 4, 2, 11, 15, 8, 7, 1, 13, 5, 9, 14, 3, 4, 12, 7, 0, 10, 5, 15, 8, 3, 1, 11, 14, 6, 4, 13, 9, 2, 10, 8, 6, 0]

def base16_inv (x: List UInt8): ByteArray :=
  let n := x.foldl (fun acc b => acc*16 + (UInt8.toNat b)) 0
  n.toByteArray

#guard base16_inv (base16 [192, 3].toByteArray) == [192, 3].toByteArray
#guard base16_inv (base16 [18, 52, 192, 0, 99, 0xFF].toByteArray)
      == [18, 52, 192, 0, 99, 0xFF].toByteArray


def checksum (M: List UInt8): List UInt8 :=
  let C := M.foldl (fun acc M_i => acc + (w - 1 - M_i.toNat)) 0
  let C' := C.toByteArray
  let c16 := base16 C'
  -- pick only the last len_2 elements, the first elements are 0 anyway
  let l := c16.length - len_2
  assert! (c16.take l).foldl (fun acc c_i => acc && c_i == 0) true
  c16.drop l

#guard checksum (base16 (List.replicate 32 0x00.toUInt8).toByteArray) == [3, 12, 0]

def winternitzdigits (M: ByteArray) : List UInt8 :=
  let M' := base16 M
  M'.append (checksum M')

def witnernitz (M: ByteArray) (xs: List ByteArray) (randomization: List ByteArray) (seed: ByteArray) (verify: Bool): List ByteArray :=
  let B := winternitzdigits M
  assert! B.length == len
  let B' := B.map (if verify then fun b => w - 1 - b.toNat else fun b => b.toNat)
  let r := fun b => if !verify then w - 1 - b else 0
  let zipped := List.zip xs B'
  zipped.foldl (fun acc z => (acc ++ [(chain z.1 z.2 seed (List.drop (r z.2) randomization))])) []

def sign (M: ByteArray) (sk: Seckey) (randomization: List ByteArray) (seed: ByteArray): List ByteArray :=
  witnernitz M sk randomization seed false

def pk_from_sig (M: ByteArray) (sig: List ByteArray) (randomization: List ByteArray) (seed: ByteArray): ByteArray :=
  let pk_0 := seed.append (flatten randomization)
  let pk_i :=  witnernitz M sig randomization seed true
  pk_0.append (flatten pk_i)

namespace Test

def completeness (seed: ByteArray) (randomization: List ByteArray) (M: ByteArray) (pk: Pubkey) (sig: List ByteArray): Bool :=
  let pk' := pk.serialize
  assert! pk'.size == ((w-1)*n + n + len*n)
  let computed_pk := pk_from_sig M sig randomization seed
  computed_pk == pk'

namespace one
def M := ((List.range 32).map (fun x => x.toUInt8)).toByteArray
def sk: Seckey := (List.range len).map (fun x => ((List.range 32).map (fun y => (x + y).toUInt8)).toByteArray)
def seed := ((List.range 32).map (fun x => (x + 3).toUInt8)).toByteArray
def randomization := (List.range (w-1)).map (fun x => ((List.range 32).map (fun y => (x + y + 7).toUInt8)).toByteArray)
def pk := keygen sk randomization seed
def sig := sign M sk randomization seed
#guard completeness seed randomization M pk sig == true
end one

namespace two
def M := (fromHex "43aa5c341c39ce3bd1aec51cb3b413d9fa9434d97b3a58977b24fab8069fe371").get!
def sk: Seckey := [
  fromHex "7700e44728dfdcd1f5cbc8197d75dbd97e1072e6f4c09b1baf2772b8eab38a4d",
  fromHex "074a287ef99f24423351fa9137aac7d5b805a4da482170c6aea0a8950aab78cc",
  fromHex "4ae5e4209401456ef6713fb39ca549a61f7fa78a8089c1af409c3015655d34fc",
  fromHex "69a9396fcac8bf07c241e11ead9ed80f0ad53b3b61fd1f51e019b1b46d325cf7",
  fromHex "ca4ccf92e2d6cb27a3f705cff79aca22251c99ac1d0f2f817d0e6b2ada1e78bc",
  fromHex "841368ba2158ce573ef422f0149b33a97679ec8ed9017fa0d5a025d6be8ec424",
  fromHex "12e43b15905ae51345d778598d821c03903dbd0740f0291e4760b72eb1f47840",
  fromHex "de468a4a1dd2a323f83c73402f09af8b4267dd05efecf17072fdfa5e836051ec",
  fromHex "31778e12ae20e98e96ef8ee4288216cc3e9b1b40a4935be73ff31cd2efaf47ae",
  fromHex "5c69a5c179bf1be31074aecba63250c5d4ef065f6807c47aa646ba8f13549b40",
  fromHex "956392a10cb86ee4c4d33deb514d4b31cf8295006c6efdb651b5eb0b7b20e7a0",
  fromHex "18bab9eb22e4c66dcd1e3905e5d18db0f555f9f8a4b5c20f1079a4bd34701343",
  fromHex "f948d492f1f801ddee7e3375429fe5601fc1bc165aa716532403e15d428df8cd",
  fromHex "c8483ee69d955a601e42352c9a4b2095bc7ab53d202f9afa13913515e1a63fbd",
  fromHex "d4351a2b27a8fe533148257e434e5bfa75032e1d5c48296c2eb24b9e53faf46a",
  fromHex "ddac6c3605088a84cb2e23af1d4fb4303aa5d584c561c3d4492a7905a60a5b2c",
  fromHex "a443f9395b172accfea55a465e8a68e6f4dba9dc60d6b1ffc0536cd737e8b59d",
  fromHex "d6b6a8fb17612bb78a4823232df94573dccee7535c4403cad079640deefcc2fa",
  fromHex "3af25d7e8ab88c4d7853544dad4984649194530b8a722a0d84831c5a9e544eed",
  fromHex "b17735af8636c2ddcaf63212572c50fec9826fcf5c3e20e4da3ffe68f164747d",
  fromHex "5d806836f65ab4ba3e7de04ddab5618a77115370c9384ebab2a2477ab044e954",
  fromHex "591d0608a5219f094af98b7c0ddb1d5190cf307521e151431926e9d645183918",
  fromHex "2920ab03ffbf5b8ae416f1e6b1e1a181555ccc51aca300163f978cb4100ca655",
  fromHex "aa256022492048b6e4455e88ecabe908ef7a22f8da4c3fbfae1d62e1f672ec27",
  fromHex "23e06bda6e99abcf49ae8a86547fc3cbf2bf2bb8d526082671bb3811deaaff12",
  fromHex "b857798a65cf68dfaa279f76f0b18d321f16d35d96f4757c1d7de947d9982c10",
  fromHex "3f546ef3ba9442c93c966e13dd155c1310b53680dda5a993c7cef9187ebf5abc",
  fromHex "e215ed98bd1aeaee254a9440311baf91e38ec8bbc01bf4e98257dff2d5635b2a",
  fromHex "36d23f22a14af54569b4de8dc1908866b5d01718b93e048b7b1ffe5b1f521c36",
  fromHex "8cd7b1014fc40eed42fadbd3a7969e02ca87612fc2add8cd1b5394af1ff0c8ca",
  fromHex "c01e6a4302ab66de050447c9a4e16a3bd8055db02887ce28b6d3d65d36313a77",
  fromHex "49f5524fcb2b04c7ad0137d64dd4f38ef8e8c0354d670608e904d088c203fabb",
  fromHex "dddaac2effacc666952c8d37afc8c75d663d3cf06d64a6421656bcbaa042b099",
  fromHex "7e9331a631ccb9cc172291464672546c7bb2afc10da738ae8b93621191641a86",
  fromHex "b1a968fd2d78157abac04e7aba856ad468ab5f24aaa7a68dc8e0fd218bc97843",
  fromHex "7f8aed1840aa2f055ca81d71d2506c59335a46563861bbff2970c60b92316f68",
  fromHex "ad421ed57c1dc01bc8d6da0a5c7140a108df899e5221fb1ac3b088919286dd20",
  fromHex "8c41fd108c86ebf5cedadc5b24f5c1f64f71319fd03cb0d0b88b9335bb9d07ae",
  fromHex "246590d5c82dbb38eca1736e0786acffa7602a1380a04cc22297a70169e45d6b",
  fromHex "72d81fcb9a35c50afbb0a4099009c3dccd9dcde299b894ec98dc5ca04a7ea072",
  fromHex "8ca0915b0fd8772df6fe33d79f01b9a77619b39e1b193c5745747e305b7df577",
  fromHex "b3341fb2119b42e3c5af2659b6354fcc91898311dcd3e21e4fabb237ce655f72",
  fromHex "42d4663da900db7db9002162e089a87b26b48a0a112e4f392b29d6c8f04f73ea",
  fromHex "34058e7753c5b8f75d0c860e238475cb5aaf0a70f9b414ef1175c1f830d6988d",
  fromHex "e3e4d70c0cd2d53f8e95ecf46925c137153362a6088d78613ada364993fb9bb2",
  fromHex "8936794309e4771272176cb7d2213b33416ff7864873196bef810c5217953b3f",
  fromHex "9ff994fb23c6ca86299be970b5843993cf7a28ad35fa9c84cf8d478a39859603",
  fromHex "3e457d83fc2e877212eb5665ca64e4eb072b85cc80d764018963143e48caf495",
  fromHex "492c2b7b34b56394922d9c2f1682b485874fbe5f98a55050f167c96d8d66f74f",
  fromHex "476e4cbe3569fd57efd7ff6a7a66ba4f4a1281caec8e171ecbef84b8ee0f9068",
  fromHex "dea89bdc749ee0e7202ba430acf4b81ec8d1240827fc013267dea6dde79b10f9",
  fromHex "e88430c0592b98ba296fc92af264436d21a1594db842b7622a69c810bdd087ee",
  fromHex "2812b3aade14d3ef9039f0db3c38a9b4fd9e0244fca142746725b8519ad73884",
  fromHex "821ddb880bf7a0ed12818c5164557cb7c18097adb67c9caa8ab88f80a88172c2",
  fromHex "4cb9457c65ed3e1a6452e56d62b6140a6c0a3c9e10b180a166e7935ef276300d",
  fromHex "ff4f15f2ee6cd15e223f75c0409d8215f6d63bb06707fc47188a023272b3c42c",
  fromHex "b90ea0f5049c2420731e61624c5fefb06e09c8886356fac0243e7b2df2535127",
  fromHex "9ccc7aa01142b8eba75f865eabc3345b0dedbc7d27c3ef0578754cefc235145c",
  fromHex "742b2cf208cfa05355bbd1c1c8fa9979f05dfead76de2862718956af44accf58",
  fromHex "f0eb91410beff3e906c4e0d6916352331cc9a117c9a6a9e4aff7461b645ea553",
  fromHex "23b28c1de1a3f60079a4197b83050f19f0ab6d32b348fec5726008809bda9fa9",
  fromHex "7ffef37b8b63f67f07a4234cf692956b660065a1f4f22968c61f736cd5195cb3",
  fromHex "d297d1a1bb0bb717c8f494f68a81b18f0241065d0c7e364fc660d886d190d489",
  fromHex "4eaa16f0ab9f66a2a61e18f0796ba9a0ad9b1a2b2fe7950cb60b9ea28c586060",
  fromHex "289b916d105cea18d5577878325fbf673730d4c09271d7ed42d070287ec8c21b",
  fromHex "93d2ab1ba1818dd0b195b1c0f18bf8598878cdd9159bdbd18057a20ecae8bc6f",
  fromHex "cc2aa301860867c6efe071ffb1eba7e20ba07cc354a6769e39f0a858ec0d3e97",
].map fun x => x.get!
def seed := (fromHex "16da87bacccf9123a96f4236ca9c1aff65993e524713b6d22e872172027c2853").get!
def randomization: List ByteArray := [
  fromHex "3e1ee27d230c9876514203f2340cf2a713903612519e93b67bc30511c76cb748",
  fromHex "435d683df80f2c36d5f97f8a565bb36a05ba09afa903366fafd0db79191376f7",
  fromHex "cb89fa4c99819c526af7931a0348a753a427b7da1025b9b7951555102e50524b",
  fromHex "b79f2a6f99316d3895fa80340d441622f11a28d8e961c7785a0e509204185664",
  fromHex "9297f2101b4c969d718f2607251935e2f6d9efa0ca1737145e78b9ba7dfacaed",
  fromHex "e6e3a6595bdaf14dffcdd6fe62a84617f6149eef7399ebd7bd02e6226582ecff",
  fromHex "1a9c9a107580d7d359f108f1526c62b95a7b9b274b1fb044bbe2baadeb48a6f0",
  fromHex "c451040b7f8ceb7787b3c1ad191e2f929a06a6d61c76a0c7de4c4b1ef4808a5c",
  fromHex "8e7936ac25bf1e7a827716299200519dd8493ef4acbd4a8309d7f88e5167d7df",
  fromHex "2a8b6a5a10871230c62522df6d117572ad7b44ada0d10f83376f8c325bde23ce",
  fromHex "923791177bda1d4cad85722e0354cd11dff7564a536429f1760ed3e9ad759eea",
  fromHex "525db3403dc624e21efebd2afb22474aa2f03028fd0bacbca05c2ab7b49a25e9",
  fromHex "e572a07dc374f99ee99736810d154ab057d0e891d9710766e4537ba31efbdfb6",
  fromHex "6eb1c214d78e73200a76a7ba77a8b323aaeee41d3ed86ababc906e6a19febd53",
  fromHex "8cd3621a73a6647ac063babcd87f8bd8dc1f64d66ffa5285563fe5dfd066d4f6",
].map fun x => x.get!
def pk := keygen sk randomization seed
def sig := sign M sk randomization seed
#guard completeness seed randomization M pk sig == true
end two

end Test
end Winternitz
