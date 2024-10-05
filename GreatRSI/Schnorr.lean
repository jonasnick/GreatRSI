import GreatRSI.SHA256
import GreatRSI.Bytes

namespace Schnorr

def G := (fromHex "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798").get!

-- This is the correct signature challenge if pk = G and R = G
def challenge_cat_trick (m: ByteArray) : ByteArray :=
  -- TODO: misses hash tag
  sha256 (G ++ G ++ m)

def verify_dummy (pk: ByteArray) (m: ByteArray) (sig: ByteArray) : Bool :=
  assert! pk.size == 32 && m.size == 32 && sig.size == 64
  if pk != G then false else
    let (R, s) := sig.toList.splitAt 32
    let (R, s) := (R.toByteArray, s.toByteArray)
    if R != G then false else
      -- s*G = R + H(R, pk, m)P <=> s = 1 + H(R, pk, m)
      -- NOTE: the probability of the event that 1 + sha(...) is out of range is
      --       negligible
      s.toNat == 1 + (challenge_cat_trick m).toNat

end Schnorr
