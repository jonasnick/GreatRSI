import GreatRSI.SHA256

def List.pairwiseMap {α β} (f : α → α → β) : List α → List β
  | [] => []
  | [x] => [f x x]
  | x :: y :: xs => f x y :: pairwiseMap f xs

namespace MerkleTree

-- Note: does not hash the leaves
partial def root (elements : List ByteArray) : ByteArray :=
  if elements.isEmpty then
    sha256 ByteArray.empty
  else
    let rec buildTree (hashes : List ByteArray) : ByteArray :=
      match hashes with
      | [hash] => hash  -- Only one hash left, this is the root
      | _ =>
        let pairedHashes := hashes.pairwiseMap (fun left right =>
          sha256 (left ++ right))
        buildTree pairedHashes
    buildTree elements

namespace Test

def a := List.toByteArray [0]
def b := List.toByteArray [1, 2]
def t1 := sha256 (a ++ b)
def t2 := sha256 (b ++ a)
-- tree a b b a
def t3 := sha256 (t1 ++ t2)

#guard a == root [a]
#guard t1 == root [a, b]
#guard t3 == root [a, b, b, a]

end Test

end MerkleTree
