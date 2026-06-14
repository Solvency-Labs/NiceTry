import NiceTry.Fors.Types

namespace NiceTry.Fors

/--
Hash output is still opaque at this layer, but the transcript shape is explicit.
This lets later proofs talk about the exact padding/ADRS/domain inputs without
claiming concrete Keccak values or cryptographic security.
-/
inductive TranscriptField where
  | pad16 : Hash16 -> TranscriptField
  | digest32 : Digest -> TranscriptField
  | adrs32 : Adrs -> TranscriptField
  | domainFors : TranscriptField
deriving DecidableEq, Repr

opaque keccakWord : List TranscriptField -> Word

/-- The verifier keeps the high 16 bytes of leaf/node/root Keccak outputs. -/
def NMaskWord : Nat := 2 ^ 256 - 2 ^ 128

/-- The final signer address keeps the low 160 bits of its Keccak output. -/
def Lower160Mask : Nat := 2 ^ 160 - 1

/-- A model `Hash16` is the high-16-byte mask of the shared Keccak word. -/
def keccakHash16 (fields : List TranscriptField) : Hash16 :=
  keccakWord fields &&& NMaskWord

/-- A model address is the low-160-bit mask of the shared Keccak word. -/
def keccakAddress (fields : List TranscriptField) : Address :=
  keccakWord fields &&& Lower160Mask

def hMsgTranscript
    (pkSeed : Hash16)
    (r : Hash16)
    (digest : Digest)
    (counter : Counter) :
    List TranscriptField :=
  [.pad16 pkSeed, .pad16 r, .digest32 digest, .domainFors, .pad16 counter]

def leafTranscript
    (pkSeed : Hash16)
    (adrs : Adrs)
    (sk : Hash16) :
    List TranscriptField :=
  [.pad16 pkSeed, .adrs32 adrs, .pad16 sk]

def nodeTranscript
    (pkSeed : Hash16)
    (adrs : Adrs)
    (left right : Hash16) :
    List TranscriptField :=
  [.pad16 pkSeed, .adrs32 adrs, .pad16 left, .pad16 right]

def rootFields (roots : TreeIndex -> Hash16) : List TranscriptField :=
  (List.ofFn roots).map .pad16

def rootsTranscript
    (pkSeed : Hash16)
    (roots : TreeIndex -> Hash16) :
    List TranscriptField :=
  [.pad16 pkSeed, .adrs32 { adrsType := .forsRoots }] ++ rootFields roots

def addressTranscript
    (pkSeed pkRoot : Hash16) :
    List TranscriptField :=
  [.pad16 pkSeed, .pad16 pkRoot]

def hMsg
    (pkSeed : Hash16)
    (r : Hash16)
    (digest : Digest)
    (counter : Counter) :
    Word :=
  keccakWord (hMsgTranscript pkSeed r digest counter)

def leafHash
    (pkSeed : Hash16)
    (adrs : Adrs)
    (sk : Hash16) :
    Hash16 :=
  keccakHash16 (leafTranscript pkSeed adrs sk)

def nodeHash
    (pkSeed : Hash16)
    (adrs : Adrs)
    (left right : Hash16) :
    Hash16 :=
  keccakHash16 (nodeTranscript pkSeed adrs left right)

def compressRoots
    (pkSeed : Hash16)
    (roots : TreeIndex -> Hash16) :
    Hash16 :=
  keccakHash16 (rootsTranscript pkSeed roots)

def addressFromRoot
    (pkSeed : Hash16)
    (pkRoot : Hash16) :
    Address :=
  keccakAddress (addressTranscript pkSeed pkRoot)

end NiceTry.Fors
