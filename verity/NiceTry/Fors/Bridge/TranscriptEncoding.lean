import NiceTry.Fors.Bridge.EvmMemory

/-!
# Canonical FORS transcript encoding

This module separates the mechanical value/byte correspondence from the trusted
Keccak step. A transcript field is encoded as the exact 32-byte EVM word written
by the reviewed verifier runtime transcription. The cryptographic bridge can
therefore be stated over `encodeTranscript fields`, without shape-specific byte
hypotheses or bundled masking claims.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

/-- Concrete 32-byte ADRS word represented by a model `Adrs`. -/
def transcriptAdrsWord (adrs : Adrs) : Nat :=
  match adrs.adrsType with
  | .forsTree =>
      if adrs.height = 0 then
        shapeLeafAdrsWord adrs.tree adrs.index
      else
        shapeNodeAdrsWord adrs.tree adrs.height adrs.index
  | .forsRoots => ForsRootsAdrsWord

/-- Concrete EVM word represented by one abstract transcript field. -/
def transcriptFieldWord : TranscriptField → Nat
  | .pad16 value => value
  | .digest32 value => value
  | .adrs32 adrs => transcriptAdrsWord adrs
  | .domainFors => ForsDomainWord

/-- Canonical byte encoding hashed by the verifier for an abstract transcript. -/
def encodeTranscript (fields : List TranscriptField) : ByteArray :=
  ⟨concatData (fields.map fun field =>
    (UInt256.ofNat (transcriptFieldWord field)).toByteArray)⟩

theorem transcript_uint256_eq_of_toNat_eq (v : UInt256) (n : Nat)
    (h : v.toNat = n) :
    v = UInt256.ofNat n := by
  cases v with
  | mk v =>
      congr 1
      apply Fin.ext
      simp only [Fin.val_ofNat]
      calc
        v.val = n := h
        _ = n % UInt256.size := (Nat.mod_eq_of_lt (h ▸ v.isLt)).symm

theorem transcript_uint256_ofNat_toNat (v : UInt256) :
    UInt256.ofNat v.toNat = v :=
  (transcript_uint256_eq_of_toNat_eq v v.toNat rfl).symm

theorem transcriptAdrsWord_leaf (tree leafIdx : Nat) :
    transcriptAdrsWord (leafAdrs tree leafIdx) =
      shapeLeafAdrsWord tree leafIdx := by
  simp [transcriptAdrsWord, leafAdrs]

theorem transcriptAdrsWord_node (tree height parentIdx : Nat) :
    transcriptAdrsWord (nodeAdrs tree height parentIdx) =
      shapeNodeAdrsWord tree height parentIdx := by
  by_cases hheight : height = 0
  · subst height
    simp [transcriptAdrsWord, nodeAdrs, shapeLeafAdrsWord,
      shapeNodeAdrsWord, HeightWord, twoPow, A]
  · simp [transcriptAdrsWord, nodeAdrs, hheight]

theorem transcriptAdrsWord_roots :
    transcriptAdrsWord rootsAdrs = ForsRootsAdrsWord := by
  rfl

theorem encodeTranscript_address (pkSeed pkRoot : UInt256) :
    encodeTranscript (addressTranscript pkSeed.toNat pkRoot.toNat) =
      pkSeed.toByteArray ++ pkRoot.toByteArray := by
  apply ByteArray.ext
  simp only [encodeTranscript, addressTranscript, List.map_cons, List.map_nil,
    transcriptFieldWord, concatData, ByteArray.data_append]
  rw [transcript_uint256_ofNat_toNat, transcript_uint256_ofNat_toNat]
  simp

theorem encodeTranscript_hmsg
    (pkSeed r digest domain counter : UInt256)
    (hdomain : domain.toNat = ForsDomainWord) :
    encodeTranscript
        (hMsgTranscript pkSeed.toNat r.toNat digest.toNat counter.toNat) =
      ⟨concatData
        ([pkSeed, r, digest, domain, counter].map UInt256.toByteArray)⟩ := by
  apply ByteArray.ext
  simp only [encodeTranscript, hMsgTranscript, List.map_cons, List.map_nil,
    transcriptFieldWord, concatData]
  rw [transcript_uint256_ofNat_toNat, transcript_uint256_ofNat_toNat,
    transcript_uint256_ofNat_toNat, transcript_uint256_ofNat_toNat,
    ← transcript_uint256_eq_of_toNat_eq domain _ hdomain]

theorem encodeTranscript_leaf
    (pkSeed adrs sk : UInt256) (tree leafIdx : Nat)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree leafIdx) :
    encodeTranscript
        (leafTranscript pkSeed.toNat (leafAdrs tree leafIdx) sk.toNat) =
      ⟨concatData ([pkSeed, adrs, sk].map UInt256.toByteArray)⟩ := by
  apply ByteArray.ext
  simp only [encodeTranscript, leafTranscript, List.map_cons, List.map_nil,
    transcriptFieldWord, transcriptAdrsWord_leaf, concatData]
  rw [transcript_uint256_ofNat_toNat, transcript_uint256_ofNat_toNat,
    ← transcript_uint256_eq_of_toNat_eq adrs _ hadrs]

theorem encodeTranscript_node
    (pkSeed adrs left right : UInt256) (tree height parentIdx : Nat)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height parentIdx) :
    encodeTranscript
        (nodeTranscript pkSeed.toNat (nodeAdrs tree height parentIdx)
          left.toNat right.toNat) =
      ⟨concatData
        ([pkSeed, adrs, left, right].map UInt256.toByteArray)⟩ := by
  apply ByteArray.ext
  simp only [encodeTranscript, nodeTranscript, List.map_cons, List.map_nil,
    transcriptFieldWord, transcriptAdrsWord_node, concatData]
  rw [transcript_uint256_ofNat_toNat, transcript_uint256_ofNat_toNat,
    transcript_uint256_ofNat_toNat,
    ← transcript_uint256_eq_of_toNat_eq adrs _ hadrs]

theorem encodeTranscript_roots
    (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord) :
    encodeTranscript
        (rootsTranscript pkSeed.toNat (fun i => (roots i).toNat)) =
      ⟨concatData (rootsBufferBytes pkSeed rootsAdrs roots)⟩ := by
  apply ByteArray.ext
  have hadrsWord :
      UInt256.ofNat ForsRootsAdrsWord = rootsAdrs :=
    (transcript_uint256_eq_of_toNat_eq rootsAdrs ForsRootsAdrsWord hadrs).symm
  have hrootBytes :
      (List.ofFn (fun i => (roots i).toNat)).map
          (fun value => (UInt256.ofNat value).toByteArray) =
        (List.ofFn roots).map UInt256.toByteArray := by
    rw [List.map_ofFn, List.map_ofFn]
    congr 1
    funext i
    exact congrArg UInt256.toByteArray (transcript_uint256_ofNat_toNat (roots i))
  have hwords :
      (rootsTranscript pkSeed.toNat (fun i => (roots i).toNat)).map
          (fun field =>
            (UInt256.ofNat (transcriptFieldWord field)).toByteArray) =
        rootsBufferBytes pkSeed rootsAdrs roots := by
    unfold rootsTranscript rootsBufferBytes rootsBufferValues
    rw [List.map_append]
    simp only [List.map_cons, List.map_nil, transcriptFieldWord]
    rw [show transcriptAdrsWord { adrsType := .forsRoots } =
        ForsRootsAdrsWord from rfl]
    rw [transcript_uint256_ofNat_toNat, hadrsWord]
    rw [rootFields, List.map_map]
    change [pkSeed.toByteArray, rootsAdrs.toByteArray] ++
        (List.ofFn (fun i => (roots i).toNat)).map
          (fun value => (UInt256.ofNat value).toByteArray) =
      [pkSeed.toByteArray, rootsAdrs.toByteArray] ++
        (List.ofFn roots).map UInt256.toByteArray
    rw [hrootBytes]
  exact congrArg concatData hwords

end NiceTry.Fors.Bridge
