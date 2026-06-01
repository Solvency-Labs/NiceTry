import Mathlib.Data.Fin.Basic
import NiceTry.Fors.Bridge.ByteArrayLemmas

/-!
# MachineState-level memory lemmas (route i, Gap A continued)

Lifts the proved `ByteArray` lemmas to actual EVMYulLean execution: relates
`MachineState.mstore` to `ByteArray.write`, then assembles what `keccak256(0,0x40)`
reads after the FORS address-derivation `mstore(0x00,pkSeed); mstore(0x20,pkRoot)`.

Offsets are passed as `UInt256` with `.toNat` hypotheses, so the lemma is free of
`OfNat UInt256` literal-reduction concerns (the contract proof supplies them).
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

private theorem uint256_word_list_size (ws : List UInt256) :
    ∀ w ∈ ws.map UInt256.toByteArray, w.size = 32 := by
  intro w hw
  rcases List.mem_map.mp hw with ⟨v, _hv, rfl⟩
  exact uint256_toByteArray_size v

private theorem uint256_ofNat_toNat (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  unfold UInt256.ofNat UInt256.toNat
  rw [Fin.ofNat_eq_cast]
  exact Fin.val_cast_of_lt h

/-- `mstore` touches memory exactly as one `ByteArray.write` of the 32-byte word
    (the `activeWords` bookkeeping is irrelevant to `.memory`). -/
theorem mstore_memory (m : MachineState) (spos sval : UInt256) :
    (m.mstore spos sval).memory
      = ByteArray.write sval.toByteArray 0 m.memory spos.toNat 32 := by
  simp only [MachineState.mstore, MachineState.writeWord, writeBytes]

/-- A small executable model for consecutive `mstore`s at `offset`, `offset+32`, …
    using concrete `UInt256.ofNat` offsets. This is the shape needed for the roots
    buffer before the full loop proof is introduced. -/
def mstoreWords32At : Nat → List UInt256 → MachineState → MachineState
  | _, [], m => m
  | offset, w :: ws, m =>
      mstoreWords32At (offset + 32) ws (m.mstore (UInt256.ofNat offset) w)

/-- The recursive `mstoreWords32At` choreography touches memory exactly like the
    byte-level `writeWords32At`, provided the generated offsets are valid
    `UInt256` values. -/
theorem mstoreWords32At_memory (vals : List UInt256) (m : MachineState) (offset : Nat)
    (hfit : offset + 32 * vals.length < UInt256.size) :
    (mstoreWords32At offset vals m).memory =
      writeWords32At offset (vals.map UInt256.toByteArray) m.memory := by
  induction vals generalizing m offset with
  | nil => simp [mstoreWords32At, writeWords32At]
  | cons v vals ih =>
      have hoff : offset < UInt256.size := by
        simp only [List.length_cons] at hfit
        omega
      have hfit' : offset + 32 + 32 * vals.length < UInt256.size := by
        simp only [List.length_cons] at hfit
        omega
      rw [mstoreWords32At, ih (m.mstore (UInt256.ofNat offset) v) (offset + 32) hfit']
      simp [writeWords32At, mstore_memory, uint256_ofNat_toNat offset hoff]

/-- The recursive `mstoreWords32At` choreography preserves total memory size when
    the overwritten window is in bounds. -/
theorem mstoreWords32At_size (vals : List UInt256) (m : MachineState) (offset : Nat)
    (hfit : offset + 32 * vals.length < UInt256.size)
    (hbound : offset + 32 * vals.length ≤ m.memory.size) :
    (mstoreWords32At offset vals m).memory.size = m.memory.size := by
  rw [mstoreWords32At_memory vals m offset hfit]
  exact writeWords32At_size (vals.map UInt256.toByteArray) m.memory offset
    (uint256_word_list_size vals) (by simpa using hbound)

/-- Initializing the roots buffer with `mstore(0x00, pkSeed)` establishes the
    `pkSeed` prefix used by the roots-compression post-loop handoff. -/
theorem pk_seed_mstore_prefix
    (m : MachineState) (pkSeed : UInt256)
    (hsize : 32 ≤ m.memory.size) :
    (m.mstore (UInt256.ofNat 0) pkSeed).memory.data.extract 0 32 =
      pkSeed.toByteArray.data := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := uint256_ofNat_toNat 0 (by simp [UInt256.size])
  have hdata : (m.mstore (UInt256.ofNat 0) pkSeed).memory.data =
      m.memory.data.extract 0 0 ++ pkSeed.toByteArray.data ++
        m.memory.data.extract (0 + 32) m.memory.size := by
    rw [mstore_memory, h0]
    exact byteArray_write_overwrite pkSeed.toByteArray m.memory 0 32
      (uint256_toByteArray_size pkSeed).symm (by omega) hsize
  rw [hdata]
  rw [show m.memory.data.extract 0 0 = #[] by
    exact Array.extract_empty_of_stop_le_start (by omega)]
  rw [Array.empty_append]
  rw [show 0 + 32 = 32 by omega]
  rw [Array.extract_append_left' (a := pkSeed.toByteArray.data)
    (b := m.memory.data.extract 32 m.memory.size) (i := 0) (j := 32)
    (by rw [show pkSeed.toByteArray.data.size = 32 by
      exact uint256_toByteArray_size pkSeed])]
  exact Array.extract_eq_self_of_le
    (by rw [show pkSeed.toByteArray.data.size = 32 by
      exact uint256_toByteArray_size pkSeed])

/-- `mstore(0x00, pkSeed)` overwrites in place when the current memory is already
    large enough for the roots buffer. -/
theorem pk_seed_mstore_size
    (m : MachineState) (pkSeed : UInt256)
    (hsize : 32 ≤ m.memory.size) :
    (m.mstore (UInt256.ofNat 0) pkSeed).memory.size = m.memory.size := by
  have h0 : (UInt256.ofNat 0).toNat = 0 := uint256_ofNat_toNat 0 (by simp [UInt256.size])
  have hdata : (m.mstore (UInt256.ofNat 0) pkSeed).memory.data =
      m.memory.data.extract 0 0 ++ pkSeed.toByteArray.data ++
        m.memory.data.extract (0 + 32) m.memory.size := by
    rw [mstore_memory, h0]
    exact byteArray_write_overwrite pkSeed.toByteArray m.memory 0 32
      (uint256_toByteArray_size pkSeed).symm (by omega) hsize
  show (m.mstore (UInt256.ofNat 0) pkSeed).memory.data.size = m.memory.size
  rw [hdata]
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hps : pkSeed.toByteArray.data.size = 32 := uint256_toByteArray_size pkSeed
  simp only [Array.size_append, Array.size_extract]
  rw [hps]
  rw [show min m.memory.size m.memory.data.size = m.memory.size by rw [hmd]; simp]
  omega

/-- After `mstore(0x00,pkSeed); mstore(0x20,pkRoot)` on empty memory, the region
    `keccak256(0x00,0x40)` hashes is exactly `pkSeed ‖ pkRoot` (32+32 bytes). -/
theorem address_keccak_input
    (m : MachineState) (o0 o20 pkSeed pkRoot : UInt256)
    (hm : m.memory = ByteArray.empty) (h0 : o0.toNat = 0) (h20 : o20.toNat = 32) :
    (((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.readWithPadding 0 0x40).data
      = pkSeed.toByteArray.data ++ pkRoot.toByteArray.data := by
  have hmem : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory
      = ByteArray.write pkRoot.toByteArray 0
          (ByteArray.write pkSeed.toByteArray 0 ByteArray.empty 0 32) 32 32 := by
    rw [mstore_memory, mstore_memory, h0, h20, hm]
  have hdata : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.data
      = pkSeed.toByteArray.data ++ pkRoot.toByteArray.data := by
    rw [hmem]; exact two_word_writes pkSeed pkRoot
  have hps : pkSeed.toByteArray.data.size = 32 := uint256_toByteArray_size pkSeed
  have hpr : pkRoot.toByteArray.data.size = 32 := uint256_toByteArray_size pkRoot
  have hsize : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.size = 0x40 := by
    show ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.data.size = 0x40
    rw [hdata, Array.size_append]; omega
  rw [readWithPadding_exact _ 0x40 hsize.symm (by rw [hsize]; decide) (by rw [hsize]; decide),
      hdata]

/-- **Realistic** address-input lemma (matches the actual contract). `pkSeed` is
    already at `0x00` (from the Hmsg step) in a larger, already-populated memory;
    the contract does a single `mstore(0x20, pkRoot)` overwriting within bounds.
    Then `keccak256(0x00,0x40)` still reads exactly `pkSeed ‖ pkRoot`. -/
theorem address_keccak_input_overwrite
    (m : MachineState) (o20 pkSeed pkRoot : UInt256)
    (h20 : o20.toNat = 32)
    (hsize : 64 ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data) :
    ((m.mstore o20 pkRoot).memory.readWithPadding 0 0x40).data
      = pkSeed.toByteArray.data ++ pkRoot.toByteArray.data := by
  have hps : pkSeed.toByteArray.data.size = 32 := uint256_toByteArray_size pkSeed
  have hpr : pkRoot.toByteArray.data.size = 32 := uint256_toByteArray_size pkRoot
  have hdata : (m.mstore o20 pkRoot).memory.data
      = m.memory.data.extract 0 32 ++ pkRoot.toByteArray.data
          ++ m.memory.data.extract (32 + 32) m.memory.size := by
    rw [mstore_memory, h20]
    exact byteArray_write_overwrite pkRoot.toByteArray m.memory 32 32
      (uint256_toByteArray_size pkRoot).symm (by omega) (by omega)
  have hmsz : m.memory.data.size = m.memory.size := rfl
  have hsz : (m.mstore o20 pkRoot).memory.size = m.memory.size := by
    show (m.mstore o20 pkRoot).memory.data.size = m.memory.size
    rw [hdata]; simp only [Array.size_append, Array.size_extract]; omega
  rw [readWithPadding_prefix _ 0x40 (by rw [hsz]; omega) (by rw [hsz]; omega) (by decide),
      ByteArray.data_extract, hdata, hpk,
      extract_two_prefix _ _ _ 0x40 (by rw [hps, hpr])]

/-! ## Multi-word overwrite transcript inputs -/

/-- Hmsg input bytes after the real contract's five-word overwrite:
    `pkSeed ‖ r ‖ digest ‖ domain ‖ counter`. -/
theorem hmsg_keccak_input_overwrite
    (m : MachineState) (o0 o20 o40 o60 o80 pkSeed r digest domain counter : UInt256)
    (h0 : o0.toNat = 0) (h20 : o20.toNat = 32) (h40 : o40.toNat = 64)
    (h60 : o60.toNat = 96) (h80 : o80.toNat = 128)
    (hsize : HMsgHashLen ≤ m.memory.size) :
    (ByteArray.readWithPadding
        (((((m.mstore o0 pkSeed).mstore o20 r).mstore o40 digest).mstore o60 domain).mstore o80 counter).memory
        0 HMsgHashLen).data =
      concatData ([pkSeed, r, digest, domain, counter].map UInt256.toByteArray) := by
  let ws := ([pkSeed, r, digest, domain, counter].map UInt256.toByteArray)
  have hws : ∀ w ∈ ws, w.size = 32 := by
    dsimp [ws]
    exact uint256_word_list_size [pkSeed, r, digest, domain, counter]
  have hmem :
      (((((m.mstore o0 pkSeed).mstore o20 r).mstore o40 digest).mstore o60 domain).mstore o80 counter).memory =
        writeWords32At 0 ws m.memory := by
    dsimp [ws]
    simp [writeWords32At, mstore_memory, h0, h20, h40, h60, h80]
  have hread := writeWords32At_readWithPadding_data ws m.memory 0 hws
    (by simpa [ws] using hsize) (by simp [ws]) (by simp [ws])
  rw [hmem]
  rw [show HMsgHashLen = 32 * ws.length by simp [ws, HMsgHashLen]]
  exact hread

/-- Leaf-hash input bytes after writing the scratch transcript at `0x380`:
    `pkSeed ‖ ADRS ‖ sk`. -/
theorem leaf_keccak_input_overwrite
    (m : MachineState) (oScratch oAdrs oLeft pkSeed adrs sk : UInt256)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size) :
    (ByteArray.readWithPadding
        (((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sk).memory
        ScratchBase LeafHashLen).data =
      concatData ([pkSeed, adrs, sk].map UInt256.toByteArray) := by
  let ws := ([pkSeed, adrs, sk].map UInt256.toByteArray)
  have hws : ∀ w ∈ ws, w.size = 32 := by
    dsimp [ws]
    exact uint256_word_list_size [pkSeed, adrs, sk]
  have hmem :
      (((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sk).memory =
        writeWords32At ScratchBase ws m.memory := by
    dsimp [ws]
    simp [writeWords32At, mstore_memory, hScratch, hAdrs, hLeft,
      ScratchAdrsOffset, ScratchLeftOffset, ScratchBase]
  have hread := writeWords32At_readWithPadding_data ws m.memory ScratchBase hws
    (by simpa [ws] using hsize) (by simp [ws]) (by simp [ws])
  rw [hmem]
  rw [show LeafHashLen = 32 * ws.length by simp [ws, LeafHashLen]]
  exact hread

/-- Node-hash input bytes after writing the scratch transcript at `0x380`:
    `pkSeed ‖ ADRS ‖ left ‖ right`. -/
theorem node_keccak_input_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs left right : UInt256)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (ByteArray.readWithPadding
        ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft left).mstore oRight right).memory
        ScratchBase NodeHashLen).data =
      concatData ([pkSeed, adrs, left, right].map UInt256.toByteArray) := by
  let ws := ([pkSeed, adrs, left, right].map UInt256.toByteArray)
  have hws : ∀ w ∈ ws, w.size = 32 := by
    dsimp [ws]
    exact uint256_word_list_size [pkSeed, adrs, left, right]
  have hmem :
      ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft left).mstore oRight right).memory =
        writeWords32At ScratchBase ws m.memory := by
    dsimp [ws]
    simp [writeWords32At, mstore_memory, hScratch, hAdrs, hLeft, hRight,
      ScratchAdrsOffset, ScratchLeftOffset, ScratchRightOffset, ScratchBase]
  have hread := writeWords32At_readWithPadding_data ws m.memory ScratchBase hws
    (by simpa [ws] using hsize) (by simp [ws]) (by simp [ws])
  rw [hmem]
  rw [show NodeHashLen = 32 * ws.length by simp [ws, NodeHashLen]]
  exact hread

/-! ## Roots-compression transcript input -/

def rootsBufferValues (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256) :
    List UInt256 :=
  [pkSeed, rootsAdrs] ++ List.ofFn roots

def rootsBufferBytes (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256) :
    List ByteArray :=
  (rootsBufferValues pkSeed rootsAdrs roots).map UInt256.toByteArray

theorem rootsBufferBytes_size
    (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256) :
    32 * (rootsBufferBytes pkSeed rootsAdrs roots).length = RootsHashLen := by
  simp [rootsBufferBytes, rootsBufferValues, RootsHashLen, RealTrees, K]

/-- Writing 25 root values into the root buffer preserves the `pkSeed` prefix
    and establishes the exact root-buffer slice. This is the loop-invariant
    skeleton before proving that each root value is the FORS tree-climb result. -/
theorem root_writes_preserve_pk_and_set_roots
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length = RealTrees)
    (hsize : RootsHashLen ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data) :
    let afterRoots := mstoreWords32At RootBufferStart rootVals m
    afterRoots.memory.data.extract 0 32 = pkSeed.toByteArray.data ∧
      afterRoots.memory.data.extract RootBufferStart RootsHashLen =
        concatData (rootVals.map UInt256.toByteArray) := by
  dsimp
  let rootBytes := rootVals.map UInt256.toByteArray
  have hRHL : RootsHashLen = 864 := by decide
  have hRBS : RootBufferStart = 64 := rfl
  have hrootBytesLen : rootBytes.length = RealTrees := by
    dsimp [rootBytes]
    simpa using hlen
  have hrootBytesSize : (concatData rootBytes).size = 32 * rootBytes.length :=
    concatData_size rootBytes (by
      dsimp [rootBytes]
      exact uint256_word_list_size rootVals)
  have hrootBytesSize' : (concatData rootBytes).size = RootsHashLen - RootBufferStart := by
    rw [hrootBytesSize, hrootBytesLen]
    simp [RootsHashLen, RootBufferStart, RealTrees, K]
  have hrootMem : (mstoreWords32At RootBufferStart rootVals m).memory =
      writeWords32At RootBufferStart rootBytes m.memory := by
    dsimp [rootBytes]
    exact mstoreWords32At_memory rootVals m RootBufferStart (by
      rw [hlen]
      simp [RootBufferStart, UInt256.size, RealTrees, K])
  have hwriteData := writeWords32At_data rootBytes m.memory RootBufferStart
    (by
      dsimp [rootBytes]
      exact uint256_word_list_size rootVals)
    (by
      have hNeed : RootBufferStart + 32 * rootBytes.length = RootsHashLen := by
        rw [hrootBytesLen]
        simp [RootBufferStart, RootsHashLen, RealTrees, K]
      rw [hNeed]
      exact hsize)
  have hfinalData : (mstoreWords32At RootBufferStart rootVals m).memory.data =
      m.memory.data.extract 0 RootBufferStart ++ concatData rootBytes ++
        m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size := by
    rw [hrootMem]
    exact hwriteData
  have hprefSize : (m.memory.data.extract 0 RootBufferStart).size = RootBufferStart := by
    have hmd : m.memory.data.size = m.memory.size := rfl
    rw [Array.size_extract]
    rw [show min RootBufferStart m.memory.data.size = RootBufferStart by
      rw [hmd, hRBS]
      omega]
    simp
  constructor
  · rw [hfinalData]
    rw [show (m.memory.data.extract 0 RootBufferStart ++ concatData rootBytes ++
          m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size) =
        (m.memory.data.extract 0 RootBufferStart) ++
          (concatData rootBytes ++
            m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size) by
        rw [Array.append_assoc]]
    rw [Array.extract_append_left' (a := m.memory.data.extract 0 RootBufferStart)
      (b := concatData rootBytes ++
        m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size)
      (i := 0) (j := 32) (by rw [hprefSize]; simp [RootBufferStart])]
    have hx := extract_after_extract_window m.memory.data
      (start := 0) (stop := RootBufferStart) (off := 0) (len := 32)
      (by omega)
      (by
        have hmd : m.memory.data.size = m.memory.size := rfl
        rw [hmd, hRBS]
        omega)
      (by simp [RootBufferStart])
    simpa using hx.trans hpk
  · rw [hfinalData]
    let A := m.memory.data.extract 0 RootBufferStart
    let B := concatData rootBytes
    let C := m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size
    change (A ++ B ++ C).extract RootBufferStart RootsHashLen = concatData rootBytes
    have hA : A.size = RootBufferStart := by
      dsimp [A]
      exact hprefSize
    have hB : B.size = RootsHashLen - RootBufferStart := by
      dsimp [B]
      exact hrootBytesSize'
    rw [show RootBufferStart = A.size by rw [hA]]
    rw [show RootsHashLen = A.size + B.size by rw [hA, hB, hRHL, hRBS]]
    exact extract_middle _ _ _

/-- Prefix form of the root-buffer invariant. After writing any first `n ≤ 25`
    root words into `0x40 + 32*i`, the `pkSeed` prefix is preserved and the
    written root-buffer prefix contains exactly those `n` words. This is the
    induction target for the future `forEach t 25` proof. -/
theorem root_writes_preserve_pk_and_set_prefix
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length ≤ RealTrees)
    (hsize : RootBufferStart + 32 * rootVals.length ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data) :
    let afterRoots := mstoreWords32At RootBufferStart rootVals m
    afterRoots.memory.data.extract 0 32 = pkSeed.toByteArray.data ∧
      afterRoots.memory.data.extract RootBufferStart
          (RootBufferStart + 32 * rootVals.length) =
        concatData (rootVals.map UInt256.toByteArray) := by
  dsimp
  let rootBytes := rootVals.map UInt256.toByteArray
  have hRBS : RootBufferStart = 64 := rfl
  have hrootBytesLen : rootBytes.length = rootVals.length := by
    dsimp [rootBytes]
    simp
  have hrootBytesSize : (concatData rootBytes).size = 32 * rootBytes.length :=
    concatData_size rootBytes (by
      dsimp [rootBytes]
      exact uint256_word_list_size rootVals)
  have hrootMem : (mstoreWords32At RootBufferStart rootVals m).memory =
      writeWords32At RootBufferStart rootBytes m.memory := by
    dsimp [rootBytes]
    exact mstoreWords32At_memory rootVals m RootBufferStart (by
      have hReal : RealTrees = 25 := rfl
      rw [hReal] at hlen
      simp [RootBufferStart, UInt256.size]
      omega)
  have hwriteData := writeWords32At_data rootBytes m.memory RootBufferStart
    (by
      dsimp [rootBytes]
      exact uint256_word_list_size rootVals)
    (by
      rw [hrootBytesLen]
      exact hsize)
  have hfinalData : (mstoreWords32At RootBufferStart rootVals m).memory.data =
      m.memory.data.extract 0 RootBufferStart ++ concatData rootBytes ++
        m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size := by
    rw [hrootMem]
    exact hwriteData
  have hprefSize : (m.memory.data.extract 0 RootBufferStart).size = RootBufferStart := by
    have hmd : m.memory.data.size = m.memory.size := rfl
    rw [Array.size_extract]
    rw [show min RootBufferStart m.memory.data.size = RootBufferStart by
      rw [hmd, hRBS]
      omega]
    simp
  constructor
  · rw [hfinalData]
    rw [show (m.memory.data.extract 0 RootBufferStart ++ concatData rootBytes ++
          m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size) =
        (m.memory.data.extract 0 RootBufferStart) ++
          (concatData rootBytes ++
            m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size) by
        rw [Array.append_assoc]]
    rw [Array.extract_append_left' (a := m.memory.data.extract 0 RootBufferStart)
      (b := concatData rootBytes ++
        m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size)
      (i := 0) (j := 32) (by rw [hprefSize]; simp [RootBufferStart])]
    have hx := extract_after_extract_window m.memory.data
      (start := 0) (stop := RootBufferStart) (off := 0) (len := 32)
      (by omega)
      (by
        have hmd : m.memory.data.size = m.memory.size := rfl
        rw [hmd, hRBS]
        omega)
      (by simp [RootBufferStart])
    simpa using hx.trans hpk
  · rw [hfinalData]
    let A := m.memory.data.extract 0 RootBufferStart
    let B := concatData rootBytes
    let C := m.memory.data.extract (RootBufferStart + 32 * rootBytes.length) m.memory.size
    change (A ++ B ++ C).extract RootBufferStart
      (RootBufferStart + 32 * rootVals.length) = concatData rootBytes
    have hA : A.size = RootBufferStart := by
      dsimp [A]
      exact hprefSize
    have hB : B.size = 32 * rootVals.length := by
      dsimp [B]
      rw [hrootBytesSize, hrootBytesLen]
    rw [show RootBufferStart = A.size by rw [hA]]
    rw [show 32 * rootVals.length = B.size by rw [hB]]
    exact extract_middle _ _ _

/-- Prefix root-loop invariant after the contract's initial
    `mstore(0x00, pkSeed)`. This is the form needed at the start of the actual
    `forEach t 25` proof. -/
theorem roots_loop_buffer_prefix_after_init
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length ≤ RealTrees)
    (hsize : RootBufferStart + 32 * rootVals.length ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart rootVals afterPk
    afterRoots.memory.data.extract 0 32 = pkSeed.toByteArray.data ∧
      afterRoots.memory.data.extract RootBufferStart
          (RootBufferStart + 32 * rootVals.length) =
        concatData (rootVals.map UInt256.toByteArray) := by
  dsimp
  have h32 : 32 ≤ m.memory.size := by
    have hRBS : RootBufferStart = 64 := rfl
    omega
  apply root_writes_preserve_pk_and_set_prefix
  · exact hlen
  · rw [pk_seed_mstore_size m pkSeed h32]
    exact hsize
  · exact pk_seed_mstore_prefix m pkSeed h32

/-- The partial root-loop prefix writes preserve memory size after pkSeed
    initialization. -/
theorem roots_loop_buffer_prefix_size_after_init
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length ≤ RealTrees)
    (hsize : RootBufferStart + 32 * rootVals.length ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart rootVals afterPk
    afterRoots.memory.size = m.memory.size := by
  dsimp
  have h32 : 32 ≤ m.memory.size := by
    have hRBS : RootBufferStart = 64 := rfl
    omega
  have hPkSize := pk_seed_mstore_size m pkSeed h32
  rw [mstoreWords32At_size rootVals (m.mstore (UInt256.ofNat 0) pkSeed) RootBufferStart]
  · exact hPkSize
  · have hReal : RealTrees = 25 := rfl
    rw [hReal] at hlen
    simp [RootBufferStart, UInt256.size]
    omega
  · rw [hPkSize]
    exact hsize

/-- Combined root-buffer setup target: `mstore(0x00, pkSeed)` followed by the 25
    contiguous root-slot writes establishes exactly the two post-loop premises
    expected by `roots_keccak_input_from_buffer`. -/
theorem roots_loop_buffer_post_after_init
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length = RealTrees)
    (hsize : RootsHashLen ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart rootVals afterPk
    afterRoots.memory.data.extract 0 32 = pkSeed.toByteArray.data ∧
      afterRoots.memory.data.extract RootBufferStart RootsHashLen =
        concatData (rootVals.map UInt256.toByteArray) := by
  dsimp
  have h32 : 32 ≤ m.memory.size := by
    have hRHL : RootsHashLen = 864 := by decide
    omega
  apply root_writes_preserve_pk_and_set_roots
  · exact hlen
  · rw [pk_seed_mstore_size m pkSeed h32]
    exact hsize
  · exact pk_seed_mstore_prefix m pkSeed h32

/-- Indexed specialization of `roots_loop_buffer_post_after_init`, matching the
    `TreeIndex → UInt256` shape consumed by the roots-compression bridge. -/
theorem roots_loop_buffer_post_after_init_indexed
    (m : MachineState) (pkSeed : UInt256) (roots : TreeIndex → UInt256)
    (hsize : RootsHashLen ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
    afterRoots.memory.data.extract 0 32 = pkSeed.toByteArray.data ∧
      afterRoots.memory.data.extract RootBufferStart RootsHashLen =
        concatData ((List.ofFn roots).map UInt256.toByteArray) := by
  exact roots_loop_buffer_post_after_init m pkSeed (List.ofFn roots)
    (by simp [RealTrees, K]) hsize

/-- The same root-buffer setup preserves total memory size. This supplies the
    in-bounds premise needed for the final roots-compression keccak call. -/
theorem roots_loop_buffer_size_after_init
    (m : MachineState) (pkSeed : UInt256) (rootVals : List UInt256)
    (hlen : rootVals.length = RealTrees)
    (hsize : RootsHashLen ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart rootVals afterPk
    afterRoots.memory.size = m.memory.size := by
  dsimp
  have h32 : 32 ≤ m.memory.size := by
    have hRHL : RootsHashLen = 864 := by decide
    omega
  have hPkSize := pk_seed_mstore_size m pkSeed h32
  rw [mstoreWords32At_size rootVals (m.mstore (UInt256.ofNat 0) pkSeed) RootBufferStart]
  · exact hPkSize
  · rw [hlen]
    simp [RootBufferStart, UInt256.size, RealTrees, K]
  · rw [hPkSize]
    have hNeed : RootBufferStart + 32 * rootVals.length = RootsHashLen := by
      rw [hlen]
      simp [RootBufferStart, RootsHashLen, RealTrees, K]
    rw [hNeed]
    exact hsize

/-- Indexed specialization of `roots_loop_buffer_size_after_init`. -/
theorem roots_loop_buffer_size_after_init_indexed
    (m : MachineState) (pkSeed : UInt256) (roots : TreeIndex → UInt256)
    (hsize : RootsHashLen ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
    afterRoots.memory.size = m.memory.size := by
  exact roots_loop_buffer_size_after_init m pkSeed (List.ofFn roots)
    (by simp [RealTrees, K]) hsize

/-- Roots-compression input bytes after writing `pkSeed`, the FORS-roots ADRS
    word, and the 25 tree roots contiguously into `0x00..0x35f`. This proves the
    27-word roots input shape, but intentionally leaves the future tree loop proof
    to show where each `roots i` value comes from. -/
theorem roots_keccak_input_overwrite
    (m : MachineState) (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (hsize : RootsHashLen ≤ m.memory.size) :
    (ByteArray.readWithPadding
        (mstoreWords32At 0 (rootsBufferValues pkSeed rootsAdrs roots) m).memory
        0 RootsHashLen).data =
      concatData (rootsBufferBytes pkSeed rootsAdrs roots) := by
  let vals := rootsBufferValues pkSeed rootsAdrs roots
  let ws := rootsBufferBytes pkSeed rootsAdrs roots
  have hws : ∀ w ∈ ws, w.size = 32 := by
    dsimp [ws, rootsBufferBytes, vals]
    exact uint256_word_list_size (rootsBufferValues pkSeed rootsAdrs roots)
  have hmem : (mstoreWords32At 0 vals m).memory = writeWords32At 0 ws m.memory := by
    dsimp [vals, ws, rootsBufferBytes]
    exact mstoreWords32At_memory (rootsBufferValues pkSeed rootsAdrs roots) m 0 (by
      simp [rootsBufferValues, UInt256.size, RealTrees, K])
  have hlen : 32 * ws.length = RootsHashLen := by
    dsimp [ws]
    exact rootsBufferBytes_size pkSeed rootsAdrs roots
  have hread := writeWords32At_readWithPadding_data ws m.memory 0 hws
    (by rw [hlen]; simpa using hsize)
    (by simp [ws, rootsBufferBytes, rootsBufferValues])
    (by rw [hlen]; decide)
  rw [hmem]
  rw [← hlen]
  exact hread

/-- The real `compressRoots` local choreography: assuming the full loop has
    already established `pkSeed` at `0x00` and the 25-root buffer at
    `0x40..0x35f`, the final `mstore(0x20, rootsADRS)` makes
    `keccak256(0,0x360)` read exactly
    `pkSeed ‖ ADRS_roots ‖ root_0 ‖ … ‖ root_24`.

    This is the handoff theorem for the future tree-loop proof: that proof only
    needs to establish the `hpk` and `hroots` premises for its post-loop state. -/
theorem roots_keccak_input_from_buffer
    (m : MachineState) (o20 pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (h20 : o20.toNat = RootsAdrsOffset)
    (hsize : RootsHashLen ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data)
    (hroots : m.memory.data.extract RootBufferStart RootsHashLen =
      concatData ((List.ofFn roots).map UInt256.toByteArray)) :
    ((m.mstore o20 rootsAdrs).memory.readWithPadding 0 RootsHashLen).data =
      concatData (rootsBufferBytes pkSeed rootsAdrs roots) := by
  have hRHL : RootsHashLen = 864 := by decide
  have hRBS : RootBufferStart = 64 := rfl
  have h64 : 64 ≤ m.memory.size := by omega
  let rootBytes := (List.ofFn roots).map UInt256.toByteArray
  have hrootBytesSize : (concatData rootBytes).size = 32 * rootBytes.length :=
    concatData_size rootBytes (uint256_word_list_size (List.ofFn roots))
  have hrootBytesLen : rootBytes.length = RealTrees := by
    dsimp [rootBytes]
    simp [RealTrees, K]
  have hrootBytesSize' : (concatData rootBytes).size = RootsHashLen - 64 := by
    rw [hrootBytesSize, hrootBytesLen]
    simp [RootsHashLen, RealTrees, K]
  have hra : rootsAdrs.toByteArray.data.size = 32 := uint256_toByteArray_size rootsAdrs
  have hdata : (m.mstore o20 rootsAdrs).memory.data =
      m.memory.data.extract 0 32 ++ rootsAdrs.toByteArray.data ++
        m.memory.data.extract (32 + 32) m.memory.size := by
    rw [mstore_memory, h20]
    exact byteArray_write_overwrite rootsAdrs.toByteArray m.memory 32 32
      (uint256_toByteArray_size rootsAdrs).symm (by omega) (by omega)
  have hsz : (m.mstore o20 rootsAdrs).memory.size = m.memory.size := by
    show (m.mstore o20 rootsAdrs).memory.data.size = m.memory.size
    rw [hdata]
    have hmd : m.memory.data.size = m.memory.size := rfl
    rw [Array.size_append, Array.size_append, hra]
    simp only [Array.size_extract]
    rw [show min 32 m.memory.data.size = 32 by rw [hmd]; omega]
    rw [show min m.memory.size m.memory.data.size = m.memory.size by rw [hmd]; simp]
    omega
  have htailPrefix :
      (m.memory.data.extract (32 + 32) m.memory.size).extract 0 (RootsHashLen - 64) =
        concatData rootBytes := by
    have hmd : m.memory.data.size = m.memory.size := rfl
    have hx := extract_after_extract_window m.memory.data
      (start := RootBufferStart) (stop := m.memory.size)
      (off := 0) (len := RootsHashLen - 64)
      (by omega) (by rw [hmd]) (by omega)
    have hprefix :
        (m.memory.data.extract RootBufferStart m.memory.size).extract 0 (RootsHashLen - 64) =
          m.memory.data.extract RootBufferStart RootsHashLen := by
      simpa [hRHL, hRBS] using hx
    rw [show 32 + 32 = RootBufferStart by rw [hRBS]]
    rw [hprefix, hroots]
  rw [readWithPadding_prefix _ RootsHashLen (by rw [hsz]; exact hsize)
      (by rw [hsz]; omega) (by decide),
    ByteArray.data_extract, hdata]
  have hpfxSize : (m.memory.data.extract 0 32).size = 32 := by
    have hmd : m.memory.data.size = m.memory.size := rfl
    rw [Array.size_extract]
    rw [show min 32 m.memory.data.size = 32 by rw [hmd]; omega]
  have hstop :
      RootsHashLen =
        (m.memory.data.extract 0 32).size + rootsAdrs.toByteArray.data.size +
          (RootsHashLen - 64) := by
    rw [hpfxSize, hra]
    omega
  rw [hstop]
  rw [extract_three_prefix _ _ _ (RootsHashLen - 64)]
  rw [hpk, htailPrefix]
  simp [rootsBufferBytes, rootsBufferValues, rootBytes, concatData]

end NiceTry.Fors.Bridge
