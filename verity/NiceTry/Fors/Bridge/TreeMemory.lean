import NiceTry.Fors.Bridge.AddressShape

/-!
# Extract-based scratch-window calculus (the tree-loop value layer)

The executed loop body (`TreeLeaf.lean`/`TreeNode.lean`) produces long `mstore`
chains; the proved shape lemmas (`AddressShape.lean`) consume canonical 3/4-store
chains. Rather than re-factoring chains (overwrite collapse + disjoint commute),
this file works with **extract facts**: what each 32-byte slot of the scratch
window `[0x380, 0x400)` holds.

* `mstore` extract algebra (in-bounds): `mstore_memory_size`,
  `mstore_extract_disjoint`, `mstore_extract_self` — chase a slot's content
  through any store sequence.
* Window reads: `scratch_leaf_read_of_extracts` / `scratch_node_read_of_extracts`
  — the keccak input bytes from per-slot extract facts.
* Derivation wrappers: `leaf_derivation_of_extracts`,
  `node_derivation_of_extracts`, and the `climbLevel` even/odd forms — the
  extract-based counterparts of the `*_derivation_eq_*_overwrite` lemmas.

This also makes the A4 loop invariant robust: `pkSeed@0x380` is the extract fact
`m.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data`, preserved across
iterations by `mstore_extract_disjoint` (nothing in the body writes `0x380`).
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-- Concrete-offset `toNat` bridge (public twin of `EvmMemory`'s private lemma,
    for the value-layer files). -/
theorem uint256_ofNat_toNat_of_lt (k : Nat) (h : k < EvmYul.UInt256.size) :
    (UInt256.ofNat k).toNat = k := by
  unfold UInt256.ofNat UInt256.toNat
  rw [Fin.ofNat_eq_cast]
  exact Fin.val_cast_of_lt h

/-! ## In-bounds `mstore` extract algebra -/

/-- An in-bounds `mstore` splices the word into the memory bytes. -/
private theorem mstore_data_splice (m : MachineState) (a v : UInt256)
    (hb : a.toNat + 32 ≤ m.memory.size) :
    (m.mstore a v).memory.data
      = m.memory.data.extract 0 a.toNat ++ v.toByteArray.data
          ++ m.memory.data.extract (a.toNat + 32) m.memory.size := by
  rw [mstore_memory]
  exact byteArray_write_overwrite v.toByteArray m.memory a.toNat 32
    (uint256_toByteArray_size v).symm (by omega) hb

/-- An in-bounds `mstore` preserves the memory size. -/
theorem mstore_memory_size (m : MachineState) (a v : UInt256)
    (hb : a.toNat + 32 ≤ m.memory.size) :
    (m.mstore a v).memory.size = m.memory.size := by
  show (m.mstore a v).memory.data.size = m.memory.size
  rw [mstore_data_splice m a v hb]
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hvs : v.toByteArray.data.size = 32 := uint256_toByteArray_size v
  simp only [Array.size_append, Array.size_extract]
  omega

/-- An extract disjoint from the written window is unchanged by an in-bounds
    `mstore`. -/
theorem mstore_extract_disjoint (m : MachineState) (a v : UInt256) (lo hi : Nat)
    (hb : a.toNat + 32 ≤ m.memory.size)
    (hdisj : hi ≤ a.toNat ∨ a.toNat + 32 ≤ lo) :
    (m.mstore a v).memory.data.extract lo hi = m.memory.data.extract lo hi := by
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hvs : v.toByteArray.data.size = 32 := uint256_toByteArray_size v
  have hA : (m.memory.data.extract 0 a.toNat).size = a.toNat := by
    simp only [Array.size_extract]; omega
  have hAw : (m.memory.data.extract 0 a.toNat ++ v.toByteArray.data).size
      = a.toNat + 32 := by
    simp only [Array.size_append, hA, hvs]
  rw [mstore_data_splice m a v hb]
  apply Array.ext
  · simp only [Array.size_extract, Array.size_append, hA, hvs]
    omega
  · intro i h1 h2
    simp only [Array.size_extract] at h2
    rw [Array.getElem_extract, Array.getElem_extract]
    rcases hdisj with hlt | hge
    · -- the slot lies before the write: read from the untouched prefix
      have hiA : lo + i < a.toNat := by omega
      rw [Array.getElem_append_left (show lo + i
          < (m.memory.data.extract 0 a.toNat ++ v.toByteArray.data).size by
        rw [hAw]; omega)]
      rw [Array.getElem_append_left (show lo + i
          < (m.memory.data.extract 0 a.toNat).size by rw [hA]; omega)]
      rw [Array.getElem_extract]
      congr 1
      omega
    · -- the slot lies after the write: read from the untouched suffix
      have hiC : a.toNat + 32 ≤ lo + i := by omega
      rw [Array.getElem_append_right (show
          (m.memory.data.extract 0 a.toNat ++ v.toByteArray.data).size ≤ lo + i by
        rw [hAw]; omega)]
      simp only [hAw]
      rw [Array.getElem_extract]
      congr 1
      omega

/-- The extract of exactly the written window is the stored word. -/
theorem mstore_extract_self (m : MachineState) (a v : UInt256)
    (hb : a.toNat + 32 ≤ m.memory.size) :
    (m.mstore a v).memory.data.extract a.toNat (a.toNat + 32)
      = v.toByteArray.data := by
  have hA : (m.memory.data.extract 0 a.toNat).size = a.toNat := by
    have hmd : m.memory.data.size = m.memory.size := rfl
    simp only [Array.size_extract]; omega
  have hvs : v.toByteArray.data.size = 32 := uint256_toByteArray_size v
  have h := extract_middle (m.memory.data.extract 0 a.toNat) v.toByteArray.data
    (m.memory.data.extract (a.toNat + 32) m.memory.size)
  rw [hA, hvs] at h
  rw [mstore_data_splice m a v hb]
  exact h

/-! ## Window reads from extract facts -/

/-- Splitting an extract at an interior point. -/
theorem extract_split {α} (xs : Array α) (i j k : Nat)
    (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ xs.size) :
    xs.extract i k = xs.extract i j ++ xs.extract j k := by
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract]
    omega
  · intro t h1 h2
    simp only [Array.size_extract] at h1
    rw [Array.getElem_extract]
    by_cases ht : t < j - i
    · rw [Array.getElem_append_left (show t < (xs.extract i j).size by
        simp only [Array.size_extract]; omega)]
      rw [Array.getElem_extract]
    · rw [Array.getElem_append_right (show (xs.extract i j).size ≤ t by
        simp only [Array.size_extract]; omega)]
      rw [Array.getElem_extract]
      congr 1
      simp only [Array.size_extract]
      omega

/-- The 96-byte leaf window `[0x380, 0x3e0)` as three extracted words. -/
theorem scratch_leaf_read_of_extracts (m : MachineState) (w0 w1 w2 : UInt256)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = w0.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = w1.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = w2.toByteArray.data) :
    (ByteArray.readWithPadding m.memory ScratchBase LeafHashLen).data
      = concatData ([w0, w1, w2].map UInt256.toByteArray) := by
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hsz : (0x3e0 : Nat) ≤ m.memory.data.size := by
    unfold ScratchBase LeafHashLen at hsize
    omega
  rw [readWithPadding_window _ ScratchBase LeafHashLen hsize (by decide) (by decide)]
  rw [ByteArray.data_extract]
  show m.memory.data.extract 0x380 0x3e0 = _
  rw [extract_split m.memory.data 0x380 0x3a0 0x3e0 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x3a0 0x3c0 0x3e0 (by omega) (by omega) hsz,
      h0, h1, h2]
  simp [concatData]

/-- The 128-byte node window `[0x380, 0x400)` as four extracted words. -/
theorem scratch_node_read_of_extracts (m : MachineState) (w0 w1 w2 w3 : UInt256)
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = w0.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = w1.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = w2.toByteArray.data)
    (h3 : m.memory.data.extract 0x3e0 0x400 = w3.toByteArray.data) :
    (ByteArray.readWithPadding m.memory ScratchBase NodeHashLen).data
      = concatData ([w0, w1, w2, w3].map UInt256.toByteArray) := by
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hsz : (0x400 : Nat) ≤ m.memory.data.size := by
    unfold ScratchBase NodeHashLen at hsize
    omega
  rw [readWithPadding_window _ ScratchBase NodeHashLen hsize (by decide) (by decide)]
  rw [ByteArray.data_extract]
  show m.memory.data.extract 0x380 0x400 = _
  rw [extract_split m.memory.data 0x380 0x3a0 0x400 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x3a0 0x3c0 0x400 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x3c0 0x3e0 0x400 (by omega) (by omega) hsz,
      h0, h1, h2, h3]
  simp [concatData]

/-! ## Extract-based derivation lemmas -/

/-- Leaf derivation from per-slot extract facts. -/
theorem leaf_derivation_of_extracts
    (m : MachineState) (pkSeed adrs sk : UInt256) (tree leafIdx : Nat)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree leafIdx)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = adrs.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = sk.toByteArray.data) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding m.memory ScratchBase LeafHashLen)))
        &&& NMaskWord
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx) sk.toNat :=
  evm_keccak_leaf _ pkSeed adrs sk tree leafIdx hadrs
    (scratch_leaf_read_of_extracts m pkSeed adrs sk hsize h0 h1 h2)

/-- Node derivation from per-slot extract facts. -/
theorem node_derivation_of_extracts
    (m : MachineState) (pkSeed adrs left right : UInt256)
    (tree height parentIdx : Nat)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height parentIdx)
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = adrs.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = left.toByteArray.data)
    (h3 : m.memory.data.extract 0x3e0 0x400 = right.toByteArray.data) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding m.memory ScratchBase NodeHashLen)))
        &&& NMaskWord
      = nodeHash pkSeed.toNat (nodeAdrs tree height parentIdx)
          left.toNat right.toNat :=
  evm_keccak_node _ pkSeed adrs left right tree height parentIdx hadrs
    (scratch_node_read_of_extracts m pkSeed adrs left right hsize h0 h1 h2 h3)

/-- Even-branch `climbLevel` from extract facts: the current node sits in the
    left slot (`0x3c0`), the auth sibling in the right slot (`0x3e0`). -/
theorem node_derivation_climbLevel_even_of_extracts
    (m : MachineState) (pkSeed adrs node sibling : UInt256)
    (tree height pathIdx : Nat)
    (hEven : pathIdx % 2 = 0)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = adrs.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = node.toByteArray.data)
    (h3 : m.memory.data.extract 0x3e0 0x400 = sibling.toByteArray.data) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding m.memory ScratchBase NodeHashLen)))
        &&& NMaskWord
      = climbLevel pkSeed.toNat tree height pathIdx node.toNat sibling.toNat := by
  rw [node_derivation_of_extracts m pkSeed adrs node sibling tree height (pathIdx / 2)
    hadrs hsize h0 h1 h2 h3]
  simp [climbLevel, hEven]

/-- Odd-branch `climbLevel` from extract facts: the auth sibling sits in the
    left slot (`0x3c0`), the current node in the right slot (`0x3e0`). -/
theorem node_derivation_climbLevel_odd_of_extracts
    (m : MachineState) (pkSeed adrs node sibling : UInt256)
    (tree height pathIdx : Nat)
    (hOdd : pathIdx % 2 ≠ 0)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (h1 : m.memory.data.extract 0x3a0 0x3c0 = adrs.toByteArray.data)
    (h2 : m.memory.data.extract 0x3c0 0x3e0 = sibling.toByteArray.data)
    (h3 : m.memory.data.extract 0x3e0 0x400 = node.toByteArray.data) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding m.memory ScratchBase NodeHashLen)))
        &&& NMaskWord
      = climbLevel pkSeed.toNat tree height pathIdx node.toNat sibling.toNat := by
  rw [node_derivation_of_extracts m pkSeed adrs sibling node tree height (pathIdx / 2)
    hadrs hsize h0 h1 h2 h3]
  simp [climbLevel, hOdd]

end NiceTry.Fors.Bridge
