import NiceTry.Fors.Bridge.TreeNode
import NiceTry.Fors.Bridge.TreeMemory

/-!
# Tree-loop per-hash value discharge (leaf template)

Connects the **executed** loop-body states (`TreeLeaf.lean`/`TreeNode.lean`) to
the **extract-based** derivation lemmas (`TreeMemory.lean`):

* `tree_leaf_node_value_of_extract` — the A2 leaf value theorem upgraded to the
  extract-based invariant: with `pkSeed`'s bytes at `[0x380, 0x3a0)` of the
  entry memory (and the window in bounds), the value the leaf prefix binds to
  `usr_node` is the model `leafHash`. The extract facts for the two leaf
  `mstore`s are discharged by `mstore_extract_{self,disjoint}`.
* The `xor` swap-offset facts (`xor_3c0_zero`/`xor_3c0_32`/…): with the
  selector `usr_s_k ∈ {0, 32}`, the node/sibling stores land on
  `0x3c0`/`0x3e0` straight or swapped — the case split feeding
  `node_derivation_climbLevel_{even,odd}_of_extracts` for the five node levels
  (same discharge pattern as the leaf, on `treeAfterSibling<k>`'s memory).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-! ## Swap-offset facts -/

theorem xor_3c0_zero :
    (UInt256.ofNat 0x3c0).xor (UInt256.ofNat 0) = UInt256.ofNat 0x3c0 := by decide

theorem xor_3e0_zero :
    (UInt256.ofNat 0x3e0).xor (UInt256.ofNat 0) = UInt256.ofNat 0x3e0 := by decide

theorem xor_3c0_32 :
    (UInt256.ofNat 0x3c0).xor (UInt256.ofNat 32) = UInt256.ofNat 0x3e0 := by decide

theorem xor_3e0_32 :
    (UInt256.ofNat 0x3e0).xor (UInt256.ofNat 32) = UInt256.ofNat 0x3c0 := by decide

/-! ## The leaf value, from the extract-based invariant -/

/-- **Leaf value discharge (extract-based).** With `pkSeed`'s bytes sitting at
    `[0x380, 0x3a0)` of the entry memory and the scratch window in bounds, the
    leaf prefix binds `usr_node` to the model `leafHash`. `hadrs` is the
    ADRS-word arithmetic the loop invariant supplies (A4). -/
theorem tree_leaf_node_value_of_extract
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256) (tree leafIdx : Nat)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x400 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hadrs : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat = shapeLeafAdrsWord tree leafIdx) :
    (treeLeafNodeWord (.Ok ss vs)).toNat
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx)
          (treeSkWord (.Ok ss vs)).toNat := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  -- bounds for the two leaf stores
  have hb1 : (UInt256.ofNat 0x3a0).toNat + 32
      ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size := by
    rw [h3a0]; omega
  have hsz1 : ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
        (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
          (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)).memory.size
      = (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size :=
    mstore_memory_size _ _ _ hb1
  have hb2 : (UInt256.ofNat 0x3c0).toNat + 32
      ≤ ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
          (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
            (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)).memory.size := by
    rw [h3c0, hsz1]; omega
  have hsz2 : (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
        (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
          (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)).mstore (UInt256.ofNat 0x3c0)
        (treeSkWord (.Ok ss vs))).memory.size
      = ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
          (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
            (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)).memory.size :=
    mstore_memory_size _ _ _ hb2
  unfold treeLeafNodeWord
  rw [treeAfterLeafSk_getElem, hlen, masked_keccak_toNat,
    treeAfterLeafSk_toMachineState,
    show (UInt256.ofNat 0x380).toNat = ScratchBase from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 96).toNat = LeafHashLen from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  refine leaf_derivation_of_extracts _ pkSeed
    (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
      (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)
    (treeSkWord (.Ok ss vs)) tree leafIdx hadrs ?_ ?_ ?_ ?_
  · -- window in bounds after both stores
    rw [hsz2, hsz1]
    unfold ScratchBase LeafHashLen
    omega
  · -- pkSeed slot untouched by both stores
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (Or.inl (by rw [h3c0]; omega)),
      mstore_extract_disjoint _ _ _ _ _ hb1 (Or.inl (by rw [h3a0]))]
    exact hpk
  · -- the ADRS slot: written by store 1, untouched by store 2
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (Or.inl (by rw [h3c0]))]
    have h := mstore_extract_self (EvmYul.Yul.State.Ok ss vs).toMachineState
      (UInt256.ofNat 0x3a0)
      (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!) hb1
    rw [h3a0] at h
    exact h
  · -- the sk slot: written by store 2
    have h := mstore_extract_self
      ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
        (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
          (EvmYul.Yul.State.Ok ss vs)[dCursorId]!))
      (UInt256.ofNat 0x3c0) (treeSkWord (.Ok ss vs)) hb2
    rw [h3c0] at h
    exact h

end NiceTry.Fors.Bridge
