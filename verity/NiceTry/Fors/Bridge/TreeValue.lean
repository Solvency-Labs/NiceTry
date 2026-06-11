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

/-! ## Generic chain-value lemmas (boundary-tolerant)

Each level's keccak runs over a canonical 2/3-store chain on its entry memory
`M`. These lemmas carry all the extract/bounds work once; the per-level
discharges below are thin wrappers. The size hypotheses match iteration 0
exactly (loop entry leaves `size = 0x3a0`; the leaf prefix grows it to
`0x3e0`; the first node level reaches `0x400`). -/

/-- Masked keccak over the leaf chain `ADRS@0x3a0, sk@0x3c0` = `leafHash`. -/
theorem masked_keccak_leaf_chain_value
    (M : MachineState) (pkSeed adrsW skW : UInt256) (tree leafIdx : Nat)
    (hadrs : adrsW.toNat = shapeLeafAdrsWord tree leafIdx)
    (hpk : M.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (hsize : 0x3a0 ≤ M.memory.size) :
    ((((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3c0) skW).keccak256
        (UInt256.ofNat 0x380) (UInt256.ofNat 96)).1.land
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx) skW.toNat := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have hb1 : (UInt256.ofNat 0x3a0).toNat ≤ M.memory.size := by rw [h3a0]; omega
  have hsz1 := mstore_memory_size' M (UInt256.ofNat 0x3a0) adrsW hb1
  rw [h3a0] at hsz1
  have hb2 : (UInt256.ofNat 0x3c0).toNat
      ≤ (M.mstore (UInt256.ofNat 0x3a0) adrsW).memory.size := by
    rw [h3c0, hsz1]; omega
  have hsz2 := mstore_memory_size'
    (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3c0) skW hb2
  rw [h3c0, hsz1] at hsz2
  rw [masked_keccak_toNat,
    show (UInt256.ofNat 0x380).toNat = ScratchBase from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 96).toNat = LeafHashLen from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  refine leaf_derivation_of_extracts _ pkSeed adrsW skW tree leafIdx hadrs ?_ ?_ ?_ ?_
  · rw [hsz2]; unfold ScratchBase LeafHashLen; omega
  · rw [mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0]; omega),
      mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0])]
    exact hpk
  · rw [mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0])]
    have h := mstore_extract_self' M (UInt256.ofNat 0x3a0) adrsW hb1
    rw [h3a0] at h
    exact h
  · have h := mstore_extract_self'
      (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3c0) skW hb2
    rw [h3c0] at h
    exact h

/-- Masked keccak over the even node chain `ADRS@0x3a0, node@0x3c0, sib@0x3e0`
    = `climbLevel` (even branch). -/
theorem masked_keccak_node_chain_value_even
    (M : MachineState) (pkSeed adrsW nodeW sibW : UInt256)
    (tree height pathIdx : Nat)
    (hEven : pathIdx % 2 = 0)
    (hadrs : adrsW.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hpk : M.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (hsize : 0x3e0 ≤ M.memory.size) :
    (((((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3c0) nodeW).mstore
        (UInt256.ofNat 0x3e0) sibW).keccak256
        (UInt256.ofNat 0x380) (UInt256.ofNat 128)).1.land
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = climbLevel pkSeed.toNat tree height pathIdx nodeW.toNat sibW.toNat := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3e0 : (UInt256.ofNat 0x3e0).toNat = 0x3e0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have hb1 : (UInt256.ofNat 0x3a0).toNat ≤ M.memory.size := by rw [h3a0]; omega
  have hsz1 := mstore_memory_size' M (UInt256.ofNat 0x3a0) adrsW hb1
  rw [h3a0] at hsz1
  have hb2 : (UInt256.ofNat 0x3c0).toNat
      ≤ (M.mstore (UInt256.ofNat 0x3a0) adrsW).memory.size := by
    rw [h3c0, hsz1]; omega
  have hsz2 := mstore_memory_size'
    (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3c0) nodeW hb2
  rw [h3c0, hsz1] at hsz2
  have hb3 : (UInt256.ofNat 0x3e0).toNat
      ≤ ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore
          (UInt256.ofNat 0x3c0) nodeW).memory.size := by
    rw [h3e0, hsz2]; omega
  have hsz3 := mstore_memory_size'
    ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3c0) nodeW)
    (UInt256.ofNat 0x3e0) sibW hb3
  rw [h3e0, hsz2] at hsz3
  rw [masked_keccak_toNat,
    show (UInt256.ofNat 0x380).toNat = ScratchBase from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 128).toNat = NodeHashLen from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  refine node_derivation_climbLevel_even_of_extracts _ pkSeed adrsW nodeW sibW
    tree height pathIdx hEven hadrs ?_ ?_ ?_ ?_ ?_
  · rw [hsz3]; unfold ScratchBase NodeHashLen; omega
  · rw [mstore_extract_below' _ _ _ _ _ hb3 (by rw [h3e0]; omega),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0]; omega),
      mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0])]
    exact hpk
  · rw [mstore_extract_below' _ _ _ _ _ hb3 (by rw [h3e0]; omega),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0])]
    have h := mstore_extract_self' M (UInt256.ofNat 0x3a0) adrsW hb1
    rw [h3a0] at h
    exact h
  · rw [mstore_extract_below' _ _ _ _ _ hb3 (by rw [h3e0])]
    have h := mstore_extract_self'
      (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3c0) nodeW hb2
    rw [h3c0] at h
    exact h
  · have h := mstore_extract_self'
      ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3c0) nodeW)
      (UInt256.ofNat 0x3e0) sibW hb3
    rw [h3e0] at h
    exact h

/-- Masked keccak over the odd node chain `ADRS@0x3a0, node@0x3e0, sib@0x3c0`
    = `climbLevel` (odd branch; the last store is strictly in-bounds, so the
    node slot above it survives by the strict right-disjoint lemma). -/
theorem masked_keccak_node_chain_value_odd
    (M : MachineState) (pkSeed adrsW nodeW sibW : UInt256)
    (tree height pathIdx : Nat)
    (hOdd : pathIdx % 2 ≠ 0)
    (hadrs : adrsW.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hpk : M.memory.data.extract 0x380 0x3a0 = pkSeed.toByteArray.data)
    (hsize : 0x3e0 ≤ M.memory.size) :
    (((((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3e0) nodeW).mstore
        (UInt256.ofNat 0x3c0) sibW).keccak256
        (UInt256.ofNat 0x380) (UInt256.ofNat 128)).1.land
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = climbLevel pkSeed.toNat tree height pathIdx nodeW.toNat sibW.toNat := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3e0 : (UInt256.ofNat 0x3e0).toNat = 0x3e0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have hb1 : (UInt256.ofNat 0x3a0).toNat ≤ M.memory.size := by rw [h3a0]; omega
  have hsz1 := mstore_memory_size' M (UInt256.ofNat 0x3a0) adrsW hb1
  rw [h3a0] at hsz1
  have hb2 : (UInt256.ofNat 0x3e0).toNat
      ≤ (M.mstore (UInt256.ofNat 0x3a0) adrsW).memory.size := by
    rw [h3e0, hsz1]; omega
  have hsz2 := mstore_memory_size'
    (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3e0) nodeW hb2
  rw [h3e0, hsz1] at hsz2
  have hb3 : (UInt256.ofNat 0x3c0).toNat + 32
      ≤ ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore
          (UInt256.ofNat 0x3e0) nodeW).memory.size := by
    rw [h3c0, hsz2]; omega
  have hsz3 := mstore_memory_size
    ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3e0) nodeW)
    (UInt256.ofNat 0x3c0) sibW hb3
  rw [masked_keccak_toNat,
    show (UInt256.ofNat 0x380).toNat = ScratchBase from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 128).toNat = NodeHashLen from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  refine node_derivation_climbLevel_odd_of_extracts _ pkSeed adrsW nodeW sibW
    tree height pathIdx hOdd hadrs ?_ ?_ ?_ ?_ ?_
  · rw [hsz3, hsz2]; unfold ScratchBase NodeHashLen; omega
  · rw [mstore_extract_disjoint _ _ _ _ _ hb3 (Or.inl (by rw [h3c0]; omega)),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3e0]; omega),
      mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0])]
    exact hpk
  · rw [mstore_extract_disjoint _ _ _ _ _ hb3 (Or.inl (by rw [h3c0])),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3e0]; omega)]
    have h := mstore_extract_self' M (UInt256.ofNat 0x3a0) adrsW hb1
    rw [h3a0] at h
    exact h
  · have h := mstore_extract_self
      ((M.mstore (UInt256.ofNat 0x3a0) adrsW).mstore (UInt256.ofNat 0x3e0) nodeW)
      (UInt256.ofNat 0x3c0) sibW hb3
    rw [h3c0] at h
    exact h
  · rw [mstore_extract_disjoint _ _ _ _ _ hb3 (Or.inr (by rw [h3c0]))]
    have h := mstore_extract_self'
      (M.mstore (UInt256.ofNat 0x3a0) adrsW) (UInt256.ofNat 0x3e0) nodeW hb2
    rw [h3e0] at h
    exact h

/-! ## The leaf value, from the extract-based invariant -/

/-- **Leaf value discharge (extract-based).** With `pkSeed`'s bytes sitting at
    `[0x380, 0x3a0)` of the entry memory (size at least the scratch base — true
    already at loop entry, where memory ends exactly at `0x3a0`), the leaf
    prefix binds `usr_node` to the model `leafHash`. `hadrs` is the ADRS-word
    arithmetic the loop invariant supplies (A4). -/
theorem tree_leaf_node_value_of_extract
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256) (tree leafIdx : Nat)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3a0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hadrs : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat = shapeLeafAdrsWord tree leafIdx) :
    (treeLeafNodeWord (.Ok ss vs)).toNat
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx)
          (treeSkWord (.Ok ss vs)).toNat := by
  unfold treeLeafNodeWord
  rw [treeAfterLeafSk_getElem, hlen, treeAfterLeafSk_toMachineState]
  exact masked_keccak_leaf_chain_value _ pkSeed _ _ tree leafIdx hadrs hpk hsize

/-! ## Node level 1: lookup resolution -/

/-- `setMachineState` keeps the varstore (generic lookup preservation). -/
theorem state_setMachineState_getElem (ss : SharedState .Yul) (vs : VarStore)
    (m : MachineState) (x : Identifier) :
    ((EvmYul.Yul.State.Ok ss vs).setMachineState m)[x]!
      = (EvmYul.Yul.State.Ok ss vs)[x]! := rfl

theorem treeAfterSel0_toMachineState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSel0 (.Ok ss vs)).toMachineState
      = (EvmYul.Yul.State.Ok ss vs).toMachineState := rfl

theorem treeAfterSel0_getElem_self (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSel0 (.Ok ss vs))[usrSId]! = treeSelector0Word (.Ok ss vs) :=
  state_getElem_insert_self ss vs _ _

theorem treeAfterSel0_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h : y ≠ "usr_s") :
    (treeAfterSel0 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! :=
  state_getElem_insert_ne ss vs (treeSelector0Word (.Ok ss vs)) h

theorem treeAfterNode1Adrs_getElem (ss : SharedState .Yul) (vs : VarStore)
    (x : Identifier) :
    (treeAfterNode1Adrs (.Ok ss vs))[x]! = (treeAfterSel0 (.Ok ss vs))[x]! := rfl

theorem treeAfterNode1Store_getElem (ss : SharedState .Yul) (vs : VarStore)
    (x : Identifier) :
    (treeAfterNode1Store (.Ok ss vs))[x]! = (treeAfterSel0 (.Ok ss vs))[x]! := rfl

theorem treeAfterNode1Store_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode1Store (.Ok ss vs)).toState
      = (EvmYul.Yul.State.Ok ss vs).toState := rfl

/-- The level-1 ADRS word reads only `usr_t`/`usr_dCursor`, untouched by the
    selector insert. -/
theorem treeNodeAdrsWord_after_sel0 (ss : SharedState .Yul) (vs : VarStore)
    (k j m c : Nat) :
    treeNodeAdrsWord (treeAfterSel0 (.Ok ss vs)) k j m c
      = treeNodeAdrsWord (.Ok ss vs) k j m c := by
  unfold treeNodeAdrsWord
  rw [treeAfterSel0_getElem_ne ss vs (show usrTId ≠ "usr_s" by decide),
    treeAfterSel0_getElem_ne ss vs (show dCursorId ≠ "usr_s" by decide)]

/-- The level-1 chain, verbatim from the defs (lookups still unresolved). -/
theorem treeAfterSibling1_toMachineState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling1 (.Ok ss vs)).toMachineState
      = (((treeAfterSel0 (.Ok ss vs)).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (treeAfterSel0 (.Ok ss vs)) 4 1 15
              1020847100762815390390123822299599601664)).mstore
          ((UInt256.ofNat 0x3c0).xor (treeAfterNode1Adrs (.Ok ss vs))[usrSId]!)
          (treeAfterNode1Adrs (.Ok ss vs))[usrNodeId]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeAfterNode1Store (.Ok ss vs))[usrSId]!)
          (treeMaskedCalldataWord (treeAfterNode1Store (.Ok ss vs))
            ((treeAfterNode1Store (.Ok ss vs))[treePtrId]!.add (UInt256.ofNat 16))) := rfl

/-! ## Node level 1: the value, even and odd branches -/

/-- **Node-1 value discharge, even branch** (`usr_s = 0`: node at `0x3c0`,
    sibling at `0x3e0`). The entry state `.Ok ss vs` is the state at body
    statement 3 (after the leaf prefix, hence `0x3e0 ≤ size`); `hadrs` and the
    `pathIdx` parity are the arithmetic the A4 invariant supplies. -/
theorem tree_node1_value_of_extract_even
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256)
    (tree height pathIdx : Nat)
    (hsel : treeSelector0Word (.Ok ss vs) = UInt256.ofNat 0)
    (hEven : pathIdx % 2 = 0)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3e0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hadrs : (treeNodeAdrsWord (.Ok ss vs) 4 1 15
        1020847100762815390390123822299599601664).toNat
          = shapeNodeAdrsWord tree height (pathIdx / 2)) :
    (treeNode1Word (.Ok ss vs)).toNat
      = climbLevel pkSeed.toNat tree height pathIdx
          ((EvmYul.Yul.State.Ok ss vs)[usrNodeId]!).toNat
          (treeMaskedCalldataWord (.Ok ss vs)
            ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))).toNat := by
  have hchain : (treeAfterSibling1 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 4 1 15
              1020847100762815390390123822299599601664)).mstore
          (UInt256.ofNat 0x3c0) (EvmYul.Yul.State.Ok ss vs)[usrNodeId]!).mstore
          (UInt256.ofNat 0x3e0)
          (treeMaskedCalldataWord (.Ok ss vs)
            ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))) := by
    rw [treeAfterSibling1_toMachineState, treeAfterSel0_toMachineState,
      treeAfterNode1Adrs_getElem ss vs usrSId,
      treeAfterNode1Adrs_getElem ss vs usrNodeId,
      treeAfterNode1Store_getElem ss vs usrSId,
      treeAfterNode1Store_getElem ss vs treePtrId,
      treeAfterSel0_getElem_self, hsel, xor_3c0_zero, xor_3e0_zero,
      treeNodeAdrsWord_after_sel0,
      treeAfterSel0_getElem_ne ss vs (show usrNodeId ≠ "usr_s" by decide),
      treeAfterSel0_getElem_ne ss vs (show treePtrId ≠ "usr_s" by decide)]
    unfold treeMaskedCalldataWord
    rw [treeAfterNode1Store_toState]
  unfold treeNode1Word
  rw [hchain]
  exact masked_keccak_node_chain_value_even _ pkSeed _ _ _ tree height pathIdx
    hEven hadrs hpk hsize

/-- **Node-1 value discharge, odd branch** (`usr_s = 32`: sibling at `0x3c0`,
    node at `0x3e0`). -/
theorem tree_node1_value_of_extract_odd
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256)
    (tree height pathIdx : Nat)
    (hsel : treeSelector0Word (.Ok ss vs) = UInt256.ofNat 32)
    (hOdd : pathIdx % 2 ≠ 0)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3e0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hadrs : (treeNodeAdrsWord (.Ok ss vs) 4 1 15
        1020847100762815390390123822299599601664).toNat
          = shapeNodeAdrsWord tree height (pathIdx / 2)) :
    (treeNode1Word (.Ok ss vs)).toNat
      = climbLevel pkSeed.toNat tree height pathIdx
          ((EvmYul.Yul.State.Ok ss vs)[usrNodeId]!).toNat
          (treeMaskedCalldataWord (.Ok ss vs)
            ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))).toNat := by
  have hchain : (treeAfterSibling1 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 4 1 15
              1020847100762815390390123822299599601664)).mstore
          (UInt256.ofNat 0x3e0) (EvmYul.Yul.State.Ok ss vs)[usrNodeId]!).mstore
          (UInt256.ofNat 0x3c0)
          (treeMaskedCalldataWord (.Ok ss vs)
            ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))) := by
    rw [treeAfterSibling1_toMachineState, treeAfterSel0_toMachineState,
      treeAfterNode1Adrs_getElem ss vs usrSId,
      treeAfterNode1Adrs_getElem ss vs usrNodeId,
      treeAfterNode1Store_getElem ss vs usrSId,
      treeAfterNode1Store_getElem ss vs treePtrId,
      treeAfterSel0_getElem_self, hsel, xor_3c0_32, xor_3e0_32,
      treeNodeAdrsWord_after_sel0,
      treeAfterSel0_getElem_ne ss vs (show usrNodeId ≠ "usr_s" by decide),
      treeAfterSel0_getElem_ne ss vs (show treePtrId ≠ "usr_s" by decide)]
    unfold treeMaskedCalldataWord
    rw [treeAfterNode1Store_toState]
  unfold treeNode1Word
  rw [hchain]
  exact masked_keccak_node_chain_value_odd _ pkSeed _ _ _ tree height pathIdx
    hOdd hadrs hpk hsize

end NiceTry.Fors.Bridge
