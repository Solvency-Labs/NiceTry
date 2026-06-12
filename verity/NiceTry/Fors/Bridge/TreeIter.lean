import NiceTry.Fors.Bridge.TreeValue

/-!
# Tree-loop iteration glue (M1.4): transitions between the six hashes

The per-level value discharges (`TreeValue.lean`) are keyed on each level's
entry state. This file provides the transition lemmas that chain them through
one full iteration (`treeIterState`):

* **Memory facts** per chain shape (`leaf_chain_memory_facts`,
  `node_chain_memory_facts`, `root_store_memory_facts`): every extract ending
  at or below `0x3a0` survives a level (so `pkSeed@0x380`'s *left edge*… no —
  the scratch slots start at `0x3a0`; everything strictly below the scratch
  writes survives, which covers the roots buffer AND `pkSeed@[0x380,0x3a0)`),
  and the size grows to `max entry 0x3e0/0x400`.
* **State transparency**: each `treeAfterNode<k>` keeps `toState` and the
  untouched variables, exposes the freshly bound `usr_node_<k>`
  (`…_getElem_self`), and its memory is the level chain's memory (the keccak
  only bumps `activeWords`).

The capstone `tree_iter_*` package is assembled on top (next section/file).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul
open NiceTry.Fors

set_option maxHeartbeats 2000000

/-! ## Swap-offset case split -/

/-- With the selector in `{0, 32}` the two swap stores land on the two scratch
    slots (straight or swapped). -/
theorem xor_swap_offsets (w : UInt256)
    (hw : w = UInt256.ofNat 0 ∨ w = UInt256.ofNat 32) :
    ((UInt256.ofNat 0x3c0).xor w = UInt256.ofNat 0x3c0
        ∧ (UInt256.ofNat 0x3e0).xor w = UInt256.ofNat 0x3e0)
      ∨ ((UInt256.ofNat 0x3c0).xor w = UInt256.ofNat 0x3e0
        ∧ (UInt256.ofNat 0x3e0).xor w = UInt256.ofNat 0x3c0) := by
  rcases hw with h | h <;> subst h
  · exact Or.inl ⟨xor_3c0_zero, xor_3e0_zero⟩
  · exact Or.inr ⟨xor_3c0_32, xor_3e0_32⟩

/-! ## Per-chain memory facts -/

/-- The leaf chain (stores at `0x3a0`, `0x3c0`): low extracts survive, size
    grows to (at least) `0x3e0`. -/
theorem leaf_chain_memory_facts (M : MachineState) (A S : UInt256)
    (hsize : 0x3a0 ≤ M.memory.size) :
    (∀ lo hi, hi ≤ 0x3a0 →
        ((M.mstore (UInt256.ofNat 0x3a0) A).mstore
            (UInt256.ofNat 0x3c0) S).memory.data.extract lo hi
          = M.memory.data.extract lo hi)
      ∧ ((M.mstore (UInt256.ofNat 0x3a0) A).mstore
          (UInt256.ofNat 0x3c0) S).memory.size = max M.memory.size 0x3e0 := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have hb1 : (UInt256.ofNat 0x3a0).toNat ≤ M.memory.size := by rw [h3a0]; omega
  have hsz1 := mstore_memory_size' M (UInt256.ofNat 0x3a0) A hb1
  rw [h3a0] at hsz1
  have hb2 : (UInt256.ofNat 0x3c0).toNat
      ≤ (M.mstore (UInt256.ofNat 0x3a0) A).memory.size := by
    rw [h3c0, hsz1]; omega
  have hsz2 := mstore_memory_size' (M.mstore (UInt256.ofNat 0x3a0) A)
    (UInt256.ofNat 0x3c0) S hb2
  rw [h3c0, hsz1] at hsz2
  refine ⟨fun lo hi hhi => ?_, by rw [hsz2]; omega⟩
  rw [mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0]; omega),
    mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0]; omega)]

/-- A node chain (stores at `0x3a0` and the two swap slots): low extracts
    survive, size grows to (at least) `0x400`. Stated for both swap layouts at
    once via the selector disjunction. -/
theorem node_chain_memory_facts (M : MachineState) (A W B w : UInt256)
    (hw : w = UInt256.ofNat 0 ∨ w = UInt256.ofNat 32)
    (hsize : 0x3e0 ≤ M.memory.size) :
    (∀ lo hi, hi ≤ 0x3a0 →
        (((M.mstore (UInt256.ofNat 0x3a0) A).mstore
            ((UInt256.ofNat 0x3c0).xor w) W).mstore
            ((UInt256.ofNat 0x3e0).xor w) B).memory.data.extract lo hi
          = M.memory.data.extract lo hi)
      ∧ (((M.mstore (UInt256.ofNat 0x3a0) A).mstore
          ((UInt256.ofNat 0x3c0).xor w) W).mstore
          ((UInt256.ofNat 0x3e0).xor w) B).memory.size
        = max M.memory.size 0x400 := by
  have h3a0 : (UInt256.ofNat 0x3a0).toNat = 0x3a0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3c0 : (UInt256.ofNat 0x3c0).toNat = 0x3c0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have h3e0 : (UInt256.ofNat 0x3e0).toNat = 0x3e0 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  have hb1 : (UInt256.ofNat 0x3a0).toNat ≤ M.memory.size := by rw [h3a0]; omega
  have hsz1 := mstore_memory_size' M (UInt256.ofNat 0x3a0) A hb1
  rw [h3a0] at hsz1
  rcases xor_swap_offsets w hw with ⟨hc, he⟩ | ⟨hc, he⟩ <;> rw [hc, he]
  · -- straight: 0x3c0 then 0x3e0
    have hb2 : (UInt256.ofNat 0x3c0).toNat
        ≤ (M.mstore (UInt256.ofNat 0x3a0) A).memory.size := by
      rw [h3c0, hsz1]; omega
    have hsz2 := mstore_memory_size' (M.mstore (UInt256.ofNat 0x3a0) A)
      (UInt256.ofNat 0x3c0) W hb2
    rw [h3c0, hsz1] at hsz2
    have hb3 : (UInt256.ofNat 0x3e0).toNat
        ≤ ((M.mstore (UInt256.ofNat 0x3a0) A).mstore
            (UInt256.ofNat 0x3c0) W).memory.size := by
      rw [h3e0, hsz2]; omega
    have hsz3 := mstore_memory_size'
      ((M.mstore (UInt256.ofNat 0x3a0) A).mstore (UInt256.ofNat 0x3c0) W)
      (UInt256.ofNat 0x3e0) B hb3
    rw [h3e0, hsz2] at hsz3
    refine ⟨fun lo hi hhi => ?_, by rw [hsz3]; omega⟩
    rw [mstore_extract_below' _ _ _ _ _ hb3 (by rw [h3e0]; omega),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3c0]; omega),
      mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0]; omega)]
  · -- swapped: 0x3e0 then 0x3c0
    have hb2 : (UInt256.ofNat 0x3e0).toNat
        ≤ (M.mstore (UInt256.ofNat 0x3a0) A).memory.size := by
      rw [h3e0, hsz1]; omega
    have hsz2 := mstore_memory_size' (M.mstore (UInt256.ofNat 0x3a0) A)
      (UInt256.ofNat 0x3e0) W hb2
    rw [h3e0, hsz1] at hsz2
    have hb3 : (UInt256.ofNat 0x3c0).toNat
        ≤ ((M.mstore (UInt256.ofNat 0x3a0) A).mstore
            (UInt256.ofNat 0x3e0) W).memory.size := by
      rw [h3c0, hsz2]; omega
    have hsz3 := mstore_memory_size'
      ((M.mstore (UInt256.ofNat 0x3a0) A).mstore (UInt256.ofNat 0x3e0) W)
      (UInt256.ofNat 0x3c0) B hb3
    rw [h3c0, hsz2] at hsz3
    refine ⟨fun lo hi hhi => ?_, by rw [hsz3]; omega⟩
    rw [mstore_extract_below' _ _ _ _ _ hb3 (by rw [h3c0]; omega),
      mstore_extract_below' _ _ _ _ _ hb2 (by rw [h3e0]; omega),
      mstore_extract_below' _ _ _ _ _ hb1 (by rw [h3a0]; omega)]

/-- The root store (variable offset inside the roots buffer, strictly below the
    scratch window): in-bounds, the slot gets the root, everything else
    survives. -/
theorem root_store_memory_facts (M : MachineState) (p v : UInt256)
    (hp : p.toNat + 32 ≤ 0x360) (hsize : 0x400 ≤ M.memory.size) :
    (M.mstore p v).memory.size = M.memory.size
      ∧ (M.mstore p v).memory.data.extract p.toNat (p.toNat + 32)
          = v.toByteArray.data
      ∧ (∀ lo hi, hi ≤ p.toNat →
          (M.mstore p v).memory.data.extract lo hi = M.memory.data.extract lo hi)
      ∧ (∀ lo hi, p.toNat + 32 ≤ lo →
          (M.mstore p v).memory.data.extract lo hi = M.memory.data.extract lo hi) := by
  have hb : p.toNat + 32 ≤ M.memory.size := by omega
  exact ⟨mstore_memory_size M p v hb,
    mstore_extract_self M p v hb,
    fun lo hi hhi => mstore_extract_disjoint M p v lo hi hb (Or.inl hhi),
    fun lo hi hlo => mstore_extract_disjoint M p v lo hi hb (Or.inr hlo)⟩

/-! ## One-layer state algebra (cheap; avoids deep whnf of the level chains) -/

theorem state_getElem_finsert_self (a : SharedState .Yul) (vs : VarStore)
    (x : Identifier) (v : EvmYul.Literal) :
    (EvmYul.Yul.State.Ok a (vs.insert x v))[x]! = v :=
  state_getElem_insert_self a vs x v

theorem state_getElem_finsert_ne (a : SharedState .Yul) (vs : VarStore)
    {x y : Identifier} (v : EvmYul.Literal) (h : y ≠ x) :
    (EvmYul.Yul.State.Ok a (vs.insert x v))[y]!
      = (EvmYul.Yul.State.Ok a vs)[y]! :=
  state_getElem_insert_ne a vs v h

theorem state_getElem_shared_irrel (a a' : SharedState .Yul) (vs : VarStore)
    (y : Identifier) :
    (EvmYul.Yul.State.Ok a vs)[y]! = (EvmYul.Yul.State.Ok a' vs)[y]! := rfl

theorem ok_set_insert_toMachineState (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) (x : Identifier) (v : EvmYul.Literal) :
    (((EvmYul.Yul.State.Ok a b).setMachineState m).insert x v).toMachineState
      = m := rfl

theorem ok_set_insert_getElem (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) (x : Identifier) (v : EvmYul.Literal) (y : Identifier) :
    (((EvmYul.Yul.State.Ok a b).setMachineState m).insert x v)[y]!
      = (EvmYul.Yul.State.Ok a (b.insert x v))[y]! := rfl

theorem ok_set_insert_toState (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) (x : Identifier) (v : EvmYul.Literal) :
    (((EvmYul.Yul.State.Ok a b).setMachineState m).insert x v).toState
      = (EvmYul.Yul.State.Ok a b).toState := rfl

/-! ## Ok-exposure of the chain states (the only nontrivial whnfs, one per level) -/

theorem treeAfterLeafSk_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterLeafSk (.Ok ss vs) = .Ok a vs
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


theorem treeAfterSibling1_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterSibling1 (.Ok ss vs)
        = .Ok a (vs.insert "usr_s" (treeSelector0Word (.Ok ss vs)))
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


theorem treeAfterSibling2_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterSibling2 (.Ok ss vs)
        = .Ok a (vs.insert "usr_s_1" (treeSelector1Word (.Ok ss vs)))
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


theorem treeAfterSibling3_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterSibling3 (.Ok ss vs)
        = .Ok a (vs.insert "usr_s_2" (treeSelector2Word (.Ok ss vs)))
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


theorem treeAfterSibling4_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterSibling4 (.Ok ss vs)
        = .Ok a (vs.insert "usr_s_3" (treeSelector3Word (.Ok ss vs)))
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


theorem treeAfterSibling5_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterSibling5 (.Ok ss vs)
        = .Ok a (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs)))
      ∧ a.toState = ss.toState := ⟨_, rfl, rfl⟩


/-! ## Level-exit transparency (laddered) -/

theorem treeAfterLeafHash_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterLeafHash (.Ok ss vs)).toMachineState.memory
      = (treeAfterLeafSk (.Ok ss vs)).toMachineState.memory := by
  obtain ⟨a, ha, -⟩ := treeAfterLeafSk_ok ss vs
  show (((treeAfterLeafSk (.Ok ss vs)).setMachineState
      ((treeAfterLeafSk (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        ((treeAfterLeafSk (.Ok ss vs))[ret2Id]!)).2).insert "usr_node"
      (treeLeafNodeWord (.Ok ss vs))).toMachineState.memory = _
  rw [ha, ok_set_insert_toMachineState]
  exact keccak256_memory _ _ _

theorem treeAfterLeafHash_getElem_ne' (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h : y ≠ "usr_node") :
    (treeAfterLeafHash (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (((treeAfterLeafSk (.Ok ss vs)).setMachineState
      ((treeAfterLeafSk (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        ((treeAfterLeafSk (.Ok ss vs))[ret2Id]!)).2).insert "usr_node"
      (treeLeafNodeWord (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterLeafSk_ok ss vs
  rw [ha, ok_set_insert_getElem, state_getElem_finsert_ne a vs _ h]
  exact state_getElem_shared_irrel a ss vs y

theorem treeAfterLeafHash_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterLeafHash (.Ok ss vs)).toState
      = (EvmYul.Yul.State.Ok ss vs).toState := by
  show (((treeAfterLeafSk (.Ok ss vs)).setMachineState
      ((treeAfterLeafSk (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        ((treeAfterLeafSk (.Ok ss vs))[ret2Id]!)).2).insert "usr_node"
      (treeLeafNodeWord (.Ok ss vs))).toState = _
  obtain ⟨a, ha, hts⟩ := treeAfterLeafSk_ok ss vs
  rw [ha, ok_set_insert_toState]
  exact hts


theorem treeAfterNode1_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode1 (.Ok ss vs)).toMachineState.memory
      = (treeAfterSibling1 (.Ok ss vs)).toMachineState.memory := by
  obtain ⟨a, ha, -⟩ := treeAfterSibling1_ok ss vs
  show (((treeAfterSibling1 (.Ok ss vs)).setMachineState
      ((treeAfterSibling1 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_1"
      (treeNode1Word (.Ok ss vs))).toMachineState.memory = _
  rw [ha, ok_set_insert_toMachineState]
  exact keccak256_memory _ _ _

theorem treeAfterNode1_getElem_self (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode1 (.Ok ss vs))[usrNode1Id]! = treeNode1Word (.Ok ss vs) := by
  show (((treeAfterSibling1 (.Ok ss vs)).setMachineState
      ((treeAfterSibling1 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_1"
      (treeNode1Word (.Ok ss vs)))[usrNode1Id]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling1_ok ss vs
  rw [ha, ok_set_insert_getElem]
  exact state_getElem_finsert_self a _ _ _

theorem treeAfterNode1_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h1 : y ≠ "usr_s") (h2 : y ≠ "usr_node_1") :
    (treeAfterNode1 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (((treeAfterSibling1 (.Ok ss vs)).setMachineState
      ((treeAfterSibling1 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_1"
      (treeNode1Word (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling1_ok ss vs
  rw [ha, ok_set_insert_getElem, state_getElem_finsert_ne a _ _ h2,
    state_getElem_finsert_ne a vs _ h1]
  exact state_getElem_shared_irrel a ss vs y

theorem treeAfterNode1_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode1 (.Ok ss vs)).toState = (EvmYul.Yul.State.Ok ss vs).toState := by
  show (((treeAfterSibling1 (.Ok ss vs)).setMachineState
      ((treeAfterSibling1 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_1"
      (treeNode1Word (.Ok ss vs))).toState = _
  obtain ⟨a, ha, hts⟩ := treeAfterSibling1_ok ss vs
  rw [ha, ok_set_insert_toState]
  exact hts


theorem treeAfterNode2_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode2 (.Ok ss vs)).toMachineState.memory
      = (treeAfterSibling2 (.Ok ss vs)).toMachineState.memory := by
  obtain ⟨a, ha, -⟩ := treeAfterSibling2_ok ss vs
  show (((treeAfterSibling2 (.Ok ss vs)).setMachineState
      ((treeAfterSibling2 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_2"
      (treeNode2Word (.Ok ss vs))).toMachineState.memory = _
  rw [ha, ok_set_insert_toMachineState]
  exact keccak256_memory _ _ _

theorem treeAfterNode2_getElem_self (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode2 (.Ok ss vs))[usrNode2Id]! = treeNode2Word (.Ok ss vs) := by
  show (((treeAfterSibling2 (.Ok ss vs)).setMachineState
      ((treeAfterSibling2 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_2"
      (treeNode2Word (.Ok ss vs)))[usrNode2Id]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling2_ok ss vs
  rw [ha, ok_set_insert_getElem]
  exact state_getElem_finsert_self a _ _ _

theorem treeAfterNode2_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h1 : y ≠ "usr_s_1") (h2 : y ≠ "usr_node_2") :
    (treeAfterNode2 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (((treeAfterSibling2 (.Ok ss vs)).setMachineState
      ((treeAfterSibling2 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_2"
      (treeNode2Word (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling2_ok ss vs
  rw [ha, ok_set_insert_getElem, state_getElem_finsert_ne a _ _ h2,
    state_getElem_finsert_ne a vs _ h1]
  exact state_getElem_shared_irrel a ss vs y

theorem treeAfterNode2_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode2 (.Ok ss vs)).toState = (EvmYul.Yul.State.Ok ss vs).toState := by
  show (((treeAfterSibling2 (.Ok ss vs)).setMachineState
      ((treeAfterSibling2 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_2"
      (treeNode2Word (.Ok ss vs))).toState = _
  obtain ⟨a, ha, hts⟩ := treeAfterSibling2_ok ss vs
  rw [ha, ok_set_insert_toState]
  exact hts


theorem treeAfterNode3_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode3 (.Ok ss vs)).toMachineState.memory
      = (treeAfterSibling3 (.Ok ss vs)).toMachineState.memory := by
  obtain ⟨a, ha, -⟩ := treeAfterSibling3_ok ss vs
  show (((treeAfterSibling3 (.Ok ss vs)).setMachineState
      ((treeAfterSibling3 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_3"
      (treeNode3Word (.Ok ss vs))).toMachineState.memory = _
  rw [ha, ok_set_insert_toMachineState]
  exact keccak256_memory _ _ _

theorem treeAfterNode3_getElem_self (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode3 (.Ok ss vs))[usrNode3Id]! = treeNode3Word (.Ok ss vs) := by
  show (((treeAfterSibling3 (.Ok ss vs)).setMachineState
      ((treeAfterSibling3 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_3"
      (treeNode3Word (.Ok ss vs)))[usrNode3Id]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling3_ok ss vs
  rw [ha, ok_set_insert_getElem]
  exact state_getElem_finsert_self a _ _ _

theorem treeAfterNode3_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h1 : y ≠ "usr_s_2") (h2 : y ≠ "usr_node_3") :
    (treeAfterNode3 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (((treeAfterSibling3 (.Ok ss vs)).setMachineState
      ((treeAfterSibling3 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_3"
      (treeNode3Word (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling3_ok ss vs
  rw [ha, ok_set_insert_getElem, state_getElem_finsert_ne a _ _ h2,
    state_getElem_finsert_ne a vs _ h1]
  exact state_getElem_shared_irrel a ss vs y

theorem treeAfterNode3_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode3 (.Ok ss vs)).toState = (EvmYul.Yul.State.Ok ss vs).toState := by
  show (((treeAfterSibling3 (.Ok ss vs)).setMachineState
      ((treeAfterSibling3 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_3"
      (treeNode3Word (.Ok ss vs))).toState = _
  obtain ⟨a, ha, hts⟩ := treeAfterSibling3_ok ss vs
  rw [ha, ok_set_insert_toState]
  exact hts


theorem treeAfterNode4_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode4 (.Ok ss vs)).toMachineState.memory
      = (treeAfterSibling4 (.Ok ss vs)).toMachineState.memory := by
  obtain ⟨a, ha, -⟩ := treeAfterSibling4_ok ss vs
  show (((treeAfterSibling4 (.Ok ss vs)).setMachineState
      ((treeAfterSibling4 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_4"
      (treeNode4Word (.Ok ss vs))).toMachineState.memory = _
  rw [ha, ok_set_insert_toMachineState]
  exact keccak256_memory _ _ _

theorem treeAfterNode4_getElem_self (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode4 (.Ok ss vs))[usrNode4Id]! = treeNode4Word (.Ok ss vs) := by
  show (((treeAfterSibling4 (.Ok ss vs)).setMachineState
      ((treeAfterSibling4 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_4"
      (treeNode4Word (.Ok ss vs)))[usrNode4Id]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling4_ok ss vs
  rw [ha, ok_set_insert_getElem]
  exact state_getElem_finsert_self a _ _ _

theorem treeAfterNode4_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h1 : y ≠ "usr_s_3") (h2 : y ≠ "usr_node_4") :
    (treeAfterNode4 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (((treeAfterSibling4 (.Ok ss vs)).setMachineState
      ((treeAfterSibling4 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_4"
      (treeNode4Word (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling4_ok ss vs
  rw [ha, ok_set_insert_getElem, state_getElem_finsert_ne a _ _ h2,
    state_getElem_finsert_ne a vs _ h1]
  exact state_getElem_shared_irrel a ss vs y

theorem treeAfterNode4_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode4 (.Ok ss vs)).toState = (EvmYul.Yul.State.Ok ss vs).toState := by
  show (((treeAfterSibling4 (.Ok ss vs)).setMachineState
      ((treeAfterSibling4 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_4"
      (treeNode4Word (.Ok ss vs))).toState = _
  obtain ⟨a, ha, hts⟩ := treeAfterSibling4_ok ss vs
  rw [ha, ok_set_insert_toState]
  exact hts


/-! ### Level 5 + the root store (no node insert; the root store mstores) -/

theorem ok_set_toMachineState (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) :
    ((EvmYul.Yul.State.Ok a b).setMachineState m).toMachineState = m := rfl

theorem ok_set_getElem (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) (y : Identifier) :
    ((EvmYul.Yul.State.Ok a b).setMachineState m)[y]!
      = (EvmYul.Yul.State.Ok a b)[y]! := rfl

theorem ok_set_toState (a : SharedState .Yul) (b : VarStore) (m : MachineState) :
    ((EvmYul.Yul.State.Ok a b).setMachineState m).toState
      = (EvmYul.Yul.State.Ok a b).toState := rfl

/-- `treeAfterNode5` (root store included) keeps the untouched variables. -/
theorem treeAfterNode5_getElem_ne (ss : SharedState .Yul) (vs : VarStore)
    {y : Identifier} (h : y ≠ "usr_s_4") :
    (treeAfterNode5 (.Ok ss vs))[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (treeAfterRootStore (treeAfterSibling5 (.Ok ss vs)))[y]! = _
  obtain ⟨a, ha, -⟩ := treeAfterSibling5_ok ss vs
  show ((treeAfterRootKeccak (treeAfterSibling5 (.Ok ss vs))).setMachineState
      ((treeAfterRootKeccak (treeAfterSibling5 (.Ok ss vs))).toMachineState.mstore
        ((treeAfterRootKeccak (treeAfterSibling5 (.Ok ss vs)))[rootPtrId]!)
        (treeRootWord (treeAfterSibling5 (.Ok ss vs)))))[y]! = _
  show (((treeAfterSibling5 (.Ok ss vs)).setMachineState
      ((treeAfterSibling5 (.Ok ss vs)).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).setMachineState _)[y]! = _
  rw [ha]
  show ((((EvmYul.Yul.State.Ok a (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs)))).setMachineState
      _).setMachineState _))[y]! = _
  rw [show ∀ (m : MachineState),
      ((EvmYul.Yul.State.Ok a (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs)))).setMachineState
        m) = .Ok { a with toMachineState := m }
          (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs))) from fun _ => rfl]
  rw [show ∀ (a' : SharedState .Yul) (m : MachineState),
      ((EvmYul.Yul.State.Ok a' (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs)))).setMachineState
        m) = .Ok { a' with toMachineState := m }
          (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs))) from fun _ _ => rfl]
  rw [state_getElem_finsert_ne _ vs _ h]
  exact state_getElem_shared_irrel _ ss vs y


theorem ok_set_eq (a : SharedState .Yul) (b : VarStore) (m : MachineState) :
    (EvmYul.Yul.State.Ok a b).setMachineState m
      = .Ok { a with toMachineState := m } b := rfl

theorem ok_upd_toMachineState (a : SharedState .Yul) (b : VarStore)
    (m : MachineState) :
    (EvmYul.Yul.State.Ok { a with toMachineState := m } b).toMachineState
      = m := rfl

theorem treeAfterNode5_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode5 (.Ok ss vs)).toState
      = (EvmYul.Yul.State.Ok ss vs).toState := by
  obtain ⟨a, ha, hts⟩ := treeAfterSibling5_ok ss vs
  show (treeAfterRootStore (treeAfterSibling5 (.Ok ss vs))).toState = _
  unfold treeAfterRootStore treeAfterRootKeccak
  rw [ha, ok_set_eq, ok_set_toState]
  exact hts

/-- The exit memory of the whole iteration body: the root word written at the
    `usr_rootPtr` slot of the level-5 chain memory. -/
theorem treeAfterNode5_memory (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterNode5 (.Ok ss vs)).toMachineState.memory
      = ((treeAfterSibling5 (.Ok ss vs)).toMachineState.mstore
          ((EvmYul.Yul.State.Ok ss vs)[rootPtrId]!)
          (treeRootWord (treeAfterSibling5 (.Ok ss vs)))).memory := by
  obtain ⟨a, ha, -⟩ := treeAfterSibling5_ok ss vs
  show (treeAfterRootStore (treeAfterSibling5 (.Ok ss vs))).toMachineState.memory = _
  unfold treeAfterRootStore treeAfterRootKeccak
  rw [ha, ok_set_eq, ok_set_toMachineState, ok_upd_toMachineState,
    state_getElem_finsert_ne { a with
        toMachineState := ((EvmYul.Yul.State.Ok a
          (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs)))).toMachineState.keccak256
          (UInt256.ofNat 0x380) (UInt256.ofNat 128)).2 } vs
      (treeSelector4Word (.Ok ss vs)) (show rootPtrId ≠ "usr_s_4" by decide),
    state_getElem_shared_irrel _ ss vs rootPtrId,
    mstore_memory, mstore_memory, keccak256_memory]

/-! ## Half-resolved level chains (selector symbolic)

Same as the discharge `hchain`s but with the selector left as the
`treeSelector<j>Word` — the form `node_chain_memory_facts` consumes. -/


theorem treeAfterSibling1_chain (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling1 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 4 1 15
              1020847100762815390390123822299599601664)).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector0Word (.Ok ss vs)))
          (EvmYul.Yul.State.Ok ss vs)[usrNodeId]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector0Word (.Ok ss vs)))
          (treeMaskedCalldataWord (.Ok ss vs) ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))) := by
  rw [treeAfterSibling1_toMachineState, treeAfterSel0_toMachineState,
    treeAfterNode1Adrs_getElem ss vs usrSId,
    treeAfterNode1Adrs_getElem ss vs usrNodeId,
    treeAfterNode1Store_getElem ss vs usrSId,
    treeAfterNode1Store_getElem ss vs treePtrId,
    treeAfterSel0_getElem_self,
    treeNodeAdrsWord_after_sel0,
    treeAfterSel0_getElem_ne ss vs (show usrNodeId ≠ "usr_s" by decide),
    treeAfterSel0_getElem_ne ss vs (show treePtrId ≠ "usr_s" by decide)]
  unfold treeMaskedCalldataWord
  rw [treeAfterNode1Store_toState]


theorem treeAfterSibling2_chain (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling2 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 3 2 7
              1020847100762815390390123822303894568960)).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector1Word (.Ok ss vs)))
          (EvmYul.Yul.State.Ok ss vs)[usrNode1Id]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector1Word (.Ok ss vs)))
          (treeMaskedCalldataWord (.Ok ss vs) ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (EvmYul.Yul.State.Ok ss vs)[retId]!)) := by
  rw [treeAfterSibling2_toMachineState, treeAfterSel1_toMachineState,
    treeAfterNode2Adrs_getElem ss vs usrS1Id,
    treeAfterNode2Adrs_getElem ss vs usrNode1Id,
    treeAfterNode2Store_getElem ss vs usrS1Id,
    treeAfterNode2Store_getElem ss vs treePtrId,
    treeAfterNode2Store_getElem ss vs retId,
    treeAfterSel1_getElem_self,
    treeNodeAdrsWord_after_sel1,
    treeAfterSel1_getElem_ne ss vs (show usrNode1Id ≠ "usr_s_1" by decide),
    treeAfterSel1_getElem_ne ss vs (show treePtrId ≠ "usr_s_1" by decide),
    treeAfterSel1_getElem_ne ss vs (show retId ≠ "usr_s_1" by decide)]
  unfold treeMaskedCalldataWord
  rw [treeAfterNode2Store_toState]


theorem treeAfterSibling3_chain (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling3 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 2 3 3
              1020847100762815390390123822308189536256)).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector2Word (.Ok ss vs)))
          (EvmYul.Yul.State.Ok ss vs)[usrNode2Id]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector2Word (.Ok ss vs)))
          (treeMaskedCalldataWord (.Ok ss vs) ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 48))) := by
  rw [treeAfterSibling3_toMachineState, treeAfterSel2_toMachineState,
    treeAfterNode3Adrs_getElem ss vs usrS2Id,
    treeAfterNode3Adrs_getElem ss vs usrNode2Id,
    treeAfterNode3Store_getElem ss vs usrS2Id,
    treeAfterNode3Store_getElem ss vs treePtrId,
    treeAfterSel2_getElem_self,
    treeNodeAdrsWord_after_sel2,
    treeAfterSel2_getElem_ne ss vs (show usrNode2Id ≠ "usr_s_2" by decide),
    treeAfterSel2_getElem_ne ss vs (show treePtrId ≠ "usr_s_2" by decide)]
  unfold treeMaskedCalldataWord
  rw [treeAfterNode3Store_toState]


theorem treeAfterSibling4_chain (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling4 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeNodeAdrsWord (.Ok ss vs) 1 4 1
              1020847100762815390390123822312484503552)).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector3Word (.Ok ss vs)))
          (EvmYul.Yul.State.Ok ss vs)[usrNode3Id]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector3Word (.Ok ss vs)))
          (treeMaskedCalldataWord (.Ok ss vs) ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 64))) := by
  rw [treeAfterSibling4_toMachineState, treeAfterSel3_toMachineState,
    treeAfterNode4Adrs_getElem ss vs usrS3Id,
    treeAfterNode4Adrs_getElem ss vs usrNode3Id,
    treeAfterNode4Store_getElem ss vs usrS3Id,
    treeAfterNode4Store_getElem ss vs treePtrId,
    treeAfterSel3_getElem_self,
    treeNodeAdrsWord_after_sel3,
    treeAfterSel3_getElem_ne ss vs (show usrNode3Id ≠ "usr_s_3" by decide),
    treeAfterSel3_getElem_ne ss vs (show treePtrId ≠ "usr_s_3" by decide)]
  unfold treeMaskedCalldataWord
  rw [treeAfterNode4Store_toState]


theorem treeAfterSibling5_chain (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterSibling5 (.Ok ss vs)).toMachineState
      = (((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            ((EvmYul.Yul.State.Ok ss vs)[usrTId]!.lor
              (UInt256.ofNat 1020847100762815390390123822316779470848))).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector4Word (.Ok ss vs)))
          (EvmYul.Yul.State.Ok ss vs)[usrNode4Id]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector4Word (.Ok ss vs)))
          (treeMaskedCalldataWord (.Ok ss vs)
            ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 80))) := by
  rw [treeAfterSibling5_toMachineState, treeAfterSel4_toMachineState,
    treeAfterNode5Adrs_getElem ss vs usrS4Id,
    treeAfterNode5Adrs_getElem ss vs usrNode4Id,
    treeAfterNode5Store_getElem ss vs usrS4Id,
    treeAfterNode5Store_getElem ss vs treePtrId,
    treeAfterSel4_getElem_self,
    treeAfterSel4_getElem_ne ss vs (show usrTId ≠ "usr_s_4" by decide),
    treeAfterSel4_getElem_ne ss vs (show usrNode4Id ≠ "usr_s_4" by decide),
    treeAfterSel4_getElem_ne ss vs (show treePtrId ≠ "usr_s_4" by decide)]
  unfold treeMaskedCalldataWord
  rw [treeAfterNode5Store_toState]

/-! ## The cross-level invariant -/

/-- Facts carried from the iteration entry across the level exits: the
    loop-control variables are untouched, the calldata view is unchanged, the
    pkSeed slot survives, and memory has reached the scratch end. -/
structure IterFacts (e s : EvmYul.Yul.State) : Prop where
  toState : s.toState = e.toState
  dCursor : s[dCursorId]! = e[dCursorId]!
  ret : s[retId]! = e[retId]!
  ret2 : s[ret2Id]! = e[ret2Id]!
  usrT : s[usrTId]! = e[usrTId]!
  treePtr : s[treePtrId]! = e[treePtrId]!
  tLeafBase : s[tLeafBaseId]! = e[tLeafBaseId]!
  rootPtr : s[rootPtrId]! = e[rootPtrId]!
  low : ∀ lo hi : Nat, hi ≤ 0x3a0 →
    s.toMachineState.memory.data.extract lo hi
      = e.toMachineState.memory.data.extract lo hi
  size : 0x3e0 ≤ s.toMachineState.memory.size

/-- The pkSeed slot is inside the preserved low region. -/
theorem IterFacts.pkSlot {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    s.toMachineState.memory.data.extract 0x380 0x3a0
      = e.toMachineState.memory.data.extract 0x380 0x3a0 :=
  hf.low _ _ (by omega)

/-- The leaf prefix establishes the invariant (entry memory only needs to reach
    the scratch base, as at loop entry). -/
theorem iterFacts_leaf (ss : SharedState .Yul) (vs : VarStore)
    (hsize : 0x3a0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size) :
    IterFacts (.Ok ss vs) (treeAfterLeafHash (.Ok ss vs)) where
  toState := treeAfterLeafHash_toState ss vs
  dCursor := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  ret := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  ret2 := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  usrT := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  treePtr := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  tLeafBase := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  rootPtr := treeAfterLeafHash_getElem_ne' ss vs (by decide)
  low := fun lo hi hhi => by
    rw [treeAfterLeafHash_memory, treeAfterLeafSk_toMachineState]
    exact (leaf_chain_memory_facts _ _ _ hsize).1 lo hi hhi
  size := by
    rw [treeAfterLeafHash_memory, treeAfterLeafSk_toMachineState,
      (leaf_chain_memory_facts _ _ _ hsize).2]
    omega


/-- Node level 1 preserves the invariant (given the selector lands in the
    swap set). -/
theorem iterFacts_node1 (e : EvmYul.Yul.State) (a : SharedState .Yul)
    (b : VarStore) (hf : IterFacts e (.Ok a b))
    (hsel : treeSelector0Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector0Word (.Ok a b) = UInt256.ofNat 32) :
    IterFacts e (treeAfterNode1 (.Ok a b)) where
  toState := (treeAfterNode1_toState a b).trans hf.toState
  dCursor := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.dCursor
  ret := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.ret
  ret2 := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.ret2
  usrT := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.usrT
  treePtr := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.treePtr
  tLeafBase := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.tLeafBase
  rootPtr := (treeAfterNode1_getElem_ne a b (by decide) (by decide)).trans hf.rootPtr
  low := fun lo hi hhi => by
    rw [treeAfterNode1_memory, treeAfterSibling1_chain]
    exact ((node_chain_memory_facts _ _ _ _ _ hsel hf.size).1 lo hi hhi).trans
      (hf.low lo hi hhi)
  size := by
    rw [treeAfterNode1_memory, treeAfterSibling1_chain,
      (node_chain_memory_facts _ _ _ _ _ hsel hf.size).2]
    omega


/-- Node level 2 preserves the invariant (given the selector lands in the
    swap set). -/
theorem iterFacts_node2 (e : EvmYul.Yul.State) (a : SharedState .Yul)
    (b : VarStore) (hf : IterFacts e (.Ok a b))
    (hsel : treeSelector1Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector1Word (.Ok a b) = UInt256.ofNat 32) :
    IterFacts e (treeAfterNode2 (.Ok a b)) where
  toState := (treeAfterNode2_toState a b).trans hf.toState
  dCursor := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.dCursor
  ret := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.ret
  ret2 := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.ret2
  usrT := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.usrT
  treePtr := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.treePtr
  tLeafBase := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.tLeafBase
  rootPtr := (treeAfterNode2_getElem_ne a b (by decide) (by decide)).trans hf.rootPtr
  low := fun lo hi hhi => by
    rw [treeAfterNode2_memory, treeAfterSibling2_chain]
    exact ((node_chain_memory_facts _ _ _ _ _ hsel hf.size).1 lo hi hhi).trans
      (hf.low lo hi hhi)
  size := by
    rw [treeAfterNode2_memory, treeAfterSibling2_chain,
      (node_chain_memory_facts _ _ _ _ _ hsel hf.size).2]
    omega


/-- Node level 3 preserves the invariant (given the selector lands in the
    swap set). -/
theorem iterFacts_node3 (e : EvmYul.Yul.State) (a : SharedState .Yul)
    (b : VarStore) (hf : IterFacts e (.Ok a b))
    (hsel : treeSelector2Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector2Word (.Ok a b) = UInt256.ofNat 32) :
    IterFacts e (treeAfterNode3 (.Ok a b)) where
  toState := (treeAfterNode3_toState a b).trans hf.toState
  dCursor := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.dCursor
  ret := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.ret
  ret2 := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.ret2
  usrT := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.usrT
  treePtr := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.treePtr
  tLeafBase := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.tLeafBase
  rootPtr := (treeAfterNode3_getElem_ne a b (by decide) (by decide)).trans hf.rootPtr
  low := fun lo hi hhi => by
    rw [treeAfterNode3_memory, treeAfterSibling3_chain]
    exact ((node_chain_memory_facts _ _ _ _ _ hsel hf.size).1 lo hi hhi).trans
      (hf.low lo hi hhi)
  size := by
    rw [treeAfterNode3_memory, treeAfterSibling3_chain,
      (node_chain_memory_facts _ _ _ _ _ hsel hf.size).2]
    omega


/-- Node level 4 preserves the invariant (given the selector lands in the
    swap set). -/
theorem iterFacts_node4 (e : EvmYul.Yul.State) (a : SharedState .Yul)
    (b : VarStore) (hf : IterFacts e (.Ok a b))
    (hsel : treeSelector3Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector3Word (.Ok a b) = UInt256.ofNat 32) :
    IterFacts e (treeAfterNode4 (.Ok a b)) where
  toState := (treeAfterNode4_toState a b).trans hf.toState
  dCursor := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.dCursor
  ret := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.ret
  ret2 := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.ret2
  usrT := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.usrT
  treePtr := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.treePtr
  tLeafBase := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.tLeafBase
  rootPtr := (treeAfterNode4_getElem_ne a b (by decide) (by decide)).trans hf.rootPtr
  low := fun lo hi hhi => by
    rw [treeAfterNode4_memory, treeAfterSibling4_chain]
    exact ((node_chain_memory_facts _ _ _ _ _ hsel hf.size).1 lo hi hhi).trans
      (hf.low lo hi hhi)
  size := by
    rw [treeAfterNode4_memory, treeAfterSibling4_chain,
      (node_chain_memory_facts _ _ _ _ _ hsel hf.size).2]
    omega

/-! ## Exit Ok-exposures and word transports -/

theorem treeAfterLeafHash_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterLeafHash (.Ok ss vs)
      = .Ok a (vs.insert "usr_node" (treeLeafNodeWord (.Ok ss vs))) := ⟨_, rfl⟩


theorem treeAfterNode1_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterNode1 (.Ok ss vs)
      = .Ok a ((vs.insert "usr_s" (treeSelector0Word (.Ok ss vs))).insert
          "usr_node_1" (treeNode1Word (.Ok ss vs))) := ⟨_, rfl⟩


theorem treeAfterNode2_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterNode2 (.Ok ss vs)
      = .Ok a ((vs.insert "usr_s_1" (treeSelector1Word (.Ok ss vs))).insert
          "usr_node_2" (treeNode2Word (.Ok ss vs))) := ⟨_, rfl⟩


theorem treeAfterNode3_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterNode3 (.Ok ss vs)
      = .Ok a ((vs.insert "usr_s_2" (treeSelector2Word (.Ok ss vs))).insert
          "usr_node_3" (treeNode3Word (.Ok ss vs))) := ⟨_, rfl⟩


theorem treeAfterNode4_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ a, treeAfterNode4 (.Ok ss vs)
      = .Ok a ((vs.insert "usr_s_3" (treeSelector3Word (.Ok ss vs))).insert
          "usr_node_4" (treeNode4Word (.Ok ss vs))) := ⟨_, rfl⟩


/-- The masked calldata word only reads `toState`. -/
theorem treeMaskedCalldataWord_congr {s s' : EvmYul.Yul.State}
    (h : s.toState = s'.toState) (p : UInt256) :
    treeMaskedCalldataWord s p = treeMaskedCalldataWord s' p := by
  unfold treeMaskedCalldataWord
  rw [h]


theorem treeSelector0Word_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    treeSelector0Word s = treeSelector0Word e := by
  unfold treeSelector0Word
  rw [hf.dCursor, hf.ret]


theorem treeSelector1Word_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    treeSelector1Word s = treeSelector1Word e := by
  unfold treeSelector1Word
  rw [hf.dCursor, hf.ret]


theorem treeSelector2Word_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    treeSelector2Word s = treeSelector2Word e := by
  unfold treeSelector2Word
  rw [hf.dCursor, hf.ret]


theorem treeSelector3Word_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    treeSelector3Word s = treeSelector3Word e := by
  unfold treeSelector3Word
  rw [hf.dCursor, hf.ret2, hf.ret]


theorem treeSelector4Word_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s) :
    treeSelector4Word s = treeSelector4Word e := by
  unfold treeSelector4Word
  rw [hf.dCursor, hf.ret]


theorem treeNodeAdrsWord_of_facts {e s : EvmYul.Yul.State} (hf : IterFacts e s)
    (k j m c : Nat) :
    treeNodeAdrsWord s k j m c = treeNodeAdrsWord e k j m c := by
  unfold treeNodeAdrsWord
  rw [hf.usrT, hf.dCursor]

/-! ## The single-iteration value package

Per-level step lemmas in existential form: each consumes the previous stage's
`.Ok` components and produces the next stage's, with the invariant, the
`usr_node_<k>` read-back, and the chained hash value. The capstone
`tree_iter_values` threads them through all six hashes. -/

/-- The leaf stage. -/
theorem tree_iter_leaf_step
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256) (tree idx : Nat)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3a0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hadrsL : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat = shapeLeafAdrsWord tree idx) :
    ∃ a b, treeAfterLeafHash (.Ok ss vs) = .Ok a b
      ∧ IterFacts (.Ok ss vs) (.Ok a b)
      ∧ (EvmYul.Yul.State.Ok a b)[usrNodeId]! = treeLeafNodeWord (.Ok ss vs)
      ∧ (treeLeafNodeWord (.Ok ss vs)).toNat
          = leafHash pkSeed.toNat (leafAdrs tree idx) (treeSkWord (.Ok ss vs)).toNat := by
  obtain ⟨a, h⟩ := treeAfterLeafHash_ok ss vs
  refine ⟨a, _, h, h ▸ iterFacts_leaf ss vs hsize, ?_, 
    tree_leaf_node_value_of_extract ss vs pkSeed tree idx hpk hsize hlen hadrsL⟩
  rw [show usrNodeId = "usr_node" from rfl]
  exact state_getElem_finsert_self a vs "usr_node" (treeLeafNodeWord (.Ok ss vs))


/-- Node level 1 as an iteration step. -/
theorem tree_iter_node1_step
    (e : EvmYul.Yul.State) (a : SharedState .Yul) (b : VarStore)
    (pkSeed : UInt256) (tree pIdx : Nat)
    (hf : IterFacts e (.Ok a b))
    (hpk : e.toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsel : (treeSelector0Word e = UInt256.ofNat 0 ∧ pIdx % 2 = 0)
      ∨ (treeSelector0Word e = UInt256.ofNat 32 ∧ pIdx % 2 ≠ 0))
    (hadrs : (treeNodeAdrsWord e 4 1 15 1020847100762815390390123822299599601664).toNat
          = shapeNodeAdrsWord tree 1 (pIdx / 2)) :
    ∃ a' b', treeAfterNode1 (.Ok a b) = .Ok a' b'
      ∧ IterFacts e (.Ok a' b')
      ∧ (EvmYul.Yul.State.Ok a' b')[usrNode1Id]! = treeNode1Word (.Ok a b)
      ∧ (treeNode1Word (.Ok a b)).toNat
          = climbLevel pkSeed.toNat tree 1 pIdx
              ((EvmYul.Yul.State.Ok a b)[usrNodeId]!).toNat
              (treeMaskedCalldataWord e (e[treePtrId]!.add (UInt256.ofNat 16))).toNat := by
  have hpk' := hf.pkSlot.trans hpk
  have hadrs' : (treeNodeAdrsWord (.Ok a b) 4 1 15 1020847100762815390390123822299599601664).toNat
      = shapeNodeAdrsWord tree 1 (pIdx / 2) := by
    rw [treeNodeAdrsWord_of_facts hf]; exact hadrs
  have hsd : treeSelector0Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector0Word (.Ok a b) = UInt256.ofNat 32 := by
    rw [treeSelector0Word_of_facts hf]
    exact hsel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have step : (treeNode1Word (.Ok a b)).toNat
      = climbLevel pkSeed.toNat tree 1 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNodeId]!).toNat
          (treeMaskedCalldataWord (.Ok a b) ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (UInt256.ofNat 16))).toNat := by
    rcases hsel with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact tree_node1_value_of_extract_even a b pkSeed tree 1 pIdx
        (by rw [treeSelector0Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
    · exact tree_node1_value_of_extract_odd a b pkSeed tree 1 pIdx
        (by rw [treeSelector0Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
  rw [hf.treePtr, treeMaskedCalldataWord_congr hf.toState] at step
  obtain ⟨a', h⟩ := treeAfterNode1_ok a b
  refine ⟨a', _, h, h ▸ iterFacts_node1 e a b hf hsd, ?_, step⟩
  rw [show usrNode1Id = "usr_node_1" from rfl]
  exact state_getElem_finsert_self a' _ "usr_node_1" (treeNode1Word (.Ok a b))


/-- Node level 2 as an iteration step. -/
theorem tree_iter_node2_step
    (e : EvmYul.Yul.State) (a : SharedState .Yul) (b : VarStore)
    (pkSeed : UInt256) (tree pIdx : Nat)
    (hf : IterFacts e (.Ok a b))
    (hpk : e.toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsel : (treeSelector1Word e = UInt256.ofNat 0 ∧ pIdx % 2 = 0)
      ∨ (treeSelector1Word e = UInt256.ofNat 32 ∧ pIdx % 2 ≠ 0))
    (hadrs : (treeNodeAdrsWord e 3 2 7 1020847100762815390390123822303894568960).toNat
          = shapeNodeAdrsWord tree 2 (pIdx / 2)) :
    ∃ a' b', treeAfterNode2 (.Ok a b) = .Ok a' b'
      ∧ IterFacts e (.Ok a' b')
      ∧ (EvmYul.Yul.State.Ok a' b')[usrNode2Id]! = treeNode2Word (.Ok a b)
      ∧ (treeNode2Word (.Ok a b)).toNat
          = climbLevel pkSeed.toNat tree 2 pIdx
              ((EvmYul.Yul.State.Ok a b)[usrNode1Id]!).toNat
              (treeMaskedCalldataWord e (e[treePtrId]!.add e[retId]!)).toNat := by
  have hpk' := hf.pkSlot.trans hpk
  have hadrs' : (treeNodeAdrsWord (.Ok a b) 3 2 7 1020847100762815390390123822303894568960).toNat
      = shapeNodeAdrsWord tree 2 (pIdx / 2) := by
    rw [treeNodeAdrsWord_of_facts hf]; exact hadrs
  have hsd : treeSelector1Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector1Word (.Ok a b) = UInt256.ofNat 32 := by
    rw [treeSelector1Word_of_facts hf]
    exact hsel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have step : (treeNode2Word (.Ok a b)).toNat
      = climbLevel pkSeed.toNat tree 2 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNode1Id]!).toNat
          (treeMaskedCalldataWord (.Ok a b) ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)).toNat := by
    rcases hsel with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact tree_node2_value_of_extract_even a b pkSeed tree 2 pIdx
        (by rw [treeSelector1Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
    · exact tree_node2_value_of_extract_odd a b pkSeed tree 2 pIdx
        (by rw [treeSelector1Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
  rw [hf.treePtr, hf.ret, treeMaskedCalldataWord_congr hf.toState] at step
  obtain ⟨a', h⟩ := treeAfterNode2_ok a b
  refine ⟨a', _, h, h ▸ iterFacts_node2 e a b hf hsd, ?_, step⟩
  rw [show usrNode2Id = "usr_node_2" from rfl]
  exact state_getElem_finsert_self a' _ "usr_node_2" (treeNode2Word (.Ok a b))


/-- Node level 3 as an iteration step. -/
theorem tree_iter_node3_step
    (e : EvmYul.Yul.State) (a : SharedState .Yul) (b : VarStore)
    (pkSeed : UInt256) (tree pIdx : Nat)
    (hf : IterFacts e (.Ok a b))
    (hpk : e.toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsel : (treeSelector2Word e = UInt256.ofNat 0 ∧ pIdx % 2 = 0)
      ∨ (treeSelector2Word e = UInt256.ofNat 32 ∧ pIdx % 2 ≠ 0))
    (hadrs : (treeNodeAdrsWord e 2 3 3 1020847100762815390390123822308189536256).toNat
          = shapeNodeAdrsWord tree 3 (pIdx / 2)) :
    ∃ a' b', treeAfterNode3 (.Ok a b) = .Ok a' b'
      ∧ IterFacts e (.Ok a' b')
      ∧ (EvmYul.Yul.State.Ok a' b')[usrNode3Id]! = treeNode3Word (.Ok a b)
      ∧ (treeNode3Word (.Ok a b)).toNat
          = climbLevel pkSeed.toNat tree 3 pIdx
              ((EvmYul.Yul.State.Ok a b)[usrNode2Id]!).toNat
              (treeMaskedCalldataWord e (e[treePtrId]!.add (UInt256.ofNat 48))).toNat := by
  have hpk' := hf.pkSlot.trans hpk
  have hadrs' : (treeNodeAdrsWord (.Ok a b) 2 3 3 1020847100762815390390123822308189536256).toNat
      = shapeNodeAdrsWord tree 3 (pIdx / 2) := by
    rw [treeNodeAdrsWord_of_facts hf]; exact hadrs
  have hsd : treeSelector2Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector2Word (.Ok a b) = UInt256.ofNat 32 := by
    rw [treeSelector2Word_of_facts hf]
    exact hsel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have step : (treeNode3Word (.Ok a b)).toNat
      = climbLevel pkSeed.toNat tree 3 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNode2Id]!).toNat
          (treeMaskedCalldataWord (.Ok a b) ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (UInt256.ofNat 48))).toNat := by
    rcases hsel with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact tree_node3_value_of_extract_even a b pkSeed tree 3 pIdx
        (by rw [treeSelector2Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
    · exact tree_node3_value_of_extract_odd a b pkSeed tree 3 pIdx
        (by rw [treeSelector2Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
  rw [hf.treePtr, treeMaskedCalldataWord_congr hf.toState] at step
  obtain ⟨a', h⟩ := treeAfterNode3_ok a b
  refine ⟨a', _, h, h ▸ iterFacts_node3 e a b hf hsd, ?_, step⟩
  rw [show usrNode3Id = "usr_node_3" from rfl]
  exact state_getElem_finsert_self a' _ "usr_node_3" (treeNode3Word (.Ok a b))


/-- Node level 4 as an iteration step. -/
theorem tree_iter_node4_step
    (e : EvmYul.Yul.State) (a : SharedState .Yul) (b : VarStore)
    (pkSeed : UInt256) (tree pIdx : Nat)
    (hf : IterFacts e (.Ok a b))
    (hpk : e.toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsel : (treeSelector3Word e = UInt256.ofNat 0 ∧ pIdx % 2 = 0)
      ∨ (treeSelector3Word e = UInt256.ofNat 32 ∧ pIdx % 2 ≠ 0))
    (hadrs : (treeNodeAdrsWord e 1 4 1 1020847100762815390390123822312484503552).toNat
          = shapeNodeAdrsWord tree 4 (pIdx / 2)) :
    ∃ a' b', treeAfterNode4 (.Ok a b) = .Ok a' b'
      ∧ IterFacts e (.Ok a' b')
      ∧ (EvmYul.Yul.State.Ok a' b')[usrNode4Id]! = treeNode4Word (.Ok a b)
      ∧ (treeNode4Word (.Ok a b)).toNat
          = climbLevel pkSeed.toNat tree 4 pIdx
              ((EvmYul.Yul.State.Ok a b)[usrNode3Id]!).toNat
              (treeMaskedCalldataWord e (e[treePtrId]!.add (UInt256.ofNat 64))).toNat := by
  have hpk' := hf.pkSlot.trans hpk
  have hadrs' : (treeNodeAdrsWord (.Ok a b) 1 4 1 1020847100762815390390123822312484503552).toNat
      = shapeNodeAdrsWord tree 4 (pIdx / 2) := by
    rw [treeNodeAdrsWord_of_facts hf]; exact hadrs
  have hsd : treeSelector3Word (.Ok a b) = UInt256.ofNat 0
      ∨ treeSelector3Word (.Ok a b) = UInt256.ofNat 32 := by
    rw [treeSelector3Word_of_facts hf]
    exact hsel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have step : (treeNode4Word (.Ok a b)).toNat
      = climbLevel pkSeed.toNat tree 4 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNode3Id]!).toNat
          (treeMaskedCalldataWord (.Ok a b) ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (UInt256.ofNat 64))).toNat := by
    rcases hsel with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact tree_node4_value_of_extract_even a b pkSeed tree 4 pIdx
        (by rw [treeSelector3Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
    · exact tree_node4_value_of_extract_odd a b pkSeed tree 4 pIdx
        (by rw [treeSelector3Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
  rw [hf.treePtr, treeMaskedCalldataWord_congr hf.toState] at step
  obtain ⟨a', h⟩ := treeAfterNode4_ok a b
  refine ⟨a', _, h, h ▸ iterFacts_node4 e a b hf hsd, ?_, step⟩
  rw [show usrNode4Id = "usr_node_4" from rfl]
  exact state_getElem_finsert_self a' _ "usr_node_4" (treeNode4Word (.Ok a b))


/-- The root level as an iteration step (no `usr_node_5`; the value lands in
    memory at `usr_rootPtr` — see `treeAfterNode5_memory`). -/
theorem tree_iter_root_step
    (e : EvmYul.Yul.State) (a : SharedState .Yul) (b : VarStore)
    (pkSeed : UInt256) (tree pIdx : Nat)
    (hf : IterFacts e (.Ok a b))
    (hpk : e.toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsel : (treeSelector4Word e = UInt256.ofNat 0 ∧ pIdx % 2 = 0)
      ∨ (treeSelector4Word e = UInt256.ofNat 32 ∧ pIdx % 2 ≠ 0))
    (hadrs : (e[usrTId]!.lor
        (UInt256.ofNat 1020847100762815390390123822316779470848)).toNat
          = shapeNodeAdrsWord tree 5 (pIdx / 2)) :
    (treeRootWord (treeAfterSibling5 (.Ok a b))).toNat
      = climbLevel pkSeed.toNat tree 5 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNode4Id]!).toNat
          (treeMaskedCalldataWord e (e[treePtrId]!.add (UInt256.ofNat 80))).toNat := by
  have hpk' := hf.pkSlot.trans hpk
  have hadrs' : ((EvmYul.Yul.State.Ok a b)[usrTId]!.lor
      (UInt256.ofNat 1020847100762815390390123822316779470848)).toNat
        = shapeNodeAdrsWord tree 5 (pIdx / 2) := by
    rw [hf.usrT]; exact hadrs
  have step : (treeRootWord (treeAfterSibling5 (.Ok a b))).toNat
      = climbLevel pkSeed.toNat tree 5 pIdx
          ((EvmYul.Yul.State.Ok a b)[usrNode4Id]!).toNat
          (treeMaskedCalldataWord (.Ok a b)
            ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (UInt256.ofNat 80))).toNat := by
    rcases hsel with ⟨hs, hp⟩ | ⟨hs, hp⟩
    · exact tree_root_value_of_extract_even a b pkSeed tree 5 pIdx
        (by rw [treeSelector4Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
    · exact tree_root_value_of_extract_odd a b pkSeed tree 5 pIdx
        (by rw [treeSelector4Word_of_facts hf]; exact hs) hp hpk' hf.size hadrs'
  rw [hf.treePtr, treeMaskedCalldataWord_congr hf.toState] at step
  exact step


/-- **One iteration, all six hash values**, chained and expressed against the
    iteration entry — the `hleaf/hnode1..5/hroot` payload for the A4 induction.
    The selector/parity and ADRS-word hypotheses are exactly what the
    arithmetic layer supplies from the loop invariant. -/
theorem tree_iter_values
    (ss : SharedState .Yul) (vs : VarStore) (pkSeed : UInt256)
    (tree idx : Nat)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3a0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hadrsL : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat = shapeLeafAdrsWord tree idx)
    (hsel0 : (treeSelector0Word (.Ok ss vs) = UInt256.ofNat 0 ∧ idx % 2 = 0)
      ∨ (treeSelector0Word (.Ok ss vs) = UInt256.ofNat 32 ∧ idx % 2 ≠ 0))
    (hadrs1 : (treeNodeAdrsWord (.Ok ss vs) 4 1 15
        1020847100762815390390123822299599601664).toNat
          = shapeNodeAdrsWord tree 1 (idx / 2))
    (hsel1 : (treeSelector1Word (.Ok ss vs) = UInt256.ofNat 0 ∧ idx / 2 % 2 = 0)
      ∨ (treeSelector1Word (.Ok ss vs) = UInt256.ofNat 32 ∧ idx / 2 % 2 ≠ 0))
    (hadrs2 : (treeNodeAdrsWord (.Ok ss vs) 3 2 7
        1020847100762815390390123822303894568960).toNat
          = shapeNodeAdrsWord tree 2 (idx / 2 / 2))
    (hsel2 : (treeSelector2Word (.Ok ss vs) = UInt256.ofNat 0 ∧ idx / 2 / 2 % 2 = 0)
      ∨ (treeSelector2Word (.Ok ss vs) = UInt256.ofNat 32 ∧ idx / 2 / 2 % 2 ≠ 0))
    (hadrs3 : (treeNodeAdrsWord (.Ok ss vs) 2 3 3
        1020847100762815390390123822308189536256).toNat
          = shapeNodeAdrsWord tree 3 (idx / 2 / 2 / 2))
    (hsel3 : (treeSelector3Word (.Ok ss vs) = UInt256.ofNat 0
          ∧ idx / 2 / 2 / 2 % 2 = 0)
      ∨ (treeSelector3Word (.Ok ss vs) = UInt256.ofNat 32
          ∧ idx / 2 / 2 / 2 % 2 ≠ 0))
    (hadrs4 : (treeNodeAdrsWord (.Ok ss vs) 1 4 1
        1020847100762815390390123822312484503552).toNat
          = shapeNodeAdrsWord tree 4 (idx / 2 / 2 / 2 / 2))
    (hsel4 : (treeSelector4Word (.Ok ss vs) = UInt256.ofNat 0
          ∧ idx / 2 / 2 / 2 / 2 % 2 = 0)
      ∨ (treeSelector4Word (.Ok ss vs) = UInt256.ofNat 32
          ∧ idx / 2 / 2 / 2 / 2 % 2 ≠ 0))
    (hadrs5 : ((EvmYul.Yul.State.Ok ss vs)[usrTId]!.lor
        (UInt256.ofNat 1020847100762815390390123822316779470848)).toNat
          = shapeNodeAdrsWord tree 5 (idx / 2 / 2 / 2 / 2 / 2)) :
    (treeLeafNodeWord (.Ok ss vs)).toNat
        = leafHash pkSeed.toNat (leafAdrs tree idx)
            (treeSkWord (.Ok ss vs)).toNat
      ∧ (treeNode1Word (treeAfterLeafHash (.Ok ss vs))).toNat
        = climbLevel pkSeed.toNat tree 1 idx
            (treeLeafNodeWord (.Ok ss vs)).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))).toNat
      ∧ (treeNode2Word (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))).toNat
        = climbLevel pkSeed.toNat tree 2 (idx / 2)
            (treeNode1Word (treeAfterLeafHash (.Ok ss vs))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add
                (EvmYul.Yul.State.Ok ss vs)[retId]!)).toNat
      ∧ (treeNode3Word (treeAfterNode2 (treeAfterNode1
            (treeAfterLeafHash (.Ok ss vs))))).toNat
        = climbLevel pkSeed.toNat tree 3 (idx / 2 / 2)
            (treeNode2Word (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 48))).toNat
      ∧ (treeNode4Word (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
            (treeAfterLeafHash (.Ok ss vs)))))).toNat
        = climbLevel pkSeed.toNat tree 4 (idx / 2 / 2 / 2)
            (treeNode3Word (treeAfterNode2 (treeAfterNode1
              (treeAfterLeafHash (.Ok ss vs))))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 64))).toNat
      ∧ (treeRootWord (treeAfterSibling5 (treeAfterNode4 (treeAfterNode3
            (treeAfterNode2 (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))))))).toNat
        = climbLevel pkSeed.toNat tree 5 (idx / 2 / 2 / 2 / 2)
            (treeNode4Word (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
              (treeAfterLeafHash (.Ok ss vs)))))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 80))).toNat := by
  obtain ⟨a1, b1, h1, hf1, r1, c0⟩ :=
    tree_iter_leaf_step ss vs pkSeed tree idx hpk hsize hlen hadrsL
  obtain ⟨a2, b2, h2, hf2, r2, c1⟩ :=
    tree_iter_node1_step (.Ok ss vs) a1 b1 pkSeed tree idx hf1 hpk hsel0 hadrs1
  obtain ⟨a3, b3, h3, hf3, r3, c2⟩ :=
    tree_iter_node2_step (.Ok ss vs) a2 b2 pkSeed tree (idx / 2) hf2 hpk hsel1 hadrs2
  obtain ⟨a4, b4, h4, hf4, r4, c3⟩ :=
    tree_iter_node3_step (.Ok ss vs) a3 b3 pkSeed tree (idx / 2 / 2) hf3 hpk
      hsel2 hadrs3
  obtain ⟨a5, b5, h5, hf5, r5, c4⟩ :=
    tree_iter_node4_step (.Ok ss vs) a4 b4 pkSeed tree (idx / 2 / 2 / 2) hf4 hpk
      hsel3 hadrs4
  have c5 := tree_iter_root_step (.Ok ss vs) a5 b5 pkSeed tree
    (idx / 2 / 2 / 2 / 2) hf5 hpk hsel4 hadrs5
  rw [r1] at c1
  rw [r2] at c2
  rw [r3] at c3
  rw [r4] at c4
  rw [r5] at c5
  rw [← h1] at c1
  rw [← h2, ← h1] at c2
  rw [← h3, ← h2, ← h1] at c3
  rw [← h4, ← h3, ← h2, ← h1] at c4
  rw [← h5, ← h4, ← h3, ← h2, ← h1] at c5
  exact ⟨c0, c1, c2, c3, c4, c5⟩

end NiceTry.Fors.Bridge
