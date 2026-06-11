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

end NiceTry.Fors.Bridge
