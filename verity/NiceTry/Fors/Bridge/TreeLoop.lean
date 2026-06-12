import NiceTry.Fors.Bridge.TreeArith
import NiceTry.Fors.Bridge.InterpLoop

/-!
# M3: the 25-iteration tree-loop induction (A4)

Runs `fun_recover`'s `for { } lt(usr_t, 25) { post } { body }` from the loop
invariant at `t` down to the exit at `t = 25`, collecting the 25 root words
with their closed-form chain values.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 2000000

/-! ## Loop-plumbing and word glue -/

theorem mkOk_ok (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore) :
    (👌 (EvmYul.Yul.State.Ok ss vs)) = .Ok ss vs := rfl

theorem reviveJump_ok (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore) :
    (🧟 (EvmYul.Yul.State.Ok ss vs)) = .Ok ss vs := rfl

theorem overwrite?_ok (s' : EvmYul.Yul.State) (ss : SharedState .Yul)
    (vs : EvmYul.Yul.VarStore) :
    (s' ✏️⟦EvmYul.Yul.State.Ok ss vs⟧?) = s' := rfl

theorem uint256_ofNat_add (a b : Nat) (h : a + b < UInt256.size) :
    (UInt256.ofNat a).add (UInt256.ofNat b) = UInt256.ofNat (a + b) := by
  refine uint256_eq_of_toNat ?_
  show ((UInt256.ofNat a).val + (UInt256.ofNat b).val).val = _
  rw [Fin.add_def]
  show ((UInt256.ofNat a).toNat + (UInt256.ofNat b).toNat) % UInt256.size = _
  rw [uint256_ofNat_toNat_of_lt a (by omega), uint256_ofNat_toNat_of_lt b (by omega),
    uint256_ofNat_toNat_of_lt (a + b) h]
  exact Nat.mod_eq_of_lt h

theorem uint256_lt_true (a b : Nat) (ha : a < b) (hb : b < UInt256.size) :
    UInt256.lt (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat 1 := by
  have hP : (UInt256.ofNat a) < (UInt256.ofNat b) := by
    show (UInt256.ofNat a).val < (UInt256.ofNat b).val
    rw [Fin.lt_def]
    show (UInt256.ofNat a).toNat < (UInt256.ofNat b).toNat
    rw [uint256_ofNat_toNat_of_lt a (by omega), uint256_ofNat_toNat_of_lt b hb]
    exact ha
  unfold UInt256.lt UInt256.fromBool Bool.toUInt256
  rw [if_pos (decide_eq_true hP)]

theorem uint256_lt_self_25 :
    UInt256.lt (UInt256.ofNat 25) (UInt256.ofNat 25) = (⟨0⟩ : UInt256) := by
  unfold UInt256.lt UInt256.fromBool Bool.toUInt256
  rw [show (decide (UInt256.ofNat 25 < UInt256.ofNat 25)) = false from
    decide_eq_false (fun h => absurd
      (show (UInt256.ofNat 25).val < (UInt256.ofNat 25).val from h)
      (lt_irrefl _))]
  rfl

theorem uint256_one_ne_zero : (UInt256.ofNat 1) ≠ (⟨0⟩ : UInt256) := by decide

/-- `shr(5, ·)` composes with the invariant's cursor value. -/
theorem shiftRight_cursor (dC : UInt256) (dVal t : Nat)
    (h : dC.toNat = dVal >>> (5 * t)) :
    (UInt256.shiftRight dC (UInt256.ofNat 5)).toNat = dVal >>> (5 * (t + 1)) := by
  rw [uint256_shiftRight_toNat dC _ (by
      rw [uint256_ofNat_toNat_of_lt 5 (by decide)]; omega),
    uint256_ofNat_toNat_of_lt 5 (by decide), h,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, ← pow_add,
    show 5 * t + 5 = 5 * (t + 1) from by omega]

/-- The invariant's cursor low bits are exactly `indexAt`. -/
theorem cursor_mod_indexAt (dVal t : Nat) :
    (dVal >>> (5 * t)) % 32 = indexAt dVal t := by
  unfold indexAt twoPow A
  rw [Nat.shiftRight_eq_div_pow]

/-! ## `treePostState` resolution (the post block is five inserts) -/

theorem treePost1_ok (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    treePost1 (.Ok a b) = .Ok a (b.insert "usr_t" ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1))) := rfl

theorem treePost2_ok (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    treePost2 (.Ok a b) = .Ok a ((b.insert "usr_t" ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1))).insert "usr_treePtr" ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[ret2Id]!)) := by
  show ((treePost1 (.Ok a b)).insert "usr_treePtr"
      ((treePost1 (.Ok a b))[treePtrId]!.add (treePost1 (.Ok a b))[ret2Id]!)) = _
  rw [treePost1_ok,
    state_getElem_finsert_ne a b _ (show treePtrId ≠ "usr_t" by decide),
    state_getElem_finsert_ne a b _ (show ret2Id ≠ "usr_t" by decide)]
  rfl

theorem treePost3_ok (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    treePost3 (.Ok a b) = .Ok a (((b.insert "usr_t" ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1))).insert "usr_treePtr" ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[ret2Id]!)).insert "usr_rootPtr" ((EvmYul.Yul.State.Ok a b)[rootPtrId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)) := by
  show ((treePost2 (.Ok a b)).insert "usr_rootPtr"
      ((treePost2 (.Ok a b))[rootPtrId]!.add (treePost2 (.Ok a b))[retId]!)) = _
  rw [treePost2_ok,
    state_getElem_finsert_ne a _ _ (show rootPtrId ≠ "usr_treePtr" by decide),
    state_getElem_finsert_ne a b _ (show rootPtrId ≠ "usr_t" by decide),
    state_getElem_finsert_ne a _ _ (show retId ≠ "usr_treePtr" by decide),
    state_getElem_finsert_ne a b _ (show retId ≠ "usr_t" by decide)]
  rfl

theorem treePost4_ok (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    treePost4 (.Ok a b) = .Ok a ((((b.insert "usr_t" ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1))).insert "usr_treePtr" ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[ret2Id]!)).insert "usr_rootPtr" ((EvmYul.Yul.State.Ok a b)[rootPtrId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)).insert "usr_tLeafBase" ((EvmYul.Yul.State.Ok a b)[tLeafBaseId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)) := by
  show ((treePost3 (.Ok a b)).insert "usr_tLeafBase"
      ((treePost3 (.Ok a b))[tLeafBaseId]!.add (treePost3 (.Ok a b))[retId]!)) = _
  rw [treePost3_ok,
    state_getElem_finsert_ne a _ _ (show tLeafBaseId ≠ "usr_rootPtr" by decide),
    state_getElem_finsert_ne a _ _ (show tLeafBaseId ≠ "usr_treePtr" by decide),
    state_getElem_finsert_ne a b _ (show tLeafBaseId ≠ "usr_t" by decide),
    state_getElem_finsert_ne a _ _ (show retId ≠ "usr_rootPtr" by decide),
    state_getElem_finsert_ne a _ _ (show retId ≠ "usr_treePtr" by decide),
    state_getElem_finsert_ne a b _ (show retId ≠ "usr_t" by decide)]
  rfl

theorem treePostState_ok (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    treePostState (.Ok a b) = .Ok a (((((b.insert "usr_t" ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1))).insert "usr_treePtr" ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[ret2Id]!)).insert "usr_rootPtr" ((EvmYul.Yul.State.Ok a b)[rootPtrId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)).insert "usr_tLeafBase" ((EvmYul.Yul.State.Ok a b)[tLeafBaseId]!.add (EvmYul.Yul.State.Ok a b)[retId]!)).insert "usr_dCursor" (UInt256.shiftRight (EvmYul.Yul.State.Ok a b)[dCursorId]! (UInt256.ofNat 5))) := by
  show ((treePost4 (.Ok a b)).insert "usr_dCursor"
      (UInt256.shiftRight (treePost4 (.Ok a b))[dCursorId]! (UInt256.ofNat 5))) = _
  rw [treePost4_ok,
    state_getElem_finsert_ne a _ _ (show dCursorId ≠ "usr_tLeafBase" by decide),
    state_getElem_finsert_ne a _ _ (show dCursorId ≠ "usr_rootPtr" by decide),
    state_getElem_finsert_ne a _ _ (show dCursorId ≠ "usr_treePtr" by decide),
    state_getElem_finsert_ne a b _ (show dCursorId ≠ "usr_t" by decide)]
  rfl

theorem treePostState_toState (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b)).toState = (EvmYul.Yul.State.Ok a b).toState := by
  rw [treePostState_ok]
  rfl

theorem treePostState_toMachineState (a : SharedState .Yul)
    (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b)).toMachineState
      = (EvmYul.Yul.State.Ok a b).toMachineState := by
  rw [treePostState_ok]
  rfl


theorem treePostState_usrT (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b))[usrTId]! = ((EvmYul.Yul.State.Ok a b)[usrTId]!.add (UInt256.ofNat 1)) := by
  rw [treePostState_ok,
    state_getElem_finsert_ne a _ _ (show usrTId ≠ "usr_dCursor" by decide),
    state_getElem_finsert_ne a _ _ (show usrTId ≠ "usr_tLeafBase" by decide),
    state_getElem_finsert_ne a _ _ (show usrTId ≠ "usr_rootPtr" by decide),
    state_getElem_finsert_ne a _ _ (show usrTId ≠ "usr_treePtr" by decide),
    show usrTId = "usr_t" from rfl]
  exact state_getElem_finsert_self a _ "usr_t" _


theorem treePostState_treePtr (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b))[treePtrId]! = ((EvmYul.Yul.State.Ok a b)[treePtrId]!.add (EvmYul.Yul.State.Ok a b)[ret2Id]!) := by
  rw [treePostState_ok,
    state_getElem_finsert_ne a _ _ (show treePtrId ≠ "usr_dCursor" by decide),
    state_getElem_finsert_ne a _ _ (show treePtrId ≠ "usr_tLeafBase" by decide),
    state_getElem_finsert_ne a _ _ (show treePtrId ≠ "usr_rootPtr" by decide),
    show treePtrId = "usr_treePtr" from rfl]
  exact state_getElem_finsert_self a _ "usr_treePtr" _


theorem treePostState_rootPtr (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b))[rootPtrId]! = ((EvmYul.Yul.State.Ok a b)[rootPtrId]!.add (EvmYul.Yul.State.Ok a b)[retId]!) := by
  rw [treePostState_ok,
    state_getElem_finsert_ne a _ _ (show rootPtrId ≠ "usr_dCursor" by decide),
    state_getElem_finsert_ne a _ _ (show rootPtrId ≠ "usr_tLeafBase" by decide),
    show rootPtrId = "usr_rootPtr" from rfl]
  exact state_getElem_finsert_self a _ "usr_rootPtr" _


theorem treePostState_tLeafBase (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b))[tLeafBaseId]! = ((EvmYul.Yul.State.Ok a b)[tLeafBaseId]!.add (EvmYul.Yul.State.Ok a b)[retId]!) := by
  rw [treePostState_ok,
    state_getElem_finsert_ne a _ _ (show tLeafBaseId ≠ "usr_dCursor" by decide),
    show tLeafBaseId = "usr_tLeafBase" from rfl]
  exact state_getElem_finsert_self a _ "usr_tLeafBase" _


theorem treePostState_dCursor (a : SharedState .Yul) (b : EvmYul.Yul.VarStore) :
    (treePostState (.Ok a b))[dCursorId]! = (UInt256.shiftRight (EvmYul.Yul.State.Ok a b)[dCursorId]! (UInt256.ofNat 5)) := by
  rw [treePostState_ok,

    show dCursorId = "usr_dCursor" from rfl]
  exact state_getElem_finsert_self a _ "usr_dCursor" _


theorem treePostState_other (a : SharedState .Yul) (b : EvmYul.Yul.VarStore)
    {y : Identifier} (h1 : y ≠ "usr_t") (h2 : y ≠ "usr_treePtr")
    (h3 : y ≠ "usr_rootPtr") (h4 : y ≠ "usr_tLeafBase") (h5 : y ≠ "usr_dCursor") :
    (treePostState (.Ok a b))[y]! = (EvmYul.Yul.State.Ok a b)[y]! := by
  rw [treePostState_ok,
    state_getElem_finsert_ne a _ _ h5,
    state_getElem_finsert_ne a _ _ h4,
    state_getElem_finsert_ne a _ _ h3,
    state_getElem_finsert_ne a _ _ h2,
    state_getElem_finsert_ne a b _ h1]

/-! ## Closed-form per-tree values and the loop invariant -/

/-- The masked sk word for tree `j` (read at `ptr0 + 96 j`). -/
def loopSk (T : EvmYul.State .Yul) (ptr0 j : Nat) : UInt256 :=
  (EvmYul.State.calldataload T (UInt256.ofNat (ptr0 + 96 * j))).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- The masked auth-sibling word for tree `j` at byte offset `off`. -/
def loopSib (T : EvmYul.State .Yul) (ptr0 j off : Nat) : UInt256 :=
  (EvmYul.State.calldataload T (UInt256.ofNat (ptr0 + 96 * j + off))).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- The closed-form root value of tree `j`: the five-level climb over the leaf. -/
def loopRootV (pk : UInt256) (T : EvmYul.State .Yul) (dVal ptr0 j : Nat) : Nat :=
  climbLevel pk.toNat j 5 (indexAt dVal j / 2 / 2 / 2 / 2)
    (climbLevel pk.toNat j 4 (indexAt dVal j / 2 / 2 / 2)
      (climbLevel pk.toNat j 3 (indexAt dVal j / 2 / 2)
        (climbLevel pk.toNat j 2 (indexAt dVal j / 2)
          (climbLevel pk.toNat j 1 (indexAt dVal j)
            (leafHash pk.toNat (leafAdrs j (indexAt dVal j))
              (loopSk T ptr0 j).toNat)
            (loopSib T ptr0 j 16).toNat)
          (loopSib T ptr0 j 32).toNat)
        (loopSib T ptr0 j 48).toNat)
      (loopSib T ptr0 j 64).toNat)
    (loopSib T ptr0 j 80).toNat

/-- The tree-loop invariant at counter `t`. -/
structure LoopInv (T : EvmYul.State .Yul) (pk : UInt256) (dVal ptr0 : Nat)
    (t : Nat) (s : EvmYul.Yul.State) : Prop where
  toState : s.toState = T
  usrT : s[usrTId]! = UInt256.ofNat t
  treePtr : s[treePtrId]! = UInt256.ofNat (ptr0 + 96 * t)
  rootPtr : s[rootPtrId]! = UInt256.ofNat (0x40 + 32 * t)
  tLeafBase : s[tLeafBaseId]! = UInt256.ofNat (32 * t)
  dCursor : s[dCursorId]!.toNat = dVal >>> (5 * t)
  ret : s[retId]! = UInt256.ofNat 32
  ret2 : s[ret2Id]! = UInt256.ofNat 96
  pkSlot : s.toMachineState.memory.data.extract 0x380 0x3a0 = pk.toByteArray.data
  size : 0x3a0 ≤ s.toMachineState.memory.size
  ptrB : ptr0 + 96 * 25 < UInt256.size

/-- Ok-exposure of the full body exit (the root store keeps the varstore of
    the level-5 selector insert). -/
theorem treeAfterNode5_ok (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore) :
    ∃ a, treeAfterNode5 (.Ok ss vs)
      = .Ok a (vs.insert "usr_s_4" (treeSelector4Word (.Ok ss vs))) := ⟨_, rfl⟩

/-! ## One iteration: body facts -/

set_option maxHeartbeats 4000000 in
/-- **One body iteration from the invariant**: the exit state is `.Ok`, keeps
    the loop variables and calldata view, grows memory to the scratch end,
    preserves everything below the current root slot, keeps the pkSeed slot,
    and writes the closed-form root at `0x40 + 32t`. -/
theorem tree_iter_body_facts
    (T : EvmYul.State .Yul) (pk : UInt256) (dVal ptr0 t : Nat)
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (ht : t < 25)
    (inv : LoopInv T pk dVal ptr0 t (.Ok ss vs)) :
    ∃ (a₂ : SharedState .Yul) (b₂ : EvmYul.Yul.VarStore) (rootW : UInt256),
      treeIterState (.Ok ss vs) = .Ok a₂ b₂
      ∧ (EvmYul.Yul.State.Ok a₂ b₂).toState = T
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[usrTId]! = UInt256.ofNat t
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[treePtrId]! = UInt256.ofNat (ptr0 + 96 * t)
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[rootPtrId]! = UInt256.ofNat (0x40 + 32 * t)
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[tLeafBaseId]! = UInt256.ofNat (32 * t)
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[dCursorId]!.toNat = dVal >>> (5 * t)
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[retId]! = UInt256.ofNat 32
      ∧ (EvmYul.Yul.State.Ok a₂ b₂)[ret2Id]! = UInt256.ofNat 96
      ∧ 0x400 ≤ (EvmYul.Yul.State.Ok a₂ b₂).toMachineState.memory.size
      ∧ (∀ lo hi, hi ≤ 0x40 + 32 * t →
          (EvmYul.Yul.State.Ok a₂ b₂).toMachineState.memory.data.extract lo hi
            = (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract lo hi)
      ∧ (EvmYul.Yul.State.Ok a₂ b₂).toMachineState.memory.data.extract 0x380 0x3a0
          = pk.toByteArray.data
      ∧ (EvmYul.Yul.State.Ok a₂ b₂).toMachineState.memory.data.extract
          (0x40 + 32 * t) (0x40 + 32 * t + 32) = rootW.toByteArray.data
      ∧ rootW.toNat = loopRootV pk T dVal ptr0 t := by
  obtain ⟨hT, husrT, hptr, hroot, hbase, hcur, hret, hret2, hpk, hsize, hptrB⟩ := inv
  -- entry selector facts, in indexAt-parity form
  have hidx32 : indexAt dVal t = (dVal >>> (5 * t)) % 32 := (cursor_mod_indexAt dVal t).symm
  have hsel0 : (treeSelector0Word (.Ok ss vs) = UInt256.ofNat 0 ∧ indexAt dVal t % 2 = 0)
      ∨ (treeSelector0Word (.Ok ss vs) = UInt256.ofNat 32 ∧ indexAt dVal t % 2 ≠ 0) := by
    have h := treeSelector0Word_cases (.Ok ss vs) (dVal >>> (5 * t)) hcur hret
    rwa [show (dVal >>> (5 * t)) % 2 = indexAt dVal t % 2 from by rw [hidx32]; omega] at h
  have hsel1 : (treeSelector1Word (.Ok ss vs) = UInt256.ofNat 0 ∧ indexAt dVal t / 2 % 2 = 0)
      ∨ (treeSelector1Word (.Ok ss vs) = UInt256.ofNat 32 ∧ indexAt dVal t / 2 % 2 ≠ 0) := by
    have h := treeSelector1Word_cases (.Ok ss vs) (dVal >>> (5 * t)) hcur hret
    rwa [show (dVal >>> (5 * t)) / 2 % 2 = indexAt dVal t / 2 % 2 from by
      rw [hidx32]; omega] at h
  have hsel2 : (treeSelector2Word (.Ok ss vs) = UInt256.ofNat 0
        ∧ indexAt dVal t / 2 / 2 % 2 = 0)
      ∨ (treeSelector2Word (.Ok ss vs) = UInt256.ofNat 32
        ∧ indexAt dVal t / 2 / 2 % 2 ≠ 0) := by
    have h := treeSelector2Word_cases (.Ok ss vs) (dVal >>> (5 * t)) hcur hret
    rwa [show (dVal >>> (5 * t)) / 4 % 2 = indexAt dVal t / 2 / 2 % 2 from by
      rw [hidx32]; omega] at h
  have hsel3 : (treeSelector3Word (.Ok ss vs) = UInt256.ofNat 0
        ∧ indexAt dVal t / 2 / 2 / 2 % 2 = 0)
      ∨ (treeSelector3Word (.Ok ss vs) = UInt256.ofNat 32
        ∧ indexAt dVal t / 2 / 2 / 2 % 2 ≠ 0) := by
    have h := treeSelector3Word_cases (.Ok ss vs) (dVal >>> (5 * t)) hcur hret hret2
    rwa [show (dVal >>> (5 * t)) / 8 % 2 = indexAt dVal t / 2 / 2 / 2 % 2 from by
      rw [hidx32]; omega] at h
  have hsel4 : (treeSelector4Word (.Ok ss vs) = UInt256.ofNat 0
        ∧ indexAt dVal t / 2 / 2 / 2 / 2 % 2 = 0)
      ∨ (treeSelector4Word (.Ok ss vs) = UInt256.ofNat 32
        ∧ indexAt dVal t / 2 / 2 / 2 / 2 % 2 ≠ 0) := by
    have h := treeSelector4Word_cases (.Ok ss vs) (dVal >>> (5 * t)) hcur hret
    rwa [show (dVal >>> (5 * t)) / 16 % 2 = indexAt dVal t / 2 / 2 / 2 / 2 % 2 from by
      rw [hidx32]; omega] at h
  -- entry ADRS facts, in indexAt form
  have hadrsL : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
      (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat
        = shapeLeafAdrsWord t (indexAt dVal t) := by
    have h := treeLeafAdrsWord_eq (.Ok ss vs) t (dVal >>> (5 * t)) ht hbase hcur
    rwa [cursor_mod_indexAt] at h
  have hadrs1 : (treeNodeAdrsWord (.Ok ss vs) 4 1 15
      1020847100762815390390123822299599601664).toNat
        = shapeNodeAdrsWord t 1 (indexAt dVal t / 2) := by
    have h := treeNodeAdrsWord1_eq (.Ok ss vs) t (dVal >>> (5 * t)) ht husrT hcur
    rwa [show (dVal >>> (5 * t)) / 2 ^ 1 % 2 ^ 4 = indexAt dVal t / 2 from by
      rw [hidx32]; omega] at h
  have hadrs2 : (treeNodeAdrsWord (.Ok ss vs) 3 2 7
      1020847100762815390390123822303894568960).toNat
        = shapeNodeAdrsWord t 2 (indexAt dVal t / 2 / 2) := by
    have h := treeNodeAdrsWord2_eq (.Ok ss vs) t (dVal >>> (5 * t)) ht husrT hcur
    rwa [show (dVal >>> (5 * t)) / 2 ^ 2 % 2 ^ 3 = indexAt dVal t / 2 / 2 from by
      rw [hidx32]; omega] at h
  have hadrs3 : (treeNodeAdrsWord (.Ok ss vs) 2 3 3
      1020847100762815390390123822308189536256).toNat
        = shapeNodeAdrsWord t 3 (indexAt dVal t / 2 / 2 / 2) := by
    have h := treeNodeAdrsWord3_eq (.Ok ss vs) t (dVal >>> (5 * t)) ht husrT hcur
    rwa [show (dVal >>> (5 * t)) / 2 ^ 3 % 2 ^ 2 = indexAt dVal t / 2 / 2 / 2 from by
      rw [hidx32]; omega] at h
  have hadrs4 : (treeNodeAdrsWord (.Ok ss vs) 1 4 1
      1020847100762815390390123822312484503552).toNat
        = shapeNodeAdrsWord t 4 (indexAt dVal t / 2 / 2 / 2 / 2) := by
    have h := treeNodeAdrsWord4_eq (.Ok ss vs) t (dVal >>> (5 * t)) ht husrT hcur
    rwa [show (dVal >>> (5 * t)) / 2 ^ 4 % 2 ^ 1 = indexAt dVal t / 2 / 2 / 2 / 2 from by
      rw [hidx32]; omega] at h
  have hadrs5 : ((EvmYul.Yul.State.Ok ss vs)[usrTId]!.lor
      (UInt256.ofNat 1020847100762815390390123822316779470848)).toNat
        = shapeNodeAdrsWord t 5 (indexAt dVal t / 2 / 2 / 2 / 2 / 2) := by
    have h := treeNode5AdrsWord_eq (.Ok ss vs) t ht husrT
    rwa [show (0 : Nat) = indexAt dVal t / 2 / 2 / 2 / 2 / 2 from by
      rw [hidx32]
      have := Nat.mod_lt (dVal >>> (5 * t)) (show 0 < 32 by norm_num)
      omega] at h
  -- the step chain
  obtain ⟨s1a, s1b, h1, hf1, r1, c0⟩ :=
    tree_iter_leaf_step ss vs pk t (indexAt dVal t) hpk hsize hret2 hadrsL
  obtain ⟨s2a, s2b, h2, hf2, r2, c1⟩ :=
    tree_iter_node1_step (.Ok ss vs) s1a s1b pk t (indexAt dVal t) hf1 hpk hsel0 hadrs1
  obtain ⟨s3a, s3b, h3, hf3, r3, c2⟩ :=
    tree_iter_node2_step (.Ok ss vs) s2a s2b pk t (indexAt dVal t / 2) hf2 hpk
      hsel1 hadrs2
  obtain ⟨s4a, s4b, h4, hf4, r4, c3⟩ :=
    tree_iter_node3_step (.Ok ss vs) s3a s3b pk t (indexAt dVal t / 2 / 2) hf3 hpk
      hsel2 hadrs3
  obtain ⟨s5a, s5b, h5, hf5, r5, c4⟩ :=
    tree_iter_node4_step (.Ok ss vs) s4a s4b pk t (indexAt dVal t / 2 / 2 / 2) hf4 hpk
      hsel3 hadrs4
  have c5 := tree_iter_root_step (.Ok ss vs) s5a s5b pk t
    (indexAt dVal t / 2 / 2 / 2 / 2) hf5 hpk hsel4 hadrs5
  -- chain the values into the closed form
  rw [r1] at c1
  rw [r2, c1] at c2
  rw [r3, c2] at c3
  rw [r4, c3] at c4
  rw [r5, c4] at c5
  rw [c0] at c5
  -- the body exit state
  obtain ⟨aF, hF⟩ := treeAfterNode5_ok s5a s5b
  have hIter : treeIterState (.Ok ss vs)
      = .Ok aF (s5b.insert "usr_s_4" (treeSelector4Word (.Ok s5a s5b))) := by
    show treeAfterNode5 (treeAfterNode4 (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
      (treeAfterLeafHash (.Ok ss vs)))))) = _
    rw [h1, h2, h3, h4, h5, hF]
  -- exit lookups
  have hex : ∀ y : Identifier, y ≠ "usr_s_4" →
      (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
        (treeSelector4Word (.Ok s5a s5b))))[y]!
        = (EvmYul.Yul.State.Ok s5a s5b)[y]! := fun y hy => by
    rw [state_getElem_finsert_ne aF s5b _ hy]
    exact state_getElem_shared_irrel aF s5a s5b y
  -- exit memory
  have hsel4d : treeSelector4Word (.Ok s5a s5b) = UInt256.ofNat 0
      ∨ treeSelector4Word (.Ok s5a s5b) = UInt256.ofNat 32 := by
    rw [treeSelector4Word_of_facts hf5]
    exact hsel4.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hchainM := node_chain_memory_facts (EvmYul.Yul.State.Ok s5a s5b).toMachineState
    ((EvmYul.Yul.State.Ok s5a s5b)[usrTId]!.lor
      (UInt256.ofNat 1020847100762815390390123822316779470848))
    (EvmYul.Yul.State.Ok s5a s5b)[usrNode4Id]!
    (treeMaskedCalldataWord (.Ok s5a s5b)
      ((EvmYul.Yul.State.Ok s5a s5b)[treePtrId]!.add (UInt256.ofNat 80)))
    (treeSelector4Word (.Ok s5a s5b)) hsel4d hf5.size
  have hp32 : (UInt256.ofNat (0x40 + 32 * t)).toNat = 0x40 + 32 * t :=
    uint256_ofNat_toNat_of_lt _ (by
      have h832 : (832 : Nat) < UInt256.size := by decide
      omega)
  have hrootM := root_store_memory_facts
    ((((EvmYul.Yul.State.Ok s5a s5b).toMachineState.mstore (UInt256.ofNat 0x3a0)
        ((EvmYul.Yul.State.Ok s5a s5b)[usrTId]!.lor
          (UInt256.ofNat 1020847100762815390390123822316779470848))).mstore
        ((UInt256.ofNat 0x3c0).xor (treeSelector4Word (.Ok s5a s5b)))
        (EvmYul.Yul.State.Ok s5a s5b)[usrNode4Id]!).mstore
        ((UInt256.ofNat 0x3e0).xor (treeSelector4Word (.Ok s5a s5b)))
        (treeMaskedCalldataWord (.Ok s5a s5b)
          ((EvmYul.Yul.State.Ok s5a s5b)[treePtrId]!.add (UInt256.ofNat 80))))
    (UInt256.ofNat (0x40 + 32 * t))
    (treeRootWord (treeAfterSibling5 (.Ok s5a s5b)))
    (by rw [hp32]; omega)
    (by rw [hchainM.2]; omega)
  have hmem : (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
      (treeSelector4Word (.Ok s5a s5b)))).toMachineState.memory
      = (((((EvmYul.Yul.State.Ok s5a s5b).toMachineState.mstore (UInt256.ofNat 0x3a0)
          ((EvmYul.Yul.State.Ok s5a s5b)[usrTId]!.lor
            (UInt256.ofNat 1020847100762815390390123822316779470848))).mstore
          ((UInt256.ofNat 0x3c0).xor (treeSelector4Word (.Ok s5a s5b)))
          (EvmYul.Yul.State.Ok s5a s5b)[usrNode4Id]!).mstore
          ((UInt256.ofNat 0x3e0).xor (treeSelector4Word (.Ok s5a s5b)))
          (treeMaskedCalldataWord (.Ok s5a s5b)
            ((EvmYul.Yul.State.Ok s5a s5b)[treePtrId]!.add (UInt256.ofNat 80)))).mstore
          (UInt256.ofNat (0x40 + 32 * t))
          (treeRootWord (treeAfterSibling5 (.Ok s5a s5b)))).memory := by
    rw [← hF]
    have h := treeAfterNode5_memory s5a s5b
    rw [hf5.rootPtr, hroot, treeAfterSibling5_chain] at h
    exact h
  refine ⟨aF, _, treeRootWord (treeAfterSibling5 (.Ok s5a s5b)), hIter,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hF, treeAfterNode5_toState s5a s5b, hf5.toState]
    exact hT
  · exact ((hex usrTId (by decide)).trans hf5.usrT).trans husrT
  · exact ((hex treePtrId (by decide)).trans hf5.treePtr).trans hptr
  · exact ((hex rootPtrId (by decide)).trans hf5.rootPtr).trans hroot
  · exact ((hex tLeafBaseId (by decide)).trans hf5.tLeafBase).trans hbase
  · rw [hex dCursorId (by decide), hf5.dCursor]
    exact hcur
  · exact ((hex retId (by decide)).trans hf5.ret).trans hret
  · exact ((hex ret2Id (by decide)).trans hf5.ret2).trans hret2
  · rw [show (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
        (treeSelector4Word (.Ok s5a s5b)))).toMachineState.memory.size
        = _ from congrArg ByteArray.size hmem,
      hrootM.1, hchainM.2]
    omega
  · intro lo hi hhi
    rw [show (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
        (treeSelector4Word (.Ok s5a s5b)))).toMachineState.memory.data
        = _ from congrArg ByteArray.data hmem,
      hrootM.2.2.1 lo hi (by rw [hp32]; omega),
      hchainM.1 lo hi (by omega)]
    exact hf5.low lo hi (by omega)
  · rw [show (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
        (treeSelector4Word (.Ok s5a s5b)))).toMachineState.memory.data
        = _ from congrArg ByteArray.data hmem,
      hrootM.2.2.2 0x380 0x3a0 (by rw [hp32]; omega),
      hchainM.1 0x380 0x3a0 (by omega),
      hf5.low 0x380 0x3a0 (by omega)]
    exact hpk
  · rw [show (EvmYul.Yul.State.Ok aF (s5b.insert "usr_s_4"
        (treeSelector4Word (.Ok s5a s5b)))).toMachineState.memory.data
        = _ from congrArg ByteArray.data hmem]
    have h := hrootM.2.1
    rwa [hp32] at h
  · -- the closed-form value
    have hsk : loopSk T ptr0 t = treeSkWord (.Ok ss vs) := by
      unfold loopSk treeSkWord
      rw [hT, hptr]
    have hs16 : loopSib T ptr0 t 16 = treeMaskedCalldataWord (.Ok ss vs)
        ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16)) := by
      unfold loopSib treeMaskedCalldataWord
      rw [hT, hptr, uint256_ofNat_add _ _ (by omega)]
    have hs32 : loopSib T ptr0 t 32 = treeMaskedCalldataWord (.Ok ss vs)
        ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add
          (EvmYul.Yul.State.Ok ss vs)[retId]!) := by
      unfold loopSib treeMaskedCalldataWord
      rw [hT, hptr, hret, uint256_ofNat_add _ _ (by omega)]
    have hs48 : loopSib T ptr0 t 48 = treeMaskedCalldataWord (.Ok ss vs)
        ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 48)) := by
      unfold loopSib treeMaskedCalldataWord
      rw [hT, hptr, uint256_ofNat_add _ _ (by omega)]
    have hs64 : loopSib T ptr0 t 64 = treeMaskedCalldataWord (.Ok ss vs)
        ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 64)) := by
      unfold loopSib treeMaskedCalldataWord
      rw [hT, hptr, uint256_ofNat_add _ _ (by omega)]
    have hs80 : loopSib T ptr0 t 80 = treeMaskedCalldataWord (.Ok ss vs)
        ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 80)) := by
      unfold loopSib treeMaskedCalldataWord
      rw [hT, hptr, uint256_ofNat_add _ _ (by omega)]
    show (treeRootWord (treeAfterSibling5 (.Ok s5a s5b))).toNat
        = loopRootV pk T dVal ptr0 t
    unfold loopRootV
    rw [hsk, hs16, hs32, hs48, hs64, hs80]
    exact c5



/-! ## One iteration: body + post, with the invariant restored -/

/-- One full iteration (body + post block): the invariant advances to `t+1`,
    everything below the just-written root slot is preserved, and the slot
    holds the closed-form root. -/
theorem tree_iter_step_full
    (T : EvmYul.State .Yul) (pk : UInt256) (dVal ptr0 t : Nat)
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (ht : t < 25)
    (inv : LoopInv T pk dVal ptr0 t (.Ok ss vs)) :
    ∃ (a₂ : SharedState .Yul) (b₂ : EvmYul.Yul.VarStore) (rootW : UInt256),
      treeIterState (.Ok ss vs) = .Ok a₂ b₂
      ∧ LoopInv T pk dVal ptr0 (t + 1) (treePostState (.Ok a₂ b₂))
      ∧ (∀ lo hi, hi ≤ 0x40 + 32 * t →
          (treePostState (.Ok a₂ b₂)).toMachineState.memory.data.extract lo hi
            = (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract lo hi)
      ∧ (treePostState (.Ok a₂ b₂)).toMachineState.memory.data.extract
          (0x40 + 32 * t) (0x40 + 32 * t + 32) = rootW.toByteArray.data
      ∧ rootW.toNat = loopRootV pk T dVal ptr0 t := by
  obtain ⟨a₂, b₂, rootW, hIter, hT', hu, hp, hr, hb, hd, hrt, hr2, hsz, hlow,
    hpks, hslot, hval⟩ := tree_iter_body_facts T pk dVal ptr0 t ss vs ht inv
  refine ⟨a₂, b₂, rootW, hIter, ?_, ?_, ?_, hval⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.ptrB⟩
    · rw [treePostState_toState]
      exact hT'
    · rw [treePostState_usrT, hu, uint256_ofNat_add t 1 (by
        have h26 : (26 : Nat) < UInt256.size := by decide
        omega)]
    · rw [treePostState_treePtr, hp, hr2,
        uint256_ofNat_add _ _ (by have := inv.ptrB; omega),
        show ptr0 + 96 * t + 96 = ptr0 + 96 * (t + 1) from by omega]
    · rw [treePostState_rootPtr, hr, hrt,
        uint256_ofNat_add _ _ (by
          have h864 : (900 : Nat) < UInt256.size := by decide
          omega),
        show 0x40 + 32 * t + 32 = 0x40 + 32 * (t + 1) from by omega]
    · rw [treePostState_tLeafBase, hb, hrt,
        uint256_ofNat_add _ _ (by
          have h832 : (900 : Nat) < UInt256.size := by decide
          omega),
        show 32 * t + 32 = 32 * (t + 1) from by omega]
    · rw [treePostState_dCursor]
      exact shiftRight_cursor _ dVal t hd
    · rw [treePostState_other a₂ b₂ (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact hrt
    · rw [treePostState_other a₂ b₂ (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact hr2
    · rw [treePostState_toMachineState]
      exact hpks
    · rw [treePostState_toMachineState]
      omega
  · intro lo hi hhi
    rw [treePostState_toMachineState]
    exact hlow lo hi hhi
  · rw [treePostState_toMachineState]
    exact hslot

/-! ## The 25-iteration loop run -/

set_option linter.unusedSimpArgs false in
/-- **The tree loop, run to completion.** From the invariant at `t` (with
    `t + k = 25`), the `for` statement executes to an `.Ok` state satisfying
    the invariant at 25, preserving memory below the slot region written so
    far, with every remaining root slot `j ∈ [t, 25)` holding its closed-form
    chain value. -/
theorem tree_loop_run (T : EvmYul.State .Yul) (pk : UInt256) (dVal ptr0 : Nat)
    (co : Option YulContract) :
    ∀ (k t : Nat), t + k = 25 →
    ∀ (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore),
      LoopInv T pk dVal ptr0 t (.Ok ss vs) →
    ∀ n : Nat,
      ∃ (ssf : SharedState .Yul) (vsf : EvmYul.Yul.VarStore)
        (rootsW : Nat → UInt256),
        exec (n + 3 * k + 46) (.For forsTreeCond forsTreePost forsTreeBody) co
            (.Ok ss vs)
          = .ok (.Ok ssf vsf)
        ∧ LoopInv T pk dVal ptr0 25 (.Ok ssf vsf)
        ∧ (∀ lo hi, hi ≤ 0x40 + 32 * t →
            (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract lo hi
              = (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract lo hi)
        ∧ (∀ j, t ≤ j → j < 25 →
            (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract
              (0x40 + 32 * j) (0x40 + 32 * j + 32) = (rootsW j).toByteArray.data
            ∧ (rootsW j).toNat = loopRootV pk T dVal ptr0 j) := by
  intro k
  induction k with
  | zero =>
    intro t hk ss vs inv n
    have ht : t = 25 := by omega
    subst ht
    refine ⟨ss, vs, fun _ => UInt256.ofNat 0, ?_, inv,
      fun lo hi _ => rfl, fun j hj hj' => absurd hj' (by omega)⟩
    have hcond : eval (n + 43) forsTreeCond co (👌 (EvmYul.Yul.State.Ok ss vs))
        = .ok (.Ok ss vs, (⟨0⟩ : UInt256)) := by
      rw [mkOk_ok]
      have h := eval_tree_cond (n := n + 37) (co := co) (s := .Ok ss vs)
      rw [inv.usrT, uint256_lt_self_25] at h
      exact h
    have hres := loop_exit (n := n + 43) (post := forsTreePost)
      (body := forsTreeBody) hcond
    rw [overwrite?_ok] at hres
    rw [show n + 3 * 0 + 46 = (n + 45) + 1 from by omega,
      exec_for (n := n + 45),
      show n + 45 = (n + 43) + 2 from by omega]
    exact hres
  | succ k ih =>
    intro t hk ss vs inv n
    have ht : t < 25 := by omega
    obtain ⟨a₂, b₂, rootW, hIter, inv', hlow, hslot, hval⟩ :=
      tree_iter_step_full T pk dVal ptr0 t ss vs ht inv
    rw [treePostState_ok] at inv' hlow hslot
    obtain ⟨ssf, vsf, rootsW', hexec, hinvf, hlowf, hrootsf⟩ :=
      ih (t + 1) (by omega) a₂ _ inv' n
    refine ⟨ssf, vsf, (fun j => if j = t then rootW else rootsW' j), ?_, hinvf,
      ?_, ?_⟩
    · have hcond : eval (n + 3 * k + 46) forsTreeCond co
          (👌 (EvmYul.Yul.State.Ok ss vs))
          = .ok (.Ok ss vs, UInt256.ofNat 1) := by
        rw [mkOk_ok]
        have h := eval_tree_cond (n := n + 3 * k + 40) (co := co) (s := .Ok ss vs)
        rw [inv.usrT, uint256_lt_true t 25 ht (by decide)] at h
        exact h
      have hbody : exec (n + 3 * k + 46) (.Block forsTreeBody) co (.Ok ss vs)
          = .ok (.Ok a₂ b₂) := by
        rw [show n + 3 * k + 46 = (n + 3 * k + 3) + 43 from by omega,
          exec_tree_body_iter (n + 3 * k + 3) co ss vs, hIter]
      have hpost : exec (n + 3 * k + 46) (.Block forsTreePost) co
          (🧟 (EvmYul.Yul.State.Ok a₂ b₂))
          = .ok (treePostState (.Ok a₂ b₂)) := by
        rw [reviveJump_ok,
          show n + 3 * k + 46 = (n + 3 * k + 35) + 11 from by omega]
        exact exec_tree_post (n + 3 * k + 35) co (.Ok a₂ b₂)
      have hfor : exec (n + 3 * k + 46)
          (.For forsTreeCond forsTreePost forsTreeBody) co
          ((treePostState (.Ok a₂ b₂)) ✏️⟦EvmYul.Yul.State.Ok ss vs⟧?)
          = .ok (.Ok ssf vsf) := by
        rw [overwrite?_ok, treePostState_ok]
        exact hexec
      have hres := loop_step (n := n + 3 * k + 46) (co := co)
        (s := .Ok ss vs) hcond uint256_one_ne_zero hbody hpost hfor
      rw [overwrite?_ok] at hres
      rw [show n + 3 * (k + 1) + 46 = ((n + 3 * k + 46) + 2) + 1 from by omega,
        exec_for (n := (n + 3 * k + 46) + 2)]
      exact hres
    · intro lo hi hhi
      rw [hlowf lo hi (by omega)]
      exact hlow lo hi hhi
    · intro j hj hj'
      by_cases hjt : j = t
      · subst hjt
        simp only [if_pos rfl]
        refine ⟨?_, hval⟩
        rw [hlowf _ _ (by omega)]
        exact hslot
      · simp only [if_neg hjt]
        exact hrootsf j (by omega) hj'


/-- **The loop from `t = 0`** — the entry point the pre-loop trace instantiates:
    all 25 root slots get their closed-form chain values. -/
theorem tree_loop_run_from_zero (T : EvmYul.State .Yul) (pk : UInt256)
    (dVal ptr0 : Nat) (co : Option YulContract)
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (inv : LoopInv T pk dVal ptr0 0 (.Ok ss vs)) (n : Nat) :
    ∃ (ssf : SharedState .Yul) (vsf : EvmYul.Yul.VarStore)
      (rootsW : Nat → UInt256),
      exec (n + 121) (.For forsTreeCond forsTreePost forsTreeBody) co (.Ok ss vs)
        = .ok (.Ok ssf vsf)
      ∧ LoopInv T pk dVal ptr0 25 (.Ok ssf vsf)
      ∧ (∀ lo hi, hi ≤ 0x40 →
          (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract lo hi
            = (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract lo hi)
      ∧ (∀ j, j < 25 →
          (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract
            (0x40 + 32 * j) (0x40 + 32 * j + 32) = (rootsW j).toByteArray.data
          ∧ (rootsW j).toNat = loopRootV pk T dVal ptr0 j) := by
  obtain ⟨ssf, vsf, rootsW, hexec, hinv, hlow, hroots⟩ :=
    tree_loop_run T pk dVal ptr0 co 25 0 rfl ss vs inv n
  refine ⟨ssf, vsf, rootsW, ?_, hinv, fun lo hi hhi => hlow lo hi (by omega),
    fun j hj => hroots j (by omega) hj⟩
  rw [show n + 121 = n + 3 * 25 + 46 from by omega]
  exact hexec

end NiceTry.Fors.Bridge
