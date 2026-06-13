import NiceTry.Fors.Bridge.TreePreLoop

/-!
# `fun_recover` pre-loop statement trace (body[18:32])

This file runs the interpreter through `fun_recover`'s pre-loop prefix — the hmsg
construction (statements 18–24), the forced-zero guard skip (25), and the five
loop-variable initializations (26–31) — landing at the `for`-loop entry state and
discharging `LoopInv 0` for `tree_loop_run_from_zero`.

The hmsg window is built by five `mstore`s on a 96-byte entry memory (the recover
entry inherits the dispatcher's `mstore(64, 0x80)` free-memory pointer write — and,
equivalently, the bare `runForsRecover` entry differs only below `0xa0`, all of
which these stores overwrite). Slots 0–2 land in-bounds; slots 3–4 are padding
stores that grow memory to exactly `0xa0`. `hmsg_window_after_5` carries that
threading once.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

/-! ## The five-store hmsg window over a 96-byte entry -/

private theorem o0_toNat : (UInt256.ofNat 0).toNat = 0 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o20_toNat : (UInt256.ofNat 0x20).toNat = 0x20 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o40_toNat : (UInt256.ofNat 0x40).toNat = 0x40 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o60_toNat : (UInt256.ofNat 0x60).toNat = 0x60 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o80_toNat : (UInt256.ofNat 128).toNat = 128 :=
  uint256_ofNat_toNat_of_lt _ (by decide)

/-- The state after the five hmsg `mstore`s, abbreviated. -/
def hmsgMem (m : MachineState) (w0 w1 w2 w3 w4 : UInt256) : MachineState :=
  ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
    (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).mstore
    (UInt256.ofNat 128) w4

/-- Sizes through the five-store chain over a 96-byte entry. -/
private theorem hmsg_sizes (m : MachineState) (w0 w1 w2 w3 _w4 : UInt256)
    (hsize : m.memory.size = 96) :
    (m.mstore (UInt256.ofNat 0) w0).memory.size = 96
    ∧ ((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).memory.size = 96
    ∧ (((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
        (UInt256.ofNat 0x40) w2).memory.size = 96
    ∧ ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
        (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).memory.size = 128 := by
  have s1 : (m.mstore (UInt256.ofNat 0) w0).memory.size = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o0_toNat, hsize]; try omega), hsize]
  have s2 : ((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).memory.size
      = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o20_toNat, s1]; try omega), s1]
  have s3 : (((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
      (UInt256.ofNat 0x40) w2).memory.size = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o40_toNat, s2]; try omega), s2]
  have s4 : ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
      (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).memory.size = 128 := by
    rw [mstore_pad_size _ _ _ (by rw [o60_toNat, s3]) (by rw [o60_toNat]; decide),
      o60_toNat]
  exact ⟨s1, s2, s3, s4⟩

/-- The five hmsg `mstore`s over a 96-byte entry write the transcript window
    `[0, 0xa0)` as the five words and leave memory at size `0xa0`. -/
theorem hmsg_window_after_5 (m : MachineState) (w0 w1 w2 w3 w4 : UInt256)
    (hsize : m.memory.size = 96) :
    (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x00 0x20 = w0.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x20 0x40 = w1.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x40 0x60 = w2.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x60 0x80 = w3.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x80 0xa0 = w4.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.size = 0xa0 := by
  obtain ⟨s1, s2, s3, s4⟩ := hmsg_sizes m w0 w1 w2 w3 w4 hsize
  set m1 := m.mstore (UInt256.ofNat 0) w0 with hm1
  set m2 := m1.mstore (UInt256.ofNat 0x20) w1 with hm2
  set m3 := m2.mstore (UInt256.ofNat 0x40) w2 with hm3
  set m4 := m3.mstore (UInt256.ofNat 0x60) w3 with hm4
  have hb0 : (UInt256.ofNat 0).toNat + 32 ≤ m.memory.size := by rw [o0_toNat, hsize]; try omega
  have hb1 : (UInt256.ofNat 0x20).toNat + 32 ≤ m1.memory.size := by rw [o20_toNat, s1]; try omega
  have hb2 : (UInt256.ofNat 0x40).toNat + 32 ≤ m2.memory.size := by rw [o40_toNat, s2]; try omega
  have hpad3 : m3.memory.size ≤ (UInt256.ofNat 0x60).toNat := by rw [o60_toNat, s3]
  have hpad4 : m4.memory.size ≤ (UInt256.ofNat 128).toNat := by rw [o80_toNat, s4]
  have hsmall3 : (UInt256.ofNat 0x60).toNat < 2 ^ 32 := by rw [o60_toNat]; decide
  have hsmall4 : (UInt256.ofNat 128).toNat < 2 ^ 32 := by rw [o80_toNat]; decide
  -- Final state size
  have hszF : (hmsgMem m w0 w1 w2 w3 w4).memory.size = 0xa0 := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.size = 0xa0
    rw [mstore_pad_size _ _ _ hpad4 hsmall4, o80_toNat]
  -- Slot 0: [0, 0x20)
  have e0 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x00 0x20 = w0.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x00 0x20 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (by left; rw [o40_toNat]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb1 (by left; rw [o20_toNat]; try omega)]
    have h := mstore_extract_self m (UInt256.ofNat 0) w0 hb0
    rw [o0_toNat] at h
    exact h
  -- Slot 1: [0x20, 0x40)
  have e1 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x20 0x40 = w1.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x20 0x40 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (by left; rw [o40_toNat]; try omega)]
    have h := mstore_extract_self m1 (UInt256.ofNat 0x20) w1 hb1
    rw [o20_toNat] at h
    exact h
  -- Slot 2: [0x40, 0x60)
  have e2 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x40 0x60 = w2.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x40 0x60 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    have h := mstore_extract_self m2 (UInt256.ofNat 0x40) w2 hb2
    rw [o40_toNat] at h
    exact h
  -- Slot 3: [0x60, 0x80)
  have e3 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x60 0x80 = w3.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x60 0x80 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    have h := mstore_pad_extract_self m3 (UInt256.ofNat 0x60) w3 hpad3 hsmall3
    rw [o60_toNat] at h
    exact h
  -- Slot 4: [0x80, 0xa0)
  have e4 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x80 0xa0 = w4.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x80 0xa0 = _
    have h := mstore_pad_extract_self m4 (UInt256.ofNat 128) w4 hpad4 hsmall4
    rw [o80_toNat] at h
    exact h
  exact ⟨e0, e1, e2, e3, e4, hszF⟩

/-! ## Front-half statement helpers (body[18:24]) -/

/-- General read-through of `setMachineState` (it never touches the var-store), for
    ANY state — the front-half threads reads of `ret`/`ret_2`/`var_sig_offset` back
    through the five hmsg `mstore`s (= `setMachineState`s). Generalizes
    `ok_set_getElem`, which requires an `Ok` base. -/
theorem setMachineState_getElem (s : EvmYul.Yul.State) (m : MachineState)
    (y : Identifier) :
    (s.setMachineState m)[y]! = s[y]! := by
  cases s <;> rfl



/-- `let x := keccak256(<lit>, <lit>)` — the `usr_dVal` hash (body[24]). -/
theorem exec_let_keccak_lit_lit {n co} {s : EvmYul.Yul.State} {x : Identifier}
    {off len : UInt256} :
    exec (n+8) (.Let [x] (.some (.Call (Sum.inl .KECCAK256) [.Lit off, .Lit len]))) co s
      = .ok ((s.setMachineState (s.toMachineState.keccak256 off len).2).insert x
              (s.toMachineState.keccak256 off len).1) := by
  rw [exec_let_prim (n := n+7)]
  show execPrimCall (n+7) .KECCAK256 [x]
      (reverse' (evalArgs (n+7) [.Lit len, .Lit off] co s)) = _
  rw [evalArgs_cons_ok (n := n+6) (h := eval_lit (n := n+5)),
    evalTail_cons_ok (n := n+5),
    evalArgs_cons_ok (n := n+4) (h := eval_lit (n := n+3)),
    evalTail_cons_ok (n := n+3), evalArgs_nil (n := n+2)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_keccak256 (n := n+6) s off len), multifill_single]

/-- `let x := and(calldataload(add(var, lit)), not(mask))` — the masked `usr_pkSeed`
    header read (body[18]). -/
theorem exec_let_masked_addvlit {n co} {s : EvmYul.Yul.State}
    {x var : Identifier} {b mask : UInt256} :
    exec (n+12) (.Let [x] (.some (.Call (Sum.inl .AND)
        [.Call (Sum.inl .CALLDATALOAD) [.Call (Sum.inl .ADD) [.Var var, .Lit b]],
         .Call (Sum.inl .NOT) [.Lit mask]]))) co s
      = .ok (s.insert x
          ((EvmYul.State.calldataload s.toState (s[var]!.add b)).land mask.lnot)) :=
  exec_let_binop (n := n+6) (co := co) (s := s) (x := x) (OP := .AND)
    (e₁ := .Call (Sum.inl .CALLDATALOAD) [.Call (Sum.inl .ADD) [.Var var, .Lit b]])
    (e₂ := .Call (Sum.inl .NOT) [.Lit mask])
    (v₁ := EvmYul.State.calldataload s.toState (s[var]!.add b))
    (v₂ := mask.lnot)
    (out := (EvmYul.State.calldataload s.toState (s[var]!.add b)).land mask.lnot)
    (hprim := primCall_and (n := n+10) (s := s)
      (EvmYul.State.calldataload s.toState (s[var]!.add b)) mask.lnot)
    (he₁ := eval_unop1 (n := n+4) (co := co) (s := s) (OP := .CALLDATALOAD)
      (f := EvmYul.State.calldataload s.toState)
      (hprim := primCall_calldataload (n := n+6) (s := s) (s[var]!.add b))
      (he := eval_tree_add_var_lit (n := n) (co := co) (s := s) (x := var) (b := b)))
    (he₂ := eval_not_mask (n := n+6) mask)

/-! ## Back-half trace: forced-zero skip + loop-var inits (body[25:32]) -/

private def dValReadId : Identifier := "usr_dVal"


/-- The loop-entry state: the post-keccak state after `mstore(0x380, usr_pkSeed)`
    and the five loop-variable bindings. -/
def loopEntryState (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (pk dv : UInt256) : EvmYul.Yul.State :=
  ((((((EvmYul.Yul.State.Ok ss vs).setMachineState
      ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x380) pk)).insert
      "usr_t" (UInt256.ofNat 0)).insert
      "usr_treePtr" ((UInt256.ofNat 100).add (UInt256.ofNat 0x20))).insert
      "usr_rootPtr" (UInt256.ofNat 0x40)).insert
      "usr_tLeafBase" (UInt256.ofNat 0)).insert
      "usr_dCursor" dv

private theorem o380_toNat : (UInt256.ofNat 0x380).toNat = 0x380 :=
  uint256_ofNat_toNat_of_lt _ (by decide)

/-- `loopEntryState` normalized to a single `Ok` with nested var-store inserts. -/
theorem loopEntryState_ok (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (pk dv : UInt256) :
    loopEntryState ss vs pk dv
      = .Ok { ss with toMachineState :=
                (EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x380) pk }
          (((((vs.insert "usr_t" (UInt256.ofNat 0)).insert
              "usr_treePtr" ((UInt256.ofNat 100).add (UInt256.ofNat 0x20))).insert
              "usr_rootPtr" (UInt256.ofNat 0x40)).insert
              "usr_tLeafBase" (UInt256.ofNat 0)).insert
              "usr_dCursor" dv) := rfl

/-- `loopEntryState`'s machine state is the pre-keccak machine state with
    `pkSeed` parked at `0x380`. -/
theorem loopEntry_toMachineState (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (pk dv : UInt256) :
    (loopEntryState ss vs pk dv).toMachineState
      = (EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x380) pk := rfl

/-- Reading a variable distinct from the five loop variables from `loopEntryState`
    sees the post-keccak base binding. -/
theorem loopEntry_base_read (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (pk dv : UInt256) (y : Identifier)
    (h1 : y ≠ "usr_t") (h2 : y ≠ "usr_treePtr") (h3 : y ≠ "usr_rootPtr")
    (h4 : y ≠ "usr_tLeafBase") (h5 : y ≠ "usr_dCursor") :
    (loopEntryState ss vs pk dv)[y]! = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  rw [loopEntryState_ok,
    state_getElem_finsert_ne _ _ _ h5, state_getElem_finsert_ne _ _ _ h4,
    state_getElem_finsert_ne _ _ _ h3, state_getElem_finsert_ne _ _ _ h2,
    state_getElem_finsert_ne _ _ _ h1]
  exact state_getElem_shared_irrel _ ss vs y

/-- **Back-half pre-loop trace.** From the post-keccak state (`usr_dVal` bound),
    skip the forced-zero guard, run `mstore(0x380, usr_pkSeed)` and the five
    loop-variable initializations, landing at the `for`-loop with `LoopInv 0`. -/
theorem exec_recover_tail_to_loopInv
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore) (co : Option YulContract)
    (pk dv : UInt256) (n : Nat)
    (hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 0x20)
    (hret2 : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hoff : EvmYul.Yul.State.lookup! "var_sig_offset" (.Ok ss vs) = UInt256.ofNat 100)
    (hdv : EvmYul.Yul.State.lookup! "usr_dVal" (.Ok ss vs) = dv)
    (hpk : EvmYul.Yul.State.lookup! "usr_pkSeed" (.Ok ss vs) = pk)
    (hmemsz : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size = 0xa0)
    (hfz : (UInt256.shiftRight dv (UInt256.ofNat 125)).land (UInt256.ofNat 31)
      = (⟨0⟩ : UInt256)) :
    exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co (.Ok ss vs)
      = exec (n + 23) (.Block (forsFunRecover.body.drop 32)) co
          (loopEntryState ss vs pk dv)
    ∧ LoopInv (loopEntryState ss vs pk dv).toState pk dv.toNat 132 0
        (loopEntryState ss vs pk dv) := by
  -- forced-zero guard evaluates to 0
  have hguard : eval (n + 28)
      (.Call (Sum.inl .AND)
        [.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 125), .Var "usr_dVal"],
         .Lit (UInt256.ofNat 31)]) co (.Ok ss vs)
      = .ok (.Ok ss vs, (⟨0⟩ : UInt256)) := by
    have hshr : eval (n + 24)
        (.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 125), .Var "usr_dVal"]) co (.Ok ss vs)
        = .ok (.Ok ss vs, UInt256.shiftRight dv (UInt256.ofNat 125)) := by
      have h := eval_tree_shr_lit_var (n := n + 18) (co := co) (s := .Ok ss vs)
        (b := UInt256.ofNat 125) (x := "usr_dVal")
      rw [state_getElem!_eq_lookup!, hdv] at h
      exact h
    have h := eval_binop2 (n := n + 22) (co := co) (s := .Ok ss vs) (OP := .AND)
      (f := UInt256.land)
      (hprim := primCall_and (n := n + 26) (s := .Ok ss vs)
        (UInt256.shiftRight dv (UInt256.ofNat 125)) (UInt256.ofNat 31))
      (he₁ := hshr) (he₂ := eval_lit (n := n + 25))
    rw [hfz] at h
    exact h
  have hexec : exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co (.Ok ss vs)
      = exec (n + 23) (.Block (forsFunRecover.body.drop 32)) co
          (loopEntryState ss vs pk dv) := by
    rw [show forsFunRecover.body.drop 25
        = (.If (.Call (Sum.inl .AND)
              [.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 125), .Var "usr_dVal"],
               .Lit (UInt256.ofNat 31)])
             [.ExprStmtCall (.Call (Sum.inl .MSTORE)
                [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)]),
              .ExprStmtCall (.Call (Sum.inl .RETURN)
                [.Lit (UInt256.ofNat 0), .Var "ret"])])
          :: forsFunRecover.body.drop 26 from rfl]
    rw [exec_block_cons_ok (n := n + 29) (h := exec_if_false (n := n + 28) hguard)]
    rw [show forsFunRecover.body.drop 26
        = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
            [.Lit (UInt256.ofNat 0x380), .Var "usr_pkSeed"]))
          :: forsFunRecover.body.drop 27 from rfl]
    rw [exec_block_cons_ok (n := n + 28)
      (h := exec_mstore_lit (n := n + 22) (co := co) (s := .Ok ss vs)
        (a := UInt256.ofNat 0x380) (v := pk) (e := .Var "usr_pkSeed")
        (he := by rw [eval_var, state_getElem!_eq_lookup!, hpk]))]
    rw [show forsFunRecover.body.drop 27
        = (.Let ["usr_t"] (.some (.Lit (UInt256.ofNat 0))))
          :: forsFunRecover.body.drop 28 from rfl]
    rw [exec_block_cons_ok (n := n + 27) (h := exec_let_lit (n := n + 26))]
    rw [show forsFunRecover.body.drop 28
        = (.Let ["usr_treePtr"] (.some (.Call (Sum.inl .ADD)
            [.Var "var_sig_offset", .Var "ret"])))
          :: forsFunRecover.body.drop 29 from rfl]
    rw [exec_block_cons_ok (n := n + 26)
      (h := exec_let_binop (n := n + 20) (co := co)
        (x := "usr_treePtr") (OP := .ADD)
        (e₁ := .Var "var_sig_offset") (e₂ := .Var "ret")
        (v₁ := UInt256.ofNat 100) (v₂ := UInt256.ofNat 0x20)
        (out := (UInt256.ofNat 100).add (UInt256.ofNat 0x20))
        (hprim := primCall_add (n := n + 24) (UInt256.ofNat 100) (UInt256.ofNat 0x20))
        (he₁ := by
          rw [eval_var, ok_set_insert_getElem,
            state_getElem_finsert_ne _ _ _
              (show ("var_sig_offset" : Identifier) ≠ ["usr_t"].head! by decide),
            state_getElem!_eq_lookup!, hoff])
        (he₂ := by
          rw [eval_var, ok_set_insert_getElem,
            state_getElem_finsert_ne _ _ _
              (show ("ret" : Identifier) ≠ ["usr_t"].head! by decide),
            show ("ret" : Identifier) = retId from rfl, hret]))]
    rw [show forsFunRecover.body.drop 29
        = (.Let ["usr_rootPtr"] (.some (.Lit (UInt256.ofNat 0x40))))
          :: forsFunRecover.body.drop 30 from rfl]
    rw [exec_block_cons_ok (n := n + 25) (h := exec_let_lit (n := n + 24))]
    rw [show forsFunRecover.body.drop 30
        = (.Let ["usr_tLeafBase"] (.some (.Lit (UInt256.ofNat 0))))
          :: forsFunRecover.body.drop 31 from rfl]
    rw [exec_block_cons_ok (n := n + 24) (h := exec_let_lit (n := n + 23))]
    rw [show forsFunRecover.body.drop 31
        = (.Let ["usr_dCursor"] (.some (.Var "usr_dVal")))
          :: forsFunRecover.body.drop 32 from rfl]
    rw [exec_block_cons_ok (n := n + 23) (h := exec_let_var (n := n + 22))]
    congr 1
    simp only [List.head!_cons]
    unfold loopEntryState
    congr 1
    rw [show ("usr_dVal" : Identifier) = dValReadId from rfl]
    show (EvmYul.Yul.State.Ok
        { ss with toMachineState :=
            (EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x380) pk }
        ((((vs.insert "usr_t" (UInt256.ofNat 0)).insert
            "usr_treePtr" ((UInt256.ofNat 100).add (UInt256.ofNat 0x20))).insert
            "usr_rootPtr" (UInt256.ofNat 0x40)).insert
            "usr_tLeafBase" (UInt256.ofNat 0)))[dValReadId]! = dv
    rw [state_getElem_finsert_ne _ _ _ (show dValReadId ≠ "usr_tLeafBase" by decide),
      state_getElem_finsert_ne _ _ _ (show dValReadId ≠ "usr_rootPtr" by decide),
      state_getElem_finsert_ne _ _ _ (show dValReadId ≠ "usr_treePtr" by decide),
      state_getElem_finsert_ne _ _ _ (show dValReadId ≠ "usr_t" by decide),
      state_getElem_shared_irrel _ ss vs dValReadId, state_getElem!_eq_lookup!,
      show dValReadId = "usr_dVal" from rfl, hdv]
  refine ⟨hexec, ?_⟩
  have hA : (UInt256.ofNat 100).add (UInt256.ofNat 0x20) = UInt256.ofNat 132 :=
    uint256_ofNat_add 100 0x20 (by decide)
  have hpad : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size
      ≤ (UInt256.ofNat 0x380).toNat := by rw [o380_toNat, hmemsz]; decide
  have hsmall : (UInt256.ofNat 0x380).toNat < 2 ^ 32 := by rw [o380_toNat]; decide
  exact {
    toState := rfl
    usrT := by
      rw [loopEntryState_ok,
        state_getElem_finsert_ne _ _ _ (show usrTId ≠ "usr_dCursor" by decide),
        state_getElem_finsert_ne _ _ _ (show usrTId ≠ "usr_tLeafBase" by decide),
        state_getElem_finsert_ne _ _ _ (show usrTId ≠ "usr_rootPtr" by decide),
        state_getElem_finsert_ne _ _ _ (show usrTId ≠ "usr_treePtr" by decide),
        show usrTId = "usr_t" from rfl]
      exact state_getElem_finsert_self _ _ "usr_t" _
    treePtr := by
      rw [loopEntryState_ok,
        state_getElem_finsert_ne _ _ _ (show treePtrId ≠ "usr_dCursor" by decide),
        state_getElem_finsert_ne _ _ _ (show treePtrId ≠ "usr_tLeafBase" by decide),
        state_getElem_finsert_ne _ _ _ (show treePtrId ≠ "usr_rootPtr" by decide),
        show treePtrId = "usr_treePtr" from rfl, state_getElem_finsert_self _ _ "usr_treePtr" _,
        hA]
    rootPtr := by
      rw [loopEntryState_ok,
        state_getElem_finsert_ne _ _ _ (show rootPtrId ≠ "usr_dCursor" by decide),
        state_getElem_finsert_ne _ _ _ (show rootPtrId ≠ "usr_tLeafBase" by decide),
        show rootPtrId = "usr_rootPtr" from rfl, state_getElem_finsert_self _ _ "usr_rootPtr" _]
    tLeafBase := by
      rw [loopEntryState_ok,
        state_getElem_finsert_ne _ _ _ (show tLeafBaseId ≠ "usr_dCursor" by decide),
        show tLeafBaseId = "usr_tLeafBase" from rfl, state_getElem_finsert_self _ _ "usr_tLeafBase" _]
    dCursor := by
      rw [loopEntryState_ok, show dCursorId = "usr_dCursor" from rfl,
        state_getElem_finsert_self _ _ "usr_dCursor" _, Nat.mul_zero, Nat.shiftRight_zero]
    ret := by
      rw [loopEntry_base_read _ _ _ _ retId (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact hret
    ret2 := by
      rw [loopEntry_base_read _ _ _ _ ret2Id (by decide) (by decide) (by decide)
        (by decide) (by decide)]
      exact hret2
    pkSlot := by
      rw [loopEntry_toMachineState]
      have h := mstore_pad_extract_self (EvmYul.Yul.State.Ok ss vs).toMachineState
        (UInt256.ofNat 0x380) pk hpad hsmall
      rw [o380_toNat, show 0x380 + 32 = 0x3a0 from rfl] at h
      exact h
    size := by
      rw [loopEntry_toMachineState, mstore_pad_size _ _ _ hpad hsmall, o380_toNat]
    size400 := Or.inl rfl
    ptrB := by decide
  }

end NiceTry.Fors.Bridge
