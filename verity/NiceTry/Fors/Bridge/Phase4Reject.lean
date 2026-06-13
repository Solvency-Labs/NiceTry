import NiceTry.Fors.Bridge.EvmRunRecover
import NiceTry.Fors.Bridge.Phase4Accept
import NiceTry.Fors.Bridge.TreeEntryFront
import NiceTry.Fors.Bridge.TreeFinal

/-!
# Phase 4 reject paths

This module owns the Phase 4 reject-path facts that are independent of the
accept/tree-loop proof:

* the internal `fun_recover` bad-length guard, stated over the actual EVM word
  comparison;
* the forced-zero guard body from the named post-hmsg state, including the
  `mstore(0, 0); return(0, 0x20)` zero-return plumbing.

The model-side equality between `recoverHmsgDVal` and `dValOf` is intentionally
not duplicated here.  The exported forced-zero interface carries that equality as
its only model premise.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors
open NiceTry.Fors.Proofs.Basic

set_option maxHeartbeats 2000000

/-! ## Small UInt256 facts -/

private theorem uint256_eq_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  unfold UInt256.eq UInt256.fromBool
  simp [h]

private theorem uint256_isZero_zero :
    (UInt256.ofNat 0).isZero = UInt256.ofNat 1 := by
  rfl

/-! ## Invalid-length guard -/

/-- The good-prefix state with only the actual recover length word varied.

`recoverEntryState` in `ClassA.lean` is intentionally specialized to the good
`SigLen` call.  The internal length guard itself depends only on
`var_sig_length` and `expr`, so this state isolates the actual word-level guard
condition without pretending that all `Nat` lengths inject into `UInt256`. -/
def recoverAfterRet3FromRet2WithLength
    (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet3FromRet2 raw digest).insert "var_sig_length" (UInt256.ofNat raw.len)

theorem recoverAfterRet3FromRet2WithLength_lookup_sig_length
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "var_sig_length"
        (recoverAfterRet3FromRet2WithLength raw digest) =
      UInt256.ofNat raw.len := by
  rfl

theorem recoverAfterRet3FromRet2WithLength_lookup_expr
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "expr"
        (recoverAfterRet3FromRet2WithLength raw digest) =
      UInt256.ofNat SigLen := by
  rfl

/-- The internal bad-length guard evaluates to nonzero exactly under the EVM-word
    inequality that `fun_recover` actually tests. -/
theorem eval_recover_length_reject_guard_word_ne
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hword : UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen) :
    eval (n + 28) recoverLengthRejectGuardExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest, UInt256.ofNat 1) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hsig :
      EvmYul.Yul.State.lookup! "var_sig_length" s = UInt256.ofNat raw.len := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_sig_length raw digest
  have hexpr :
      EvmYul.Yul.State.lookup! "expr" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact recoverAfterRet3FromRet2WithLength_lookup_expr raw digest
  have hvarSig : eval (n + 22) (.Var "var_sig_length") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat raw.len) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_length" s) =
      Except.ok (s, UInt256.ofNat raw.len)
    rw [hsig]
  have hvarExpr : eval (n + 24) (.Var "expr") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat SigLen) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "expr" s) =
      Except.ok (s, UInt256.ofNat SigLen)
    rw [hexpr]
  have heq : eval (n + 26)
        (.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"])
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
    have hraw := eval_binop2 (n := n + 20) (co := some forsVerifierRuntime) (OP := .EQ)
        (f := UInt256.eq)
        (primCall_eq (n := n + 24) (s := s)
          (UInt256.ofNat raw.len) (UInt256.ofNat SigLen))
        hvarSig hvarExpr
    simpa [uint256_eq_of_ne hword] using hraw
  change eval (n + 28)
      (.Call (Sum.inl .ISZERO)
        [.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"]])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 1)
  simpa [recoverLengthRejectGuardExpr, uint256_isZero_zero] using
    (eval_unop1 (n := n + 24) (co := some forsVerifierRuntime) (OP := .ISZERO)
      (f := UInt256.isZero)
      (primCall_iszero (n := n + 26) (s := s) (UInt256.ofNat 0)) heq)

/-- The length-reject body sets the return variable to zero and leaves. -/
theorem exec_recover_length_reject_body_zero
    (s : EvmYul.Yul.State) (co : Option YulContract) (n : Nat) :
    exec (n + 3) (.Block recoverLengthRejectBody) co s =
      .ok (🚪 (s.insert "var" (UInt256.ofNat 0))) := by
  rw [show recoverLengthRejectBody =
      [.Let ["var"] (.some (.Lit (UInt256.ofNat 0))), .Leave] from rfl]
  rw [exec_block_cons_ok (n := n + 2) (co := co) (s := s)
    (st := .Let ["var"] (.some (.Lit (UInt256.ofNat 0)))) (sts := [.Leave])
    (s₁ := s.insert "var" (UInt256.ofNat 0))
    (h := by simpa using
      (exec_let_lit (n := n + 1) (co := co) (s := s)
        (vars := ["var"]) (lit := UInt256.ofNat 0)))]
  rw [exec_block_cons_ok (n := n + 1) (co := co)
    (s := s.insert "var" (UInt256.ofNat 0))
    (st := .Leave) (sts := [])
    (s₁ := 🚪 (s.insert "var" (UInt256.ofNat 0)))
    (h := exec_leave (n := n) (co := co)
      (s := s.insert "var" (UInt256.ofNat 0)))]
  exact exec_block_nil (n := n) (co := co)
    (s := 🚪 (s.insert "var" (UInt256.ofNat 0)))

theorem exec_recover_length_reject_if_word_ne
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hword : UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen) :
    exec (n + 29) (.If recoverLengthRejectGuardExpr recoverLengthRejectBody)
        (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest) =
      .ok (🚪 ((recoverAfterRet3FromRet2 raw digest).insert
        "var" (UInt256.ofNat 0))) := by
  rw [exec_if_true
    (n := n + 28) (co := some forsVerifierRuntime)
    (s := recoverAfterRet3FromRet2 raw digest)
    (cond := recoverLengthRejectGuardExpr) (body := recoverLengthRejectBody)
    (s' := recoverAfterRet3FromRet2 raw digest)
    (c := UInt256.ofNat 1)
    (eval_recover_length_reject_guard_word_ne raw digest n hword)
    uint256_one_ne_zero]
  simpa using exec_recover_length_reject_body_zero
    (recoverAfterRet3FromRet2 raw digest)
    (some forsVerifierRuntime) (n + 25)

theorem recover_length_word_ne_of_raw_ne
    (raw : RawSig) (hfit : RawSigLenFitsEvmWord raw)
    (hlen : raw.len ≠ SigLen) :
    UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen := by
  intro hword
  exact hlen ((rawLen_word_eq_sigLen_iff_of_lt raw hfit).1 hword)

/-- The setup prefix of `fun_recover`, stopping immediately before the internal
    signature-length guard. -/
theorem exec_recover_prefix_to_length_guard
    (raw : RawSig) (digest : Digest) (n : Nat) :
    exec (n + 47) (.Block forsFunRecover.body) (some forsVerifierRuntime)
        (recoverEntryState raw digest) =
      exec (n + 30)
        (.Block (.If recoverLengthRejectGuardExpr recoverLengthRejectBody ::
          forsFunRecover.body.drop 18))
        (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest) := by
  rw [show forsFunRecover.body =
      (.Let ["var"] (.some (.Lit (UInt256.ofNat 0)))) ::
        forsFunRecover.body.drop 1 from rfl]
  rw [exec_block_cons_ok (n := n + 46) (h := by
    simpa [recoverAfterVarInit] using
      (exec_let_lit (n := n + 45) (co := some forsVerifierRuntime)
        (s := recoverEntryState raw digest)
        (vars := ["var"]) (lit := UInt256.ofNat 0)))]
  change exec (n + 46) (.Block (forsFunRecover.body.drop 1))
      (some forsVerifierRuntime) (recoverAfterVarInit raw digest) =
    exec (n + 30)
      (.Block (.If recoverLengthRejectGuardExpr recoverLengthRejectBody ::
        forsFunRecover.body.drop 18))
      (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest)
  rw [show forsFunRecover.body.drop 1 =
      (.Let ["expr"] (.some (.Call (Sum.inr "constant_FORS_SIG_LEN") []))) ::
        forsFunRecover.body.drop 2 from rfl]
  rw [exec_block_cons_ok (n := n + 45)
    (h := exec_recover_let_expr_const (base := n + 2) raw digest)]
  rw [exec_recover_ret_init_after_expr (base := n) raw digest]
  rw [exec_recover_prefix_to_ret1_product (base := n) raw digest]
  exact exec_recover_to_length_guard (base := n) raw digest

/-! ## `evmRunRecover` zero-result plumbing -/

/-- The scoped observable normalizes malformed lengths to the contract's zero
    result after the exact internal word guard has been checked above. -/
theorem evmRunRecover_bad_length
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len ≠ SigLen) :
    evmRunRecover raw digest = 0 := by
  simp [evmRunRecover, hlen]

theorem evmRunRecover_zero_of_run_none
    (raw : RawSig) (digest : Digest)
    (h : runForsRecover raw digest recoverFuel = none) :
    evmRunRecover raw digest = 0 := by
  unfold evmRunRecover
  split
  · rw [h]
    rfl
  · rfl

theorem evmRunRecover_zero_of_run_some {raw : RawSig} {digest : Digest}
    {w : UInt256}
    (h : runForsRecover raw digest recoverFuel = some w)
    (hw : w.toNat % 2 ^ 160 = 0) :
    evmRunRecover raw digest = 0 := by
  unfold evmRunRecover
  split
  · rw [h]
    simpa using hw
  · rfl

theorem evmRunRecover_zero_of_call_ok_zero
    (raw : RawSig) (digest : Digest) {s : EvmYul.Yul.State}
    (h : call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
      .ok (s, [UInt256.ofNat 0])) :
    evmRunRecover raw digest = 0 := by
  apply evmRunRecover_zero_of_run_some (w := UInt256.ofNat 0)
  · unfold runForsRecover
    rw [h]
    simp
  · decide

theorem evmRunRecover_zero_of_call_yulhalt_zero
    (raw : RawSig) (digest : Digest) {s : EvmYul.Yul.State} {v}
    (h : call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
      .error (.YulHalt s v))
    (hret : fromByteArrayBigEndian s.sharedState.H_return = 0) :
    evmRunRecover raw digest = 0 := by
  apply evmRunRecover_zero_of_run_some (w := UInt256.ofNat 0)
  · unfold runForsRecover
    rw [h]
    simp [hret]
  · decide

/-! ## Forced-zero guard -/

def recoverForcedZeroGuardExpr : Expr :=
  .Call (Sum.inl .AND)
    [.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 125), .Var "usr_dVal"],
     .Lit (UInt256.ofNat 31)]

def recoverForcedZeroRejectBody : List Stmt :=
  [.ExprStmtCall (.Call (Sum.inl .MSTORE)
      [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)]),
   .ExprStmtCall (.Call (Sum.inl .RETURN)
      [.Lit (UInt256.ofNat 0), .Var "ret"])]

def recoverForcedZeroRejectReturnState
    (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  let s₁ := s.setMachineState
    (s.toMachineState.mstore (UInt256.ofNat 0) (UInt256.ofNat 0))
  s₁.setMachineState (s₁.toMachineState.evmReturn
    (UInt256.ofNat 0) (UInt256.ofNat 0x20))

theorem eval_recover_forced_zero_guard
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (co : Option YulContract) (dv : UInt256) (n : Nat)
    (hdv : EvmYul.Yul.State.lookup! "usr_dVal" (.Ok ss vs) = dv) :
    eval (n + 28) recoverForcedZeroGuardExpr co (.Ok ss vs) =
      .ok (.Ok ss vs,
        (UInt256.shiftRight dv (UInt256.ofNat 125)).land (UInt256.ofNat 31)) := by
  have hshr : eval (n + 24)
      (.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 125), .Var "usr_dVal"])
      co (.Ok ss vs) =
    .ok (.Ok ss vs, UInt256.shiftRight dv (UInt256.ofNat 125)) := by
    have h := eval_tree_shr_lit_var (n := n + 18) (co := co) (s := .Ok ss vs)
      (b := UInt256.ofNat 125) (x := "usr_dVal")
    rw [state_getElem!_eq_lookup!, hdv] at h
    exact h
  have h := eval_binop2 (n := n + 22) (co := co) (s := .Ok ss vs) (OP := .AND)
    (f := UInt256.land)
    (hprim := primCall_and (n := n + 26) (s := .Ok ss vs)
      (UInt256.shiftRight dv (UInt256.ofNat 125)) (UInt256.ofNat 31))
    (he₁ := hshr) (he₂ := eval_lit (n := n + 25))
  simpa [recoverForcedZeroGuardExpr] using h

/-- `mstore(0, 0); return(0, ret)` from a post-hmsg state whose `ret` is `0x20`
    halts with the zero word in return data. -/
theorem exec_recover_forced_zero_reject_body_zero
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
    (co : Option YulContract) (n : Nat)
    (hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 0x20) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 8) (.Block recoverForcedZeroRejectBody) co (.Ok ss vs)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  let s : EvmYul.Yul.State := .Ok ss vs
  let s₁ : EvmYul.Yul.State :=
    s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0) (UInt256.ofNat 0))
  refine ⟨s₁.setMachineState (s₁.toMachineState.evmReturn
      (UInt256.ofNat 0) (UInt256.ofNat 0x20)), ?_, ?_⟩
  · rw [show recoverForcedZeroRejectBody =
        [.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)]),
         .ExprStmtCall (.Call (Sum.inl .RETURN)
          [.Lit (UInt256.ofNat 0), .Var "ret"])] from rfl]
    rw [exec_block_cons_ok (n := n + 7) (co := co) (s := s)
      (st := .ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)]))
      (sts := [.ExprStmtCall (.Call (Sum.inl .RETURN)
        [.Lit (UInt256.ofNat 0), .Var "ret"])])
      (s₁ := s₁)
      (h := by
        simpa [s, s₁] using
          (exec_mstore_lit (n := n + 1) (co := co) (s := s)
            (a := UInt256.ofNat 0) (v := UInt256.ofNat 0)
            (e := .Lit (UInt256.ofNat 0))
            (he := eval_lit (n := n + 4))))]
    exact exec_block_cons_err (n := n + 6) (co := co) (s := s₁)
      (st := .ExprStmtCall (.Call (Sum.inl .RETURN)
        [.Lit (UInt256.ofNat 0), .Var "ret"])) (sts := [])
      (e := .YulHalt
        (s₁.setMachineState (s₁.toMachineState.evmReturn
          (UInt256.ofNat 0) (UInt256.ofNat 0x20))) ⟨1⟩)
      (h := by
        have hret₁ : s₁[retId]! = UInt256.ofNat 0x20 := by
          simpa [s₁, s] using
            (setMachineState_getElem s
              (s.toMachineState.mstore (UInt256.ofNat 0) (UInt256.ofNat 0))
              retId).trans hret
        have h := exec_return_stmt (n := n) (co := co) (s := s₁)
          (a := UInt256.ofNat 0) (x := "ret")
        rw [show ("ret" : Identifier) = retId from rfl, hret₁] at h
        simpa [s₁] using h)
  · dsimp [s₁, s]
    let M := (EvmYul.Yul.State.Ok ss vs).toMachineState.mstore
      (UInt256.ofNat 0) (UInt256.ofNat 0)
    change fromByteArrayBigEndian
      (M.evmReturn (UInt256.ofNat 0) (UInt256.ofNat 0x20)).H_return = 0
    have hsize : 32 ≤ M.memory.size := by
      have hsz := mstore_memory_size'
        (EvmYul.Yul.State.Ok ss vs).toMachineState
        (UInt256.ofNat 0) (UInt256.ofNat 0)
        (by rw [uint256_ofNat_toNat_of_lt _ (by decide)]; omega)
      dsimp [M]
      rw [hsz, uint256_ofNat_toNat_of_lt _ (by decide)]
      omega
    have hslot0 :
        M.memory.data.extract 0 32 = (UInt256.ofNat 0).toByteArray.data := by
      have h := mstore_extract_self'
        (EvmYul.Yul.State.Ok ss vs).toMachineState
        (UInt256.ofNat 0) (UInt256.ofNat 0)
        (by rw [uint256_ofNat_toNat_of_lt _ (by decide)]; omega)
      rw [uint256_ofNat_toNat_of_lt _ (by decide)] at h
      simpa [M] using h
    have hread : M.memory.readWithPadding 0 32 =
        (UInt256.ofNat 0).toByteArray := by
      apply ByteArray.ext
      rw [readWithPadding_prefix _ 32 hsize (by omega) (by decide),
        ByteArray.data_extract]
      exact hslot0
    have hHr :
        (M.evmReturn (UInt256.ofNat 0) (UInt256.ofNat 0x20)).H_return =
          M.memory.readWithPadding 0 32 := by
      show M.memory.readWithPadding (UInt256.ofNat 0).toNat
          (UInt256.ofNat 0x20).toNat = _
      rw [uint256_ofNat_toNat_of_lt _ (by decide),
        uint256_ofNat_toNat_of_lt _ (by decide)]
    rw [hHr, hread, fromBE_toByteArray]
    rfl

theorem exec_recover_forced_zero_reject_from_hmsg
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hguard : (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
        (UInt256.ofNat 31) ≠ (⟨0⟩ : UInt256)) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 30) (.Block (forsFunRecover.body.drop 25)) (some forsVerifierRuntime)
          (recoverAfterHmsg raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  obtain ⟨ss, vs, hs⟩ := recoverAfterHmsg_ok raw digest
  have hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 0x20 := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_ret raw digest
  have hdv : EvmYul.Yul.State.lookup! "usr_dVal" (.Ok ss vs) =
      recoverHmsgDVal raw digest := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_dVal raw digest
  obtain ⟨S, hbody, hzero⟩ :=
    exec_recover_forced_zero_reject_body_zero ss vs
      (some forsVerifierRuntime) (n + 20) hret
  refine ⟨S, ?_, hzero⟩
  rw [hs]
  rw [show forsFunRecover.body.drop 25
      = (.If recoverForcedZeroGuardExpr recoverForcedZeroRejectBody)
        :: forsFunRecover.body.drop 26 from rfl]
  rw [exec_block_cons_err (n := n + 29) (co := some forsVerifierRuntime)
    (s := .Ok ss vs)
    (st := .If recoverForcedZeroGuardExpr recoverForcedZeroRejectBody)
    (sts := forsFunRecover.body.drop 26)
    (e := .YulHalt S ⟨1⟩)
    (h := by
      rw [exec_if_true
        (n := n + 28) (co := some forsVerifierRuntime)
        (s := .Ok ss vs)
        (cond := recoverForcedZeroGuardExpr)
        (body := recoverForcedZeroRejectBody)
        (s' := .Ok ss vs)
        (c := (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
          (UInt256.ofNat 31))
        (eval_recover_forced_zero_guard ss vs (some forsVerifierRuntime)
          (recoverHmsgDVal raw digest) n hdv)
        hguard]
      simpa using hbody)]

/-! ## Model-side interface for Worker A's hmsg equality -/

/-- Worker A supplies this premise by connecting the contract hmsg word to the
    model's `dValOf`. -/
def RecoverHmsgMatchesDVal (raw : RawSig) (digest : Digest) : Prop :=
  recoverHmsgDVal raw digest = UInt256.ofNat (dValOf raw digest)

/-- Model rejection implies that the exact UInt256 guard consumed by Yul is
    nonzero. -/
theorem recoverHmsg_guard_ne_zero_of_forcedZero_false
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = false) :
    (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
      (UInt256.ofNat 31) ≠ (⟨0⟩ : UInt256) := by
  intro hzero
  have hcalc :
      ((UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
        (UInt256.ofNat 31)).toNat =
        evmOmittedIndexShape (dValOf raw digest) := by
    rw [uint256_land_toNat]
    rw [uint256_shiftRight_toNat _ _ (by
      rw [show (UInt256.ofNat 125).toNat = 125 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      decide)]
    rw [recoverHmsgDVal_toNat_eq_dValOf raw digest hwf hdigest]
    rw [show (UInt256.ofNat 125).toNat = 125 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
    rw [show (UInt256.ofNat 31).toNat = 31 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
    rw [Nat.shiftRight_eq_div_pow]
    rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  have hshapeZero : evmOmittedIndexShape (dValOf raw digest) = 0 := by
    rw [← hcalc, hzero]
    rfl
  have hshape := forcedZero_eq_evm_shape (dValOf raw digest)
  rw [hfz, hshapeZero] at hshape
  simp at hshape

/-- Parameterized forced-zero reject interface.  Its only model-side premise is
    `RecoverHmsgMatchesDVal`; the rest is the concrete EVM guard/body trace. -/
theorem exec_recover_forced_zero_reject_from_hmsg_matches
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hmatch : RecoverHmsgMatchesDVal raw digest)
    (hguard : (UInt256.shiftRight (UInt256.ofNat (dValOf raw digest))
        (UInt256.ofNat 125)).land (UInt256.ofNat 31) ≠ (⟨0⟩ : UInt256)) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 30) (.Block (forsFunRecover.body.drop 25)) (some forsVerifierRuntime)
          (recoverAfterHmsg raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  apply exec_recover_forced_zero_reject_from_hmsg raw digest n
  rw [hmatch]
  exact hguard

/-- Forced-zero rejection for the complete `fun_recover` body. -/
theorem exec_recover_forced_zero_reject_body
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = false) :
    ∃ S : EvmYul.Yul.State,
      exec 154 (.Block forsFunRecover.body) (some forsVerifierRuntime)
          (recoverEntryState raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  have hguard :=
    recoverHmsg_guard_ne_zero_of_forcedZero_false raw digest hwf hdigest hfz
  obtain ⟨S, hsuffix, hzero⟩ :=
    exec_recover_forced_zero_reject_from_hmsg raw digest 99 hguard
  refine ⟨S, ?_, hzero⟩
  rw [show 154 = 107 + 47 by omega,
    exec_recover_good_prefix_to_hmsg raw digest 107 hlen]
  rw [show 107 + 29 = 99 + 37 by omega,
    exec_recover_hmsg_named raw digest (some forsVerifierRuntime) 99]
  simpa using hsuffix

/-- Forced-zero rejection entered through the actual scoped function call. -/
theorem call_recover_forced_zero_reject
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = false) :
    ∃ S : EvmYul.Yul.State,
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  obtain ⟨S, hbody, hzero⟩ :=
    exec_recover_forced_zero_reject_body raw digest hlen hwf hdigest hfz
  refine ⟨S, ?_, hzero⟩
  unfold recoverFuel
  apply call_err
    (dispatcherBeforeRecoverState_account_find raw digest)
    (by simpa using forsVerifierRuntime_lookup_fun_recover)
  simpa [recoverEntryState, recoverGoodArgs, forsRecoverArgs] using hbody

/-- The scoped executable returns zero on the model forced-zero reject branch. -/
theorem evmRunRecover_forced_zero_reject
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = false) :
    evmRunRecover raw digest = 0 := by
  obtain ⟨S, hcall, hzero⟩ :=
    call_recover_forced_zero_reject raw digest hlen hwf hdigest hfz
  exact evmRunRecover_zero_of_call_yulhalt_zero raw digest hcall hzero

/-! ## Dispatcher-routing lifts -/

/-- Once the scoped `fun_recover` bad-length theorem is available, this is the
    exact `h_len` branch expected by `forsRefines_of_branches`. -/
theorem evmRun_h_len_of_evmRunRecover
    (hrec : ∀ raw digest, RawSigLenFitsEvmWord raw →
      raw.len ≠ SigLen → evmRunRecover raw digest = 0) :
    ∀ raw digest, RawSigLenFitsEvmWord raw →
      raw.len ≠ SigLen → evmRun raw digest = 0 := by
  intro raw digest hfit hlen
  rw [dispatcher_routes_to_recover raw digest hfit]
  exact hrec raw digest hfit hlen

/-- Once the scoped `fun_recover` forced-zero theorem is available, this is the
    exact `h_guard` branch expected by `forsRefines_of_branches`. -/
theorem evmRun_h_guard_of_evmRunRecover
    (hrec : ∀ raw digest, raw.len = SigLen →
      forcedZero (dValOf raw digest) = false → evmRunRecover raw digest = 0) :
    ∀ raw digest, raw.len = SigLen →
      forcedZero (dValOf raw digest) = false → evmRun raw digest = 0 := by
  intro raw digest hlen hguard
  rw [evmRun_eq_recover_of_sigLen raw digest hlen]
  exact hrec raw digest hlen hguard

end NiceTry.Fors.Bridge
