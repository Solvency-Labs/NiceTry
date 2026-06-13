import NiceTry.Fors.Bridge.EvmRunRecover
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
    (raw : RawSig) (digest : Digest)
    (hword : UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen) :
    eval 28 recoverLengthRejectGuardExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2WithLength raw digest) =
      .ok (recoverAfterRet3FromRet2WithLength raw digest, UInt256.ofNat 1) := by
  let s := recoverAfterRet3FromRet2WithLength raw digest
  have hsig :
      EvmYul.Yul.State.lookup! "var_sig_length" s = UInt256.ofNat raw.len := by
    dsimp [s]
    exact recoverAfterRet3FromRet2WithLength_lookup_sig_length raw digest
  have hexpr :
      EvmYul.Yul.State.lookup! "expr" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact recoverAfterRet3FromRet2WithLength_lookup_expr raw digest
  have hvarSig : eval 22 (.Var "var_sig_length") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat raw.len) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_length" s) =
      Except.ok (s, UInt256.ofNat raw.len)
    rw [hsig]
  have hvarExpr : eval 24 (.Var "expr") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat SigLen) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "expr" s) =
      Except.ok (s, UInt256.ofNat SigLen)
    rw [hexpr]
  have heq : eval 26
        (.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"])
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
    have hraw := eval_binop2 (n := 20) (co := some forsVerifierRuntime) (OP := .EQ)
        (f := UInt256.eq)
        (primCall_eq (n := 24) (s := s)
          (UInt256.ofNat raw.len) (UInt256.ofNat SigLen))
        hvarSig hvarExpr
    simpa [uint256_eq_of_ne hword] using hraw
  change eval 28
      (.Call (Sum.inl .ISZERO)
        [.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"]])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 1)
  simpa [recoverLengthRejectGuardExpr, uint256_isZero_zero] using
    (eval_unop1 (n := 24) (co := some forsVerifierRuntime) (OP := .ISZERO)
      (f := UInt256.isZero)
      (primCall_iszero (n := 26) (s := s) (UInt256.ofNat 0)) heq)

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
    (raw : RawSig) (digest : Digest)
    (hword : UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen) :
    exec 29 (.If recoverLengthRejectGuardExpr recoverLengthRejectBody)
        (some forsVerifierRuntime) (recoverAfterRet3FromRet2WithLength raw digest) =
      .ok (🚪 ((recoverAfterRet3FromRet2WithLength raw digest).insert
        "var" (UInt256.ofNat 0))) := by
  rw [exec_if_true
    (n := 28) (co := some forsVerifierRuntime)
    (s := recoverAfterRet3FromRet2WithLength raw digest)
    (cond := recoverLengthRejectGuardExpr) (body := recoverLengthRejectBody)
    (s' := recoverAfterRet3FromRet2WithLength raw digest)
    (c := UInt256.ofNat 1)
    (eval_recover_length_reject_guard_word_ne raw digest hword)
    uint256_one_ne_zero]
  simpa using exec_recover_length_reject_body_zero
    (recoverAfterRet3FromRet2WithLength raw digest)
    (some forsVerifierRuntime) 25

theorem recover_length_word_ne_of_raw_ne
    (raw : RawSig) (hfit : RawSigLenFitsEvmWord raw)
    (hlen : raw.len ≠ SigLen) :
    UInt256.ofNat raw.len ≠ UInt256.ofNat SigLen := by
  intro hword
  exact hlen ((rawLen_word_eq_sigLen_iff_of_lt raw hfit).1 hword)

/-! ## `evmRunRecover` zero-result plumbing -/

theorem evmRunRecover_zero_of_run_none
    (raw : RawSig) (digest : Digest)
    (h : runForsRecover raw digest 100000 = none) :
    evmRunRecover raw digest = 0 := by
  unfold evmRunRecover
  rw [h]
  rfl

theorem evmRunRecover_zero_of_run_some {raw : RawSig} {digest : Digest}
    {w : UInt256}
    (h : runForsRecover raw digest 100000 = some w)
    (hw : w.toNat % 2 ^ 160 = 0) :
    evmRunRecover raw digest = 0 := by
  unfold evmRunRecover
  rw [h]
  simpa using hw

theorem evmRunRecover_zero_of_call_ok_zero
    (raw : RawSig) (digest : Digest) {s : EvmYul.Yul.State}
    (h : call 100000 (forsRecoverArgs raw digest) (some "fun_recover")
        (some forsVerifierRuntime) (forsInitialState raw digest) =
      .ok (s, [UInt256.ofNat 0])) :
    evmRunRecover raw digest = 0 := by
  apply evmRunRecover_zero_of_run_some (w := UInt256.ofNat 0)
  · unfold runForsRecover
    rw [h]
    simp
  · decide

theorem evmRunRecover_zero_of_call_yulhalt_zero
    (raw : RawSig) (digest : Digest) {s : EvmYul.Yul.State} {v}
    (h : call 100000 (forsRecoverArgs raw digest) (some "fun_recover")
        (some forsVerifierRuntime) (forsInitialState raw digest) =
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
    (raw : RawSig) (digest : Digest)
    (hguard : (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
        (UInt256.ofNat 31) ≠ (⟨0⟩ : UInt256)) :
    ∃ S : EvmYul.Yul.State,
      exec 30 (.Block (forsFunRecover.body.drop 25)) (some forsVerifierRuntime)
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
      (some forsVerifierRuntime) 20 hret
  refine ⟨S, ?_, hzero⟩
  rw [hs]
  rw [show forsFunRecover.body.drop 25
      = (.If recoverForcedZeroGuardExpr recoverForcedZeroRejectBody)
        :: forsFunRecover.body.drop 26 from rfl]
  rw [exec_block_cons_err (n := 29) (co := some forsVerifierRuntime)
    (s := .Ok ss vs)
    (st := .If recoverForcedZeroGuardExpr recoverForcedZeroRejectBody)
    (sts := forsFunRecover.body.drop 26)
    (e := .YulHalt S ⟨1⟩)
    (h := by
      rw [exec_if_true
        (n := 28) (co := some forsVerifierRuntime)
        (s := .Ok ss vs)
        (cond := recoverForcedZeroGuardExpr)
        (body := recoverForcedZeroRejectBody)
        (s' := .Ok ss vs)
        (c := (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
          (UInt256.ofNat 31))
        (eval_recover_forced_zero_guard ss vs (some forsVerifierRuntime)
          (recoverHmsgDVal raw digest) 0 hdv)
        hguard]
      simpa using hbody)]

/-! ## Model-side interface for Worker A's hmsg equality -/

/-- Worker A supplies this premise by connecting the contract hmsg word to the
    model's `dValOf`. -/
def RecoverHmsgMatchesDVal (raw : RawSig) (digest : Digest) : Prop :=
  recoverHmsgDVal raw digest = UInt256.ofNat (dValOf raw digest)

/-- Parameterized forced-zero reject interface.  Its only model-side premise is
    `RecoverHmsgMatchesDVal`; the rest is the concrete EVM guard/body trace. -/
theorem exec_recover_forced_zero_reject_from_hmsg_matches
    (raw : RawSig) (digest : Digest)
    (hmatch : RecoverHmsgMatchesDVal raw digest)
    (hguard : (UInt256.shiftRight (UInt256.ofNat (dValOf raw digest))
        (UInt256.ofNat 125)).land (UInt256.ofNat 31) ≠ (⟨0⟩ : UInt256)) :
    ∃ S : EvmYul.Yul.State,
      exec 30 (.Block (forsFunRecover.body.drop 25)) (some forsVerifierRuntime)
          (recoverAfterHmsg raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return = 0 := by
  apply exec_recover_forced_zero_reject_from_hmsg
  rw [hmatch]
  exact hguard

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
