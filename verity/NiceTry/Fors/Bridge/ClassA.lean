import NiceTry.Fors.Bridge.CalldataBytes
import NiceTry.Fors.Bridge.InterpCall
import NiceTry.Fors.Bridge.InterpEval

/-!
# Class-A dispatcher setup

Concrete initial-state and expression-evaluation facts for the ABI calldata
`encodeForsCalldata raw digest`. These are the first reusable bricks for the
bad-length trace: they pin down the dispatcher scrutinee and the ABI words before
the proof starts stepping statement blocks.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 800000

/-- Execution environment used by `runForsCalldata` on encoded FORS calldata. -/
def forsInitialEnv (raw : RawSig) (digest : Digest) : EvmYul.ExecutionEnv .Yul :=
  { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with
      calldata := encodeForsCalldata raw digest }

/-- Shared state used by `runForsCalldata`; installs the verifier account so
    user-function calls can enter `fun_recover`. -/
def forsInitialSharedState (raw : RawSig) (digest : Digest) : EvmYul.SharedState .Yul :=
  { (Inhabited.default : EvmYul.SharedState .Yul) with
      executionEnv := forsInitialEnv raw digest,
      accountMap :=
        (Inhabited.default : EvmYul.SharedState .Yul).accountMap.insert
          (forsInitialEnv raw digest).codeOwner
          { (Inhabited.default : EvmYul.Account .Yul) with code := forsVerifierRuntime } }

/-- Initial Yul state for the encoded FORS runtime call. -/
def forsInitialState (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  .Ok (forsInitialSharedState raw digest) Inhabited.default

theorem runForsCalldata_encode_unfold (raw : RawSig) (digest : Digest) (fuel : Nat) :
    runForsCalldata (encodeForsCalldata raw digest) fuel =
      match exec fuel forsDispatcher (some forsVerifierRuntime) (forsInitialState raw digest) with
      | .error (.YulHalt s _) => some (.ofNat (fromByteArrayBigEndian s.sharedState.H_return))
      | _ => none := by
  rfl

theorem forsInitialState_toState_calldata (raw : RawSig) (digest : Digest) :
    (forsInitialState raw digest).toState.executionEnv.calldata =
      encodeForsCalldata raw digest := by
  rfl

theorem forsInitialState_calldata_size (raw : RawSig) (digest : Digest) :
    (forsInitialState raw digest).executionEnv.calldata.size = 2548 := by
  rw [show (forsInitialState raw digest).executionEnv.calldata =
      encodeForsCalldata raw digest by rfl]
  exact encodeForsCalldata_size raw digest

theorem forsInitialState_callvalue (raw : RawSig) (digest : Digest) :
    (forsInitialState raw digest).executionEnv.weiValue = UInt256.ofNat 0 := by
  rfl

/-- `calldatasize()` as it appears in the dispatcher guards. -/
def dispatcherCalldataSizeExpr : Expr :=
  .Call (Sum.inl .CALLDATASIZE) []

/-- `callvalue()` as it appears in the dispatcher guards. -/
def dispatcherCallvalueExpr : Expr :=
  .Call (Sum.inl .CALLVALUE) []

/-- `shr(224, calldataload(0))`, the dispatcher selector scrutinee. -/
def dispatcherSelectorExpr : Expr :=
  .Call (Sum.inl .SHR)
    [.Lit (UInt256.ofNat 224),
     .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)]]

/-- `iszero(lt(calldatasize(), 4))`, the dispatcher's first top-level guard. -/
def dispatcherHasSelectorGuardExpr : Expr :=
  .Call (Sum.inl .ISZERO)
    [.Call (Sum.inl .LT) [dispatcherCalldataSizeExpr, .Lit (UInt256.ofNat 4)]]

/-- `slt(add(calldatasize(), not(3)), 64)`, the recover case's ABI minimum-size
    guard. -/
def dispatcherMinCalldataGuardExpr : Expr :=
  .Call (Sum.inl .SLT)
    [.Call (Sum.inl .ADD)
      [dispatcherCalldataSizeExpr,
       .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)]],
     .Lit (UInt256.ofNat 64)]

/-- `calldataload(4)`, the ABI dynamic-bytes offset word. -/
def dispatcherOffsetExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 4)]

/-- `calldataload(36)`, the ABI digest word. -/
def dispatcherDigestExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 36)]

/-- `calldataload(0x44)`, the ABI dynamic-bytes length word after offset `0x40`. -/
def dispatcherLengthWordExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0x44)]

theorem eval_dispatcher_calldatasize (raw : RawSig) (digest : Digest) :
    eval 2 dispatcherCalldataSizeExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat 2548) := by
  simpa [dispatcherCalldataSizeExpr, forsInitialState_calldata_size raw digest]
    using eval_nullop0 (n := 0) (co := some forsVerifierRuntime)
      (primCall_calldatasize (n := 0) (forsInitialState raw digest))

theorem eval_dispatcher_callvalue (raw : RawSig) (digest : Digest) :
    eval 2 dispatcherCallvalueExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat 0) := by
  simpa [dispatcherCallvalueExpr, forsInitialState_callvalue raw digest]
    using eval_nullop0 (n := 0) (co := some forsVerifierRuntime)
      (primCall_callvalue (n := 0) (forsInitialState raw digest))

theorem eval_dispatcher_calldatasize_of_size
    (s : EvmYul.Yul.State) (co : Option YulContract)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval 2 dispatcherCalldataSizeExpr co s =
      .ok (s, UInt256.ofNat 2548) := by
  simpa [dispatcherCalldataSizeExpr, hsize]
    using eval_nullop0 (n := 0) (co := co)
      (primCall_calldatasize (n := 0) s)

theorem eval_dispatcher_callvalue_of_zero
    (s : EvmYul.Yul.State) (co : Option YulContract)
    (hvalue : s.executionEnv.weiValue = UInt256.ofNat 0) :
    eval 2 dispatcherCallvalueExpr co s =
      .ok (s, UInt256.ofNat 0) := by
  simpa [dispatcherCallvalueExpr, hvalue]
    using eval_nullop0 (n := 0) (co := co)
      (primCall_callvalue (n := 0) s)

private theorem uint256_lt_2548_4 :
    UInt256.lt (UInt256.ofNat 2548) (UInt256.ofNat 4) = UInt256.ofNat 0 := by
  rfl

private theorem uint256_isZero_zero :
    (UInt256.ofNat 0).isZero = UInt256.ofNat 1 := by
  rfl

private theorem uint256_slt_min_calldata_guard :
    UInt256.slt ((UInt256.ofNat 2548).add ((UInt256.ofNat 3).lnot))
        (UInt256.ofNat 64) =
      UInt256.ofNat 0 := by
  rfl

theorem eval_dispatcher_has_selector_guard_of_size
    (s : EvmYul.Yul.State) (co : Option YulContract)
    (hsize' : s.executionEnv.calldata.size = 2548) :
    eval 8 dispatcherHasSelectorGuardExpr co s =
      .ok (s, UInt256.ofNat 1) := by
  have hsize : eval 2 dispatcherCalldataSizeExpr co s =
      .ok (s, UInt256.ofNat 2548) :=
    eval_dispatcher_calldatasize_of_size s co hsize'
  have hlt : eval 6 (.Call (Sum.inl .LT)
        [dispatcherCalldataSizeExpr, .Lit (UInt256.ofNat 4)])
        co s = .ok (s, UInt256.ofNat 0) := by
    simpa [uint256_lt_2548_4] using
      (eval_binop2 (n := 0) (co := co) (OP := .LT)
        (f := UInt256.lt)
        (primCall_lt (n := 4) (s := s) (UInt256.ofNat 2548) (UInt256.ofNat 4))
        hsize eval_lit)
  change eval 8
      (.Call (Sum.inl .ISZERO)
        [.Call (Sum.inl .LT) [dispatcherCalldataSizeExpr, .Lit (UInt256.ofNat 4)]])
      co s = .ok (s, UInt256.ofNat 1)
  simpa [uint256_isZero_zero] using
    (eval_unop1 (n := 4) (co := co) (OP := .ISZERO)
      (f := UInt256.isZero)
      (primCall_iszero (n := 6) (s := s) (UInt256.ofNat 0)) hlt)

theorem eval_dispatcher_has_selector_guard (raw : RawSig) (digest : Digest) :
    eval 8 dispatcherHasSelectorGuardExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat 1) :=
  eval_dispatcher_has_selector_guard_of_size
    (forsInitialState raw digest) (some forsVerifierRuntime)
    (forsInitialState_calldata_size raw digest)

theorem eval_dispatcher_min_calldata_guard_of_size
    (s : EvmYul.Yul.State) (co : Option YulContract)
    (hsize' : s.executionEnv.calldata.size = 2548) :
    eval 10 dispatcherMinCalldataGuardExpr co s =
      .ok (s, UInt256.ofNat 0) := by
  have hsize : eval 2 dispatcherCalldataSizeExpr co s =
      .ok (s, UInt256.ofNat 2548) :=
    eval_dispatcher_calldatasize_of_size s co hsize'
  have hnot3 : eval 4 (.Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)]) co s =
      .ok (s, (UInt256.ofNat 3).lnot) :=
    eval_unop1 (n := 0) (co := co) (OP := .NOT) (f := UInt256.lnot)
      (primCall_not (n := 2) (s := s) (UInt256.ofNat 3)) eval_lit
  have hadd : eval 6
        (.Call (Sum.inl .ADD)
          [dispatcherCalldataSizeExpr,
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)]])
        co s =
      .ok (s, (UInt256.ofNat 2548).add ((UInt256.ofNat 3).lnot)) :=
    eval_binop2 (n := 0) (co := co) (OP := .ADD) (f := UInt256.add)
      (primCall_add (n := 4) (s := s) (UInt256.ofNat 2548) ((UInt256.ofNat 3).lnot))
      hsize hnot3
  change eval 10
      (.Call (Sum.inl .SLT)
        [.Call (Sum.inl .ADD)
          [dispatcherCalldataSizeExpr,
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)]],
         .Lit (UInt256.ofNat 64)])
      co s = .ok (s, UInt256.ofNat 0)
  simpa [uint256_slt_min_calldata_guard] using
    (eval_binop2 (n := 4) (co := co) (OP := .SLT) (f := UInt256.slt)
      (primCall_slt (n := 8) (s := s)
        ((UInt256.ofNat 2548).add ((UInt256.ofNat 3).lnot)) (UInt256.ofNat 64))
      hadd eval_lit)

theorem eval_dispatcher_selector_of_calldata
    (raw : RawSig) (digest : Digest) (s : EvmYul.Yul.State)
    (co : Option YulContract)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval 6 dispatcherSelectorExpr co s =
      .ok (s, UInt256.ofNat 0x1aad75c5) := by
  let word := EvmYul.State.calldataload s.toState (UInt256.ofNat 0)
  have hload :
      eval 4 (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)])
          co s =
        .ok (s, word) := by
    dsimp [word]
    exact eval_unop1_thread (n := 0) (co := co)
      (primCall_calldataload s (UInt256.ofNat 0)) eval_lit
  have hsel :
      UInt256.shiftRight word (UInt256.ofNat 224) =
        UInt256.ofNat 0x1aad75c5 :=
    by
      dsimp [word]
      exact calldataload_encode_selector raw digest s.toState hcd
  have hprim :
      primCall 5 s .SHR [UInt256.ofNat 224, word] =
        .ok (s, [UInt256.shiftRight word (UInt256.ofNat 224)]) :=
    primCall_shr (UInt256.ofNat 224) word
  change eval 6
      (.Call (Sum.inl .SHR)
        [.Lit (UInt256.ofNat 224),
         .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)]])
      co s =
    .ok (s, UInt256.ofNat 0x1aad75c5)
  rw [eval_call_prim]
  show evalPrimCall 5 .SHR
      (reverse' (evalArgs 5
        [(.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)]),
         .Lit (UInt256.ofNat 224)] co s)) =
    .ok (s, UInt256.ofNat 0x1aad75c5)
  rw [evalArgs_cons_ok hload, evalTail_cons_ok, evalArgs_cons_ok eval_lit,
    evalTail_cons_ok, evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, evalPrimCall, hprim, hsel, head', List.head!]

theorem eval_dispatcher_selector (raw : RawSig) (digest : Digest) :
    eval 6 dispatcherSelectorExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat 0x1aad75c5) :=
  eval_dispatcher_selector_of_calldata raw digest (forsInitialState raw digest)
    (some forsVerifierRuntime) (forsInitialState_toState_calldata raw digest)

theorem eval_dispatcher_offset_of_calldata
    (raw : RawSig) (digest : Digest) (s : EvmYul.Yul.State)
    (co : Option YulContract)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval 4 dispatcherOffsetExpr co s =
      .ok (s, UInt256.ofNat 0x40) := by
  have hoff :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 4) = UInt256.ofNat 0x40 :=
    calldataload_encode_offset raw digest s.toState hcd
  change eval 4 (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 4)])
      co s = .ok (s, UInt256.ofNat 0x40)
  have h := eval_unop1_thread (n := 0) (co := co)
      (primCall_calldataload s (UInt256.ofNat 4)) eval_lit
  rw [hoff] at h
  exact h

theorem eval_dispatcher_offset (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherOffsetExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat 0x40) :=
  eval_dispatcher_offset_of_calldata raw digest (forsInitialState raw digest)
    (some forsVerifierRuntime) (forsInitialState_toState_calldata raw digest)

theorem eval_dispatcher_digest_of_calldata
    (raw : RawSig) (digest : Digest) (s : EvmYul.Yul.State)
    (co : Option YulContract)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval 4 dispatcherDigestExpr co s =
      .ok (s, UInt256.ofNat digest) := by
  have hdigest :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 36) = UInt256.ofNat digest :=
    calldataload_encode_digest raw digest s.toState hcd
  change eval 4 (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 36)])
      co s = .ok (s, UInt256.ofNat digest)
  have h := eval_unop1_thread (n := 0) (co := co)
      (primCall_calldataload s (UInt256.ofNat 36)) eval_lit
  rw [hdigest] at h
  exact h

theorem eval_dispatcher_digest (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherDigestExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat digest) :=
  eval_dispatcher_digest_of_calldata raw digest (forsInitialState raw digest)
    (some forsVerifierRuntime) (forsInitialState_toState_calldata raw digest)

theorem eval_dispatcher_length_word_of_calldata
    (raw : RawSig) (digest : Digest) (s : EvmYul.Yul.State)
    (co : Option YulContract)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval 4 dispatcherLengthWordExpr co s =
      .ok (s, UInt256.ofNat raw.len) := by
  have hlen :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 0x44) = UInt256.ofNat raw.len :=
    calldataload_encode_length raw digest s.toState hcd
  change eval 4 (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0x44)])
      co s = .ok (s, UInt256.ofNat raw.len)
  have h := eval_unop1_thread (n := 0) (co := co)
      (primCall_calldataload s (UInt256.ofNat 0x44)) eval_lit
  rw [hlen] at h
  exact h

theorem eval_dispatcher_length_word (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherLengthWordExpr (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .ok (forsInitialState raw digest, UInt256.ofNat raw.len) :=
  eval_dispatcher_length_word_of_calldata raw digest (forsInitialState raw digest)
    (some forsVerifierRuntime) (forsInitialState_toState_calldata raw digest)

theorem dispatcher_length_word_eq_sigLen_iff (raw : RawSig) (digest : Digest)
    (hbound : RawSigLenFitsEvmWord raw) :
    EvmYul.State.calldataload (forsInitialState raw digest).toState (UInt256.ofNat 0x44)
        = UInt256.ofNat SigLen ↔ raw.len = SigLen := by
  rw [calldataload_encode_length raw digest (forsInitialState raw digest).toState
    (forsInitialState_toState_calldata raw digest)]
  exact rawLen_word_eq_sigLen_iff_of_lt raw hbound

/-! ## First dispatcher statement -/

/-- First statement in the runtime dispatcher: initialize Solidity's free-memory
    pointer slot. -/
def dispatcherFreeMemPtrStmt : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Lit (UInt256.ofNat 64), .Lit (UInt256.ofNat 0x80)])

/-- Post-state after `mstore(64, 0x80)`. -/
def dispatcherAfterFreeMemPtr (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 64) (UInt256.ofNat 0x80))

theorem dispatcherAfterFreeMemPtr_toState (s : EvmYul.Yul.State) :
    (dispatcherAfterFreeMemPtr s).toState = s.toState := by
  cases s <;> rfl

theorem dispatcherAfterFreeMemPtr_executionEnv (s : EvmYul.Yul.State) :
    (dispatcherAfterFreeMemPtr s).executionEnv = s.executionEnv := by
  cases s <;> rfl

theorem exec_dispatcher_free_mem_ptr
    (s : EvmYul.Yul.State) (co : Option YulContract) :
    exec 7 dispatcherFreeMemPtrStmt co s =
      .ok (dispatcherAfterFreeMemPtr s) := by
  change exec 7
      (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Lit (UInt256.ofNat 64), .Lit (UInt256.ofNat 0x80)]))
      co s =
    .ok (dispatcherAfterFreeMemPtr s)
  rw [exec_exprstmt_prim (n := 6)]
  show execPrimCall 6 .MSTORE []
      (reverse' (evalArgs 6
        [.Lit (UInt256.ofNat 0x80), .Lit (UInt256.ofNat 64)] co s)) =
    .ok (dispatcherAfterFreeMemPtr s)
  rw [evalArgs_cons_ok (n := 5) (arg := .Lit (UInt256.ofNat 0x80))
    (args := [.Lit (UInt256.ofNat 64)]) (co := co) (s := s)
    (h := eval_lit (n := 4))]
  rw [evalTail_cons_ok (n := 4)]
  rw [evalArgs_cons_ok (n := 3) (arg := .Lit (UInt256.ofNat 64))
    (args := []) (co := co) (s := s)
    (h := eval_lit (n := 2))]
  rw [evalTail_cons_ok (n := 2), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok
    (vars := []) (prim := .MSTORE)
    (args := [UInt256.ofNat 64, UInt256.ofNat 0x80])
    (s₁ := dispatcherAfterFreeMemPtr s) (vals := [])
    (s := s)
    (h := by
      simpa [dispatcherAfterFreeMemPtr] using
        (primCall_mstore (n := 5) s (UInt256.ofNat 64) (UInt256.ofNat 0x80)))]
  cases dispatcherAfterFreeMemPtr s <;> rfl

theorem eval_dispatcher_has_selector_guard_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 8 dispatcherHasSelectorGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat 1) := by
  apply eval_dispatcher_has_selector_guard_of_size
  rw [dispatcherAfterFreeMemPtr_executionEnv]
  exact forsInitialState_calldata_size raw digest

theorem eval_dispatcher_selector_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 6 dispatcherSelectorExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest),
        UInt256.ofNat 0x1aad75c5) := by
  apply eval_dispatcher_selector_of_calldata
  rw [dispatcherAfterFreeMemPtr_toState]
  exact forsInitialState_toState_calldata raw digest

theorem eval_dispatcher_callvalue_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 2 dispatcherCallvalueExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat 0) := by
  apply eval_dispatcher_callvalue_of_zero
  rw [dispatcherAfterFreeMemPtr_executionEnv]
  exact forsInitialState_callvalue raw digest

theorem exec_dispatcher_callvalue_if_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 3 (.If dispatcherCallvalueExpr body) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) := by
  exact exec_if_false
    (n := 2) (co := some forsVerifierRuntime)
    (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (cond := dispatcherCallvalueExpr) (body := body)
    (s' := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (eval_dispatcher_callvalue_after_free_mem_ptr raw digest)

theorem eval_dispatcher_min_calldata_guard_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 10 dispatcherMinCalldataGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat 0) := by
  apply eval_dispatcher_min_calldata_guard_of_size
  rw [dispatcherAfterFreeMemPtr_executionEnv]
  exact forsInitialState_calldata_size raw digest

theorem exec_dispatcher_min_calldata_if_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 11 (.If dispatcherMinCalldataGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) := by
  exact exec_if_false
    (n := 10) (co := some forsVerifierRuntime)
    (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (cond := dispatcherMinCalldataGuardExpr) (body := body)
    (s' := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (eval_dispatcher_min_calldata_guard_after_free_mem_ptr raw digest)

theorem eval_dispatcher_offset_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherOffsetExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat 0x40) := by
  apply eval_dispatcher_offset_of_calldata
  rw [dispatcherAfterFreeMemPtr_toState]
  exact forsInitialState_toState_calldata raw digest

theorem eval_dispatcher_digest_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherDigestExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat digest) := by
  apply eval_dispatcher_digest_of_calldata
  rw [dispatcherAfterFreeMemPtr_toState]
  exact forsInitialState_toState_calldata raw digest

theorem eval_dispatcher_length_word_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    eval 4 dispatcherLengthWordExpr (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest), UInt256.ofNat raw.len) := by
  apply eval_dispatcher_length_word_of_calldata
  rw [dispatcherAfterFreeMemPtr_toState]
  exact forsInitialState_toState_calldata raw digest

private theorem uint256_one_ne_zero : UInt256.ofNat 1 ≠ UInt256.ofNat 0 := by
  decide

theorem exec_dispatcher_has_selector_if_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 9 (.If dispatcherHasSelectorGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      exec 8 (.Block body) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) := by
  exact exec_if_true
    (n := 8) (co := some forsVerifierRuntime)
    (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (cond := dispatcherHasSelectorGuardExpr) (body := body)
    (s' := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (c := UInt256.ofNat 1)
    (eval_dispatcher_has_selector_guard_after_free_mem_ptr raw digest)
    uint256_one_ne_zero

end NiceTry.Fors.Bridge
