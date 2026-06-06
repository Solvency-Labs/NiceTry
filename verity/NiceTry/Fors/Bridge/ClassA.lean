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

/-- `add(4, offset)`, the ABI location of the dynamic-bytes length word. -/
def dispatcherLengthOffsetExpr : Expr :=
  .Call (Sum.inl .ADD) [.Lit (UInt256.ofNat 4), .Var "offset"]

/-- `calldataload(add(4, offset))`, the selected recover case's length read. -/
def dispatcherLengthFromOffsetExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [dispatcherLengthOffsetExpr]

/-- `gt(length, 0xffffffffffffffff)`, the recover case's dynamic-bytes length
    upper-bound guard. -/
def dispatcherLengthBoundGuardExpr : Expr :=
  .Call (Sum.inl .GT)
    [.Var "length", .Lit (UInt256.ofNat 0xffffffffffffffff)]

/-- `add(add(offset, length), 36)`, the end offset of the dynamic bytes payload
    including ABI head bytes. -/
def dispatcherPayloadEndExpr : Expr :=
  .Call (Sum.inl .ADD)
    [.Call (Sum.inl .ADD) [.Var "offset", .Var "length"],
     .Lit (UInt256.ofNat 36)]

/-- `gt(add(add(offset, length), 36), calldatasize())`, the recover case's
    dynamic-bytes payload in-bounds guard. -/
def dispatcherPayloadBoundGuardExpr : Expr :=
  .Call (Sum.inl .GT) [dispatcherPayloadEndExpr, dispatcherCalldataSizeExpr]

/-- `add(offset, 36)`, the calldata start of the ABI bytes payload passed to
    `fun_recover`. -/
def dispatcherSigDataOffsetExpr : Expr :=
  .Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 36)]

/-- The selected recover case's user-function call expression. -/
def dispatcherRecoverCallExpr : Expr :=
  .Call (Sum.inr "fun_recover")
    [dispatcherSigDataOffsetExpr, .Var "length", dispatcherDigestExpr]

/-- `gt(offset, 0xffffffffffffffff)`, the recover case's ABI offset upper-bound
    guard. -/
def dispatcherOffsetBoundGuardExpr : Expr :=
  .Call (Sum.inl .GT)
    [.Var "offset", .Lit (UInt256.ofNat 0xffffffffffffffff)]

/-- `iszero(slt(add(offset, 35), calldatasize()))`, the recover case's dynamic
    bytes header in-bounds guard. -/
def dispatcherOffsetMinCalldataGuardExpr : Expr :=
  .Call (Sum.inl .ISZERO)
    [.Call (Sum.inl .SLT)
      [.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)],
       dispatcherCalldataSizeExpr]]

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

theorem eval_dispatcher_calldatasize_of_size_at_fuel
    (n : Nat) (s : EvmYul.Yul.State) (co : Option YulContract)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 2) dispatcherCalldataSizeExpr co s =
      .ok (s, UInt256.ofNat 2548) := by
  simpa [dispatcherCalldataSizeExpr, hsize]
    using eval_nullop0 (n := n) (co := co)
      (primCall_calldatasize (n := n) s)

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

private theorem uint256_gt_offset_bound :
    UInt256.gt (UInt256.ofNat 0x40) (UInt256.ofNat 0xffffffffffffffff) =
      UInt256.ofNat 0 := by
  rfl

private theorem uint256_gt_sigLen_bound :
    UInt256.gt (UInt256.ofNat SigLen) (UInt256.ofNat 0xffffffffffffffff) =
      UInt256.ofNat 0 := by
  rfl

private theorem uint256_add_offset_35 :
    (UInt256.ofNat 0x40).add (UInt256.ofNat 35) = UInt256.ofNat 99 := by
  rfl

private theorem uint256_add_4_offset :
    (UInt256.ofNat 4).add (UInt256.ofNat 0x40) = UInt256.ofNat 0x44 := by
  rfl

private theorem uint256_add_offset_sigLen :
    (UInt256.ofNat 0x40).add (UInt256.ofNat SigLen) =
      UInt256.ofNat 2512 := by
  rfl

private theorem uint256_add_payload_end_sigLen :
    (UInt256.ofNat 2512).add (UInt256.ofNat 36) =
      UInt256.ofNat 2548 := by
  rfl

private theorem uint256_add_offset_36 :
    (UInt256.ofNat 0x40).add (UInt256.ofNat 36) = UInt256.ofNat 100 := by
  rfl

private theorem uint256_slt_offset_min_calldata_guard :
    UInt256.slt (UInt256.ofNat 99) (UInt256.ofNat 2548) = UInt256.ofNat 1 := by
  rfl

private theorem uint256_gt_payload_bound_sigLen :
    UInt256.gt (UInt256.ofNat 2548) (UInt256.ofNat 2548) = UInt256.ofNat 0 := by
  rfl

private theorem uint256_isZero_one :
    (UInt256.ofNat 1).isZero = UInt256.ofNat 0 := by
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

/-- State after the selected recover case binds `offset := calldataload(4)`. -/
def dispatcherAfterOffset (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "offset" (UInt256.ofNat 0x40)

theorem dispatcherAfterOffset_executionEnv (s : EvmYul.Yul.State) :
    (dispatcherAfterOffset s).executionEnv = s.executionEnv := by
  cases s <;> rfl

theorem dispatcherAfterOffset_toState (s : EvmYul.Yul.State) :
    (dispatcherAfterOffset s).toState = s.toState := by
  cases s <;> rfl

/-- State after the selected recover case binds
    `length := calldataload(add(4, offset))`. -/
def dispatcherAfterLength (raw : RawSig) (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "length" (UInt256.ofNat raw.len)

theorem dispatcherAfterLength_executionEnv (raw : RawSig) (s : EvmYul.Yul.State) :
    (dispatcherAfterLength raw s).executionEnv = s.executionEnv := by
  cases s <;> rfl

theorem dispatcherAfterLength_toState (raw : RawSig) (s : EvmYul.Yul.State) :
    (dispatcherAfterLength raw s).toState = s.toState := by
  cases s <;> rfl

theorem exec_dispatcher_let_offset_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    exec 5 (.Let ["offset"] (.some dispatcherOffsetExpr)) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
  let s := dispatcherAfterFreeMemPtr (forsInitialState raw digest)
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s]
    rw [dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  have hoff :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 4) = UInt256.ofNat 0x40 :=
    calldataload_encode_offset raw digest s.toState hcd
  change exec 5 (.Let ["offset"] (.some (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 4)])))
      (some forsVerifierRuntime) s = .ok (dispatcherAfterOffset s)
  rw [exec_let_prim (n := 4)]
  show execPrimCall 4 .CALLDATALOAD ["offset"]
      (reverse' (evalArgs 4 [.Lit (UInt256.ofNat 4)] (some forsVerifierRuntime) s)) =
    .ok (dispatcherAfterOffset s)
  rw [evalArgs_cons_ok (n := 3) (arg := .Lit (UInt256.ofNat 4))
    (args := []) (co := some forsVerifierRuntime) (s := s)
    (h := eval_lit (n := 2))]
  rw [evalTail_cons_ok (n := 2), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [execPrimCall_ok
    (vars := ["offset"]) (prim := .CALLDATALOAD)
    (args := [UInt256.ofNat 4]) (s₁ := s) (vals := [UInt256.ofNat 0x40])
    (s := s)
    (h := by
      simpa [hoff] using
        (primCall_calldataload (n := 3) s (UInt256.ofNat 4)))]
  cases s <;> rfl

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

theorem dispatcherAfterOffset_lookup_offset_after_free_mem_ptr
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "offset"
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      UInt256.ofNat 0x40 := by
  rfl

theorem dispatcherAfterLength_lookup_length_after_offset
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "length"
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      UInt256.ofNat raw.len := by
  rfl

theorem dispatcherAfterLength_lookup_offset_after_offset
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "offset"
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      UInt256.ofNat 0x40 := by
  rfl

theorem eval_dispatcher_offset_bound_guard_after_offset
    (raw : RawSig) (digest : Digest) :
    eval 6 dispatcherOffsetBoundGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)),
        UInt256.ofNat 0) := by
  let s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
  have hlookup :
      EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  change eval 6
      (.Call (Sum.inl .GT)
        [.Var "offset", .Lit (UInt256.ofNat 0xffffffffffffffff)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := 0) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := 4) (s := s)
        (EvmYul.Yul.State.lookup! "offset" s)
        (UInt256.ofNat 0xffffffffffffffff))
      (eval_var (n := 1) (co := some forsVerifierRuntime) (s := s) (id := "offset"))
      (eval_lit (n := 3) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 0xffffffffffffffff))
  simpa [dispatcherOffsetBoundGuardExpr, hlookup, uint256_gt_offset_bound] using hgt

theorem exec_dispatcher_offset_bound_if_after_offset
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 7 (.If dispatcherOffsetBoundGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
  exact exec_if_false
    (n := 6) (co := some forsVerifierRuntime)
    (s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
    (cond := dispatcherOffsetBoundGuardExpr) (body := body)
    (s' := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
    (eval_dispatcher_offset_bound_guard_after_offset raw digest)

theorem eval_dispatcher_offset_min_calldata_guard_after_offset
    (raw : RawSig) (digest : Digest) :
    eval 12 dispatcherOffsetMinCalldataGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)),
        UInt256.ofNat 0) := by
  let s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
  have hlookup :
      EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  have hsize : s.executionEnv.calldata.size = 2548 := by
    dsimp [s]
    rw [dispatcherAfterOffset_executionEnv, dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_calldata_size raw digest
  have hadd : eval 6
        (.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)])
        (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 99) := by
    have hraw := eval_binop2 (n := 0) (co := some forsVerifierRuntime) (OP := .ADD)
        (f := UInt256.add)
        (primCall_add (n := 4) (s := s)
          (EvmYul.Yul.State.lookup! "offset" s) (UInt256.ofNat 35))
        (eval_var (n := 1) (co := some forsVerifierRuntime) (s := s) (id := "offset"))
        (eval_lit (n := 3) (co := some forsVerifierRuntime) (s := s)
          (val := UInt256.ofNat 35))
    simpa [hlookup, uint256_add_offset_35] using hraw
  have hcalldatasize : eval 8 dispatcherCalldataSizeExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2548) :=
    eval_dispatcher_calldatasize_of_size_at_fuel
      6 s (some forsVerifierRuntime) hsize
  have hslt : eval 10
        (.Call (Sum.inl .SLT)
          [.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)],
           dispatcherCalldataSizeExpr])
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 1) := by
    have hraw := eval_binop2 (n := 4) (co := some forsVerifierRuntime) (OP := .SLT)
        (f := UInt256.slt)
        (primCall_slt (n := 8) (s := s)
          (UInt256.ofNat 99) (UInt256.ofNat 2548))
        hadd hcalldatasize
    simpa [uint256_slt_offset_min_calldata_guard] using hraw
  change eval 12
      (.Call (Sum.inl .ISZERO)
        [.Call (Sum.inl .SLT)
          [.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)],
           dispatcherCalldataSizeExpr]])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  simpa [dispatcherOffsetMinCalldataGuardExpr, uint256_isZero_one] using
    (eval_unop1 (n := 8) (co := some forsVerifierRuntime) (OP := .ISZERO)
      (f := UInt256.isZero)
      (primCall_iszero (n := 10) (s := s) (UInt256.ofNat 1)) hslt)

theorem exec_dispatcher_offset_min_calldata_if_after_offset
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 13 (.If dispatcherOffsetMinCalldataGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
  exact exec_if_false
    (n := 12) (co := some forsVerifierRuntime)
    (s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
    (cond := dispatcherOffsetMinCalldataGuardExpr) (body := body)
    (s' := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
    (eval_dispatcher_offset_min_calldata_guard_after_offset raw digest)

theorem eval_dispatcher_length_offset_after_offset
    (raw : RawSig) (digest : Digest) :
    eval 7 dispatcherLengthOffsetExpr (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)),
        UInt256.ofNat 0x44) := by
  let s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
  have hlookup :
      EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  change eval 7
      (.Call (Sum.inl .ADD) [.Lit (UInt256.ofNat 4), .Var "offset"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0x44)
  have hraw := eval_binop2 (n := 1) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := 5) (s := s)
        (UInt256.ofNat 4) (EvmYul.Yul.State.lookup! "offset" s))
      (eval_lit (n := 2) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 4))
      (eval_var (n := 4) (co := some forsVerifierRuntime) (s := s) (id := "offset"))
  simpa [dispatcherLengthOffsetExpr, hlookup, uint256_add_4_offset] using hraw

theorem exec_dispatcher_let_length_after_offset
    (raw : RawSig) (digest : Digest) :
    exec 9 (.Let ["length"] (.some dispatcherLengthFromOffsetExpr)) (some forsVerifierRuntime)
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterLength raw
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) := by
  let s := dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s]
    rw [dispatcherAfterOffset_toState, dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 0x44) =
        UInt256.ofNat raw.len :=
    calldataload_encode_length raw digest s.toState hcd
  change exec 9
      (.Let ["length"] (.some
        (.Call (Sum.inl .CALLDATALOAD) [dispatcherLengthOffsetExpr])))
      (some forsVerifierRuntime) s = .ok (dispatcherAfterLength raw s)
  rw [exec_let_prim (n := 8)]
  show execPrimCall 8 .CALLDATALOAD ["length"]
      (reverse' (evalArgs 8 [dispatcherLengthOffsetExpr] (some forsVerifierRuntime) s)) =
    .ok (dispatcherAfterLength raw s)
  rw [evalArgs_cons_ok (n := 7) (arg := dispatcherLengthOffsetExpr)
    (args := []) (co := some forsVerifierRuntime) (s := s)
    (h := eval_dispatcher_length_offset_after_offset raw digest)]
  rw [evalTail_cons_ok (n := 6), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [execPrimCall_ok
    (vars := ["length"]) (prim := .CALLDATALOAD)
    (args := [UInt256.ofNat 0x44]) (s₁ := s) (vals := [UInt256.ofNat raw.len])
    (s := s)
    (h := by
      simpa [hload] using
        (primCall_calldataload (n := 7) s (UInt256.ofNat 0x44)))]
  cases s <;> rfl

theorem eval_dispatcher_length_bound_guard_after_length
    (raw : RawSig) (digest : Digest)
    (hbound :
      UInt256.gt (UInt256.ofNat raw.len) (UInt256.ofNat 0xffffffffffffffff) =
        UInt256.ofNat 0) :
    eval 6 dispatcherLengthBoundGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        UInt256.ofNat 0) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  have hlookup :
      EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat raw.len := by
    dsimp [s]
    exact dispatcherAfterLength_lookup_length_after_offset raw digest
  change eval 6
      (.Call (Sum.inl .GT)
        [.Var "length", .Lit (UInt256.ofNat 0xffffffffffffffff)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := 0) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := 4) (s := s)
        (EvmYul.Yul.State.lookup! "length" s)
        (UInt256.ofNat 0xffffffffffffffff))
      (eval_var (n := 1) (co := some forsVerifierRuntime) (s := s) (id := "length"))
      (eval_lit (n := 3) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 0xffffffffffffffff))
  simpa [dispatcherLengthBoundGuardExpr, hlookup, hbound] using hgt

theorem exec_dispatcher_length_bound_if_after_length
    (raw : RawSig) (digest : Digest) (body : List Stmt)
    (hbound :
      UInt256.gt (UInt256.ofNat raw.len) (UInt256.ofNat 0xffffffffffffffff) =
        UInt256.ofNat 0) :
    exec 7 (.If dispatcherLengthBoundGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) := by
  exact exec_if_false
    (n := 6) (co := some forsVerifierRuntime)
    (s := dispatcherAfterLength raw
      (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))))
    (cond := dispatcherLengthBoundGuardExpr) (body := body)
    (s' := dispatcherAfterLength raw
      (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))))
    (eval_dispatcher_length_bound_guard_after_length raw digest hbound)

theorem exec_dispatcher_length_bound_if_after_length_of_sigLen
    (raw : RawSig) (digest : Digest) (body : List Stmt)
    (hlen : raw.len = SigLen) :
    exec 7 (.If dispatcherLengthBoundGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) := by
  apply exec_dispatcher_length_bound_if_after_length
  rw [hlen]
  exact uint256_gt_sigLen_bound

theorem eval_dispatcher_payload_bound_guard_after_length_of_sigLen
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen) :
    eval 14 dispatcherPayloadBoundGuardExpr (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        UInt256.ofNat 0) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  have hoffset :
      EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterLength_lookup_offset_after_offset raw digest
  have hlength :
      EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat SigLen := by
    dsimp [s]
    rw [dispatcherAfterLength_lookup_length_after_offset raw digest, hlen]
  have hsize : s.executionEnv.calldata.size = 2548 := by
    dsimp [s]
    rw [dispatcherAfterLength_executionEnv, dispatcherAfterOffset_executionEnv,
      dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_calldata_size raw digest
  have hinner : eval 6
        (.Call (Sum.inl .ADD) [.Var "offset", .Var "length"])
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2512) := by
    have hraw := eval_binop2 (n := 0) (co := some forsVerifierRuntime) (OP := .ADD)
        (f := UInt256.add)
        (primCall_add (n := 4) (s := s)
          (EvmYul.Yul.State.lookup! "offset" s)
          (EvmYul.Yul.State.lookup! "length" s))
        (eval_var (n := 1) (co := some forsVerifierRuntime) (s := s) (id := "offset"))
        (eval_var (n := 3) (co := some forsVerifierRuntime) (s := s) (id := "length"))
    simpa [hoffset, hlength, uint256_add_offset_sigLen] using hraw
  have hend : eval 10 dispatcherPayloadEndExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2548) := by
    have hraw := eval_binop2 (n := 4) (co := some forsVerifierRuntime) (OP := .ADD)
        (f := UInt256.add)
        (primCall_add (n := 8) (s := s)
          (UInt256.ofNat 2512) (UInt256.ofNat 36))
        hinner
        (eval_lit (n := 7) (co := some forsVerifierRuntime) (s := s)
          (val := UInt256.ofNat 36))
    simpa [dispatcherPayloadEndExpr, uint256_add_payload_end_sigLen] using hraw
  have hcalldatasize : eval 12 dispatcherCalldataSizeExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2548) :=
    eval_dispatcher_calldatasize_of_size_at_fuel
      10 s (some forsVerifierRuntime) hsize
  change eval 14
      (.Call (Sum.inl .GT) [dispatcherPayloadEndExpr, dispatcherCalldataSizeExpr])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := 8) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := 12) (s := s)
        (UInt256.ofNat 2548) (UInt256.ofNat 2548))
      hend hcalldatasize
  simpa [dispatcherPayloadBoundGuardExpr, uint256_gt_payload_bound_sigLen] using hgt

theorem exec_dispatcher_payload_bound_if_after_length_of_sigLen
    (raw : RawSig) (digest : Digest) (body : List Stmt)
    (hlen : raw.len = SigLen) :
    exec 15 (.If dispatcherPayloadBoundGuardExpr body) (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
        (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) := by
  exact exec_if_false
    (n := 14) (co := some forsVerifierRuntime)
    (s := dispatcherAfterLength raw
      (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))))
    (cond := dispatcherPayloadBoundGuardExpr) (body := body)
    (s' := dispatcherAfterLength raw
      (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))))
    (eval_dispatcher_payload_bound_guard_after_length_of_sigLen raw digest hlen)

theorem eval_dispatcher_sig_data_offset_after_length
    (raw : RawSig) (digest : Digest) :
    eval 7 dispatcherSigDataOffsetExpr (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        UInt256.ofNat 100) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  have hoffset :
      EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterLength_lookup_offset_after_offset raw digest
  change eval 7
      (.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 36)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 100)
  have hraw := eval_binop2 (n := 1) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := 5) (s := s)
        (EvmYul.Yul.State.lookup! "offset" s) (UInt256.ofNat 36))
      (eval_var (n := 2) (co := some forsVerifierRuntime) (s := s) (id := "offset"))
      (eval_lit (n := 4) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 36))
  simpa [dispatcherSigDataOffsetExpr, hoffset, uint256_add_offset_36] using hraw

theorem eval_dispatcher_length_var_after_length_of_sigLen
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen) :
    eval 9 (.Var "length") (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        UInt256.ofNat SigLen) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  have hlookup :
      EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat SigLen := by
    dsimp [s]
    rw [dispatcherAfterLength_lookup_length_after_offset raw digest, hlen]
  change eval 9 (.Var "length") (some forsVerifierRuntime) s =
    .ok (s, UInt256.ofNat SigLen)
  rw [eval_var]
  change Except.ok (s, EvmYul.Yul.State.lookup! "length" s) =
    Except.ok (s, UInt256.ofNat SigLen)
  rw [hlookup]

theorem eval_dispatcher_digest_after_length
    (raw : RawSig) (digest : Digest) :
    eval 11 dispatcherDigestExpr (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        UInt256.ofNat digest) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s]
    rw [dispatcherAfterLength_toState, dispatcherAfterOffset_toState,
      dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  have hdigest :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 36) = UInt256.ofNat digest :=
    calldataload_encode_digest raw digest s.toState hcd
  change eval 11 (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 36)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat digest)
  have h := eval_unop1_thread (n := 7) (co := some forsVerifierRuntime)
      (primCall_calldataload (n := 9) s (UInt256.ofNat 36))
      (eval_lit (n := 8) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 36))
  rw [hdigest] at h
  exact h

theorem evalArgs_dispatcher_recover_call_after_length_of_sigLen
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen) :
    reverse' (evalArgs 12
        [dispatcherDigestExpr, .Var "length", dispatcherSigDataOffsetExpr]
        (some forsVerifierRuntime)
        (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))))) =
      .ok (dispatcherAfterLength raw
          (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest))),
        [UInt256.ofNat 100, UInt256.ofNat SigLen, UInt256.ofNat digest]) := by
  let s := dispatcherAfterLength raw
    (dispatcherAfterOffset (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))
  change reverse'
      (evalArgs 12 [dispatcherDigestExpr, .Var "length", dispatcherSigDataOffsetExpr]
        (some forsVerifierRuntime) s) =
    .ok (s, [UInt256.ofNat 100, UInt256.ofNat SigLen, UInt256.ofNat digest])
  rw [evalArgs_cons_ok (n := 11) (arg := dispatcherDigestExpr)
    (args := [.Var "length", dispatcherSigDataOffsetExpr])
    (co := some forsVerifierRuntime) (s := s)
    (h := eval_dispatcher_digest_after_length raw digest)]
  rw [evalTail_cons_ok (n := 10)]
  rw [evalArgs_cons_ok (n := 9) (arg := .Var "length")
    (args := [dispatcherSigDataOffsetExpr])
    (co := some forsVerifierRuntime) (s := s)
    (h := eval_dispatcher_length_var_after_length_of_sigLen raw digest hlen)]
  rw [evalTail_cons_ok (n := 8)]
  rw [evalArgs_cons_ok (n := 7) (arg := dispatcherSigDataOffsetExpr)
    (args := []) (co := some forsVerifierRuntime) (s := s)
    (h := eval_dispatcher_sig_data_offset_after_length raw digest)]
  rw [evalTail_cons_ok (n := 6), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rfl

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
