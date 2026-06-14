import NiceTry.Fors.Bridge.Phase4Reject

/-!
# Full dispatcher routing

This module executes the deployed selector/ABI dispatcher and proves that its
observable result agrees with the scoped `fun_recover` runner.  The scoped fuel
is aligned with the exact fuel received by the recover call in
`runForsCalldata ... 100000`, so no fuel-monotonicity assumption is needed.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 8000000

/-- At a good signature length the concrete recovery body always reaches one of
    its two `RETURN`s.  This statement is deliberately independent of model-side
    well-formedness: it only follows the concrete guard, loop, and post-loop
    control flow. -/
theorem exec_recover_good_length_halts
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hlen : raw.len = SigLen) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 154) (.Block forsFunRecover.body) (some forsVerifierRuntime)
          (recoverEntryState raw digest)
        = .error (.YulHalt S ⟨1⟩) := by
  let guard :=
    (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
      (UInt256.ofNat 31)
  by_cases hguard : guard = (⟨0⟩ : UInt256)
  · obtain ⟨ss, vs, hs⟩ := recoverAfterHmsg_ok raw digest
    have hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 0x20 := by
      rw [← hs]
      exact recoverAfterHmsg_lookup_ret raw digest
    have hret2 : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96 := by
      rw [← hs]
      exact recoverAfterHmsg_lookup_ret2 raw digest
    have hoff : EvmYul.Yul.State.lookup! "var_sig_offset" (.Ok ss vs) =
        UInt256.ofNat 100 := by
      rw [← hs]
      exact recoverAfterHmsg_lookup_sig_offset raw digest
    have hdv : EvmYul.Yul.State.lookup! "usr_dVal" (.Ok ss vs) =
        recoverHmsgDVal raw digest := by
      rw [← hs]
      exact recoverAfterHmsg_lookup_dVal raw digest
    have hpk : EvmYul.Yul.State.lookup! "usr_pkSeed" (.Ok ss vs) =
        recoverHmsgPkWord raw digest := by
      rw [← hs]
      exact recoverAfterHmsg_lookup_pkSeed raw digest
    have hmem : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size = 0xa0 := by
      rw [← hs]
      exact recoverAfterHmsg_memory_size raw digest
    obtain ⟨htail, hinv⟩ := exec_recover_tail_to_loopInv ss vs
      (some forsVerifierRuntime) (recoverHmsgPkWord raw digest)
      (recoverHmsgDVal raw digest) (n + 99)
      hret hret2 hoff hdv hpk hmem (by simpa [guard] using hguard)
    have hpre :
        exec (n + 136) (.Block (forsFunRecover.body.drop 18))
            (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest) =
          exec (n + 122) (.Block (forsFunRecover.body.drop 32))
            (some forsVerifierRuntime)
            (loopEntryState ss vs (recoverHmsgPkWord raw digest)
              (recoverHmsgDVal raw digest)) := by
      rw [show n + 136 = (n + 99) + 37 by omega,
        exec_recover_hmsg_named raw digest (some forsVerifierRuntime) (n + 99), hs]
      exact htail
    rw [loopEntryState_ok] at hinv
    obtain ⟨ssf, vsf, rootsW, hloop, hinvf, hlow, hroots⟩ :=
      tree_loop_run_from_zero
        (loopEntryState ss vs (recoverHmsgPkWord raw digest)
          (recoverHmsgDVal raw digest)).toState
        (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest).toNat 132
        (some forsVerifierRuntime) _ _ hinv n
    have hsize : 0x400 ≤
        (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.size := by
      rcases hinvf.size400 with hzero | hsize
      · omega
      · exact hsize
    have hpk0 :
        (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract 0 32 =
          (recoverHmsgPkWord raw digest).toByteArray.data := by
      rw [hlow 0 32 (by omega)]
      change ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore
        (UInt256.ofNat 0x380) (recoverHmsgPkWord raw digest)).memory.data.extract 0 32 =
          (recoverHmsgPkWord raw digest).toByteArray.data
      have hpad : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size ≤
          (UInt256.ofNat 0x380).toNat := by
        rw [hmem]
        decide
      rw [mstore_pad_extract_below _ _ _ _ _ hpad (by omega)]
      rw [← hs]
      exact recoverAfterHmsg_pk_extract raw digest
    obtain ⟨S, hpost, _, _⟩ :=
      post_loop_trace (n + 103) (some forsVerifierRuntime) ssf vsf
        (recoverHmsgPkWord raw digest) rootsW hinvf.ret hpk0
        (fun j hj => (hroots j hj).1) hsize
    refine ⟨S, ?_⟩
    rw [show n + 154 = (n + 107) + 47 by omega,
      exec_recover_good_prefix_to_hmsg raw digest (n + 107) hlen]
    rw [show n + 107 + 29 = (n + 99) + 37 by omega]
    rw [hpre]
    rw [show n + 99 + 23 = n + 121 + 1 by omega]
    rw [show forsFunRecover.body.drop 32 =
        (.For forsTreeCond forsTreePost forsTreeBody) ::
          forsFunRecover.body.drop 33 from rfl]
    rw [loopEntryState_ok]
    rw [exec_block_cons_ok (n := n + 121) (co := some forsVerifierRuntime)
      hloop]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpost
  · obtain ⟨S, hsuffix, _⟩ :=
      exec_recover_forced_zero_reject_from_hmsg raw digest (n + 99)
        (by simpa [guard] using hguard)
    refine ⟨S, ?_⟩
    rw [show n + 154 = (n + 107) + 47 by omega,
      exec_recover_good_prefix_to_hmsg raw digest (n + 107) hlen]
    rw [show n + 107 + 29 = (n + 99) + 37 by omega,
      exec_recover_hmsg_named raw digest (some forsVerifierRuntime) (n + 99)]
    exact hsuffix

/-- The aligned scoped call always propagates a Yul halt at a good length. -/
theorem call_recover_good_length_halts
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen) :
    ∃ S : EvmYul.Yul.State,
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest)
        = .error (.YulHalt S ⟨1⟩) := by
  obtain ⟨S, hbody⟩ :=
    exec_recover_good_length_halts raw digest 99828 hlen
  refine ⟨S, ?_⟩
  unfold recoverFuel
  apply call_err
    (dispatcherBeforeRecoverState_account_find raw digest)
    (by simpa using forsVerifierRuntime_lookup_fun_recover)
  simpa [recoverEntryState, recoverGoodArgs, forsRecoverArgs] using hbody

/-! ## Fuel-parametric dispatcher expressions -/

private theorem eval_dispatcher_calldatasize_at
    (_raw : RawSig) (_digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 2) dispatcherCalldataSizeExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2548) :=
  eval_dispatcher_calldatasize_of_size_at_fuel n s (some forsVerifierRuntime) hsize

private theorem eval_dispatcher_callvalue_at
    (n : Nat) (s : EvmYul.Yul.State)
    (hvalue : s.executionEnv.weiValue = UInt256.ofNat 0) :
    eval (n + 2) dispatcherCallvalueExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  simpa [dispatcherCallvalueExpr, hvalue] using
    eval_nullop0 (n := n) (co := some forsVerifierRuntime)
      (primCall_callvalue (n := n) s)

private theorem eval_dispatcher_has_selector_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 8) dispatcherHasSelectorGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 1) := by
  have hcds := eval_dispatcher_calldatasize_at raw digest n s hsize
  have hlt : eval (n + 6)
      (.Call (Sum.inl .LT)
        [dispatcherCalldataSizeExpr, .Lit (UInt256.ofNat 4)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0) := by
    have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .LT)
      (f := UInt256.lt)
      (primCall_lt (n := n + 4) (s := s) (UInt256.ofNat 2548)
        (UInt256.ofNat 4))
      hcds (eval_lit (n := n + 3))
    simpa using h
  have h := eval_unop1 (n := n + 4) (co := some forsVerifierRuntime)
    (OP := .ISZERO) (f := UInt256.isZero)
    (primCall_iszero (n := n + 6) (s := s) (UInt256.ofNat 0)) hlt
  simpa [dispatcherHasSelectorGuardExpr] using h

private theorem eval_dispatcher_selector_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval (n + 6) dispatcherSelectorExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0x1aad75c5) := by
  let word := EvmYul.State.calldataload s.toState (UInt256.ofNat 0)
  have hload : eval (n + 4)
      (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)])
      (some forsVerifierRuntime) s = .ok (s, word) := by
    dsimp [word]
    exact eval_unop1_thread (n := n) (co := some forsVerifierRuntime)
      (primCall_calldataload (n := n + 2) s (UInt256.ofNat 0))
      (eval_lit (n := n + 1))
  have hsel : UInt256.shiftRight word (UInt256.ofNat 224) =
      UInt256.ofNat 0x1aad75c5 := by
    dsimp [word]
    exact calldataload_encode_selector raw digest s.toState hcd
  have hprim : primCall ((n + 4) + 1) s .SHR [UInt256.ofNat 224, word] =
      .ok (s, [UInt256.shiftRight word (UInt256.ofNat 224)]) :=
    primCall_shr (n := n + 4) (s := s) (UInt256.ofNat 224) word
  change eval (n + 6)
      (.Call (Sum.inl .SHR)
        [.Lit (UInt256.ofNat 224),
         .Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)]])
      (some forsVerifierRuntime) s =
    .ok (s, UInt256.ofNat 0x1aad75c5)
  rw [eval_call_prim]
  show evalPrimCall (n + 5) .SHR
      (reverse' (evalArgs (n + 5)
        [(.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 0)]),
         .Lit (UInt256.ofNat 224)] (some forsVerifierRuntime) s)) =
    .ok (s, UInt256.ofNat 0x1aad75c5)
  rw [evalArgs_cons_ok hload, evalTail_cons_ok,
    evalArgs_cons_ok (eval_lit (n := n + 1)), evalTail_cons_ok,
    evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, evalPrimCall, hprim, hsel, head', List.head!]

private theorem eval_dispatcher_min_calldata_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 10) dispatcherMinCalldataGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  have hcds := eval_dispatcher_calldatasize_at raw digest n s hsize
  have hnot : eval (n + 4)
      (.Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)])
      (some forsVerifierRuntime) s =
      .ok (s, (UInt256.ofNat 3).lnot) :=
    eval_unop1 (n := n) (co := some forsVerifierRuntime) (OP := .NOT)
      (f := UInt256.lnot)
      (primCall_not (n := n + 2) (s := s) (UInt256.ofNat 3))
      (eval_lit (n := n + 1))
  have hadd : eval (n + 6)
      (.Call (Sum.inl .ADD)
        [dispatcherCalldataSizeExpr,
         .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 3)]])
      (some forsVerifierRuntime) s =
      .ok (s, (UInt256.ofNat 2548).add ((UInt256.ofNat 3).lnot)) :=
    eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := n + 4) (s := s) (UInt256.ofNat 2548)
        ((UInt256.ofNat 3).lnot))
      hcds hnot
  have h := eval_binop2 (n := n + 4) (co := some forsVerifierRuntime)
    (OP := .SLT) (f := UInt256.slt)
    (primCall_slt (n := n + 8) (s := s)
      ((UInt256.ofNat 2548).add ((UInt256.ofNat 3).lnot))
      (UInt256.ofNat 64))
    hadd (eval_lit (n := n + 7))
  simpa [dispatcherMinCalldataGuardExpr] using h

private theorem eval_dispatcher_offset_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval (n + 4) dispatcherOffsetExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0x40) := by
  have h := eval_unop1_thread (n := n) (co := some forsVerifierRuntime)
    (primCall_calldataload (n := n + 2) s (UInt256.ofNat 4))
    (eval_lit (n := n + 1))
  rw [calldataload_encode_offset raw digest s.toState hcd] at h
  exact h

private theorem eval_var_lookup_at
    (n : Nat) (s : EvmYul.Yul.State) (id : Identifier) :
    (∃ ss vs, s = .Ok ss vs) →
      eval (n + 1) (.Var id) (some forsVerifierRuntime) s =
        .ok (s, EvmYul.Yul.State.lookup! id s) := by
  rintro ⟨ss, vs, rfl⟩
  rw [eval_var]
  congr 2
  exact state_getElem!_eq_lookup! ss vs id

private theorem eval_dispatcher_offset_bound_at
    (n : Nat) (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40) :
    eval (n + 6) dispatcherOffsetBoundGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .GT)
    (f := UInt256.gt)
    (primCall_gt (n := n + 4) (s := s)
      (EvmYul.Yul.State.lookup! "offset" s)
      (UInt256.ofNat 0xffffffffffffffff))
    (eval_var_lookup_at (n + 1) s "offset" hok)
    (eval_lit (n := n + 3) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 0xffffffffffffffff))
  simpa [dispatcherOffsetBoundGuardExpr, hoffset] using h

private theorem eval_dispatcher_offset_min_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 12) dispatcherOffsetMinCalldataGuardExpr
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  have hadd : eval (n + 6)
      (.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 99) := by
    have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := n + 4) (s := s)
        (EvmYul.Yul.State.lookup! "offset" s) (UInt256.ofNat 35))
      (eval_var_lookup_at (n + 1) s "offset" hok)
      (eval_lit (n := n + 3) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 35))
    simpa [hoffset] using h
  have hcds := eval_dispatcher_calldatasize_at raw digest (n + 6) s hsize
  have hslt : eval (n + 10)
      (.Call (Sum.inl .SLT)
        [.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 35)],
         dispatcherCalldataSizeExpr])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 1) := by
    have h := eval_binop2 (n := n + 4) (co := some forsVerifierRuntime)
      (OP := .SLT) (f := UInt256.slt)
      (primCall_slt (n := n + 8) (s := s)
        (UInt256.ofNat 99) (UInt256.ofNat 2548))
      hadd hcds
    simpa using h
  have h := eval_unop1 (n := n + 8) (co := some forsVerifierRuntime)
    (OP := .ISZERO) (f := UInt256.isZero)
    (primCall_iszero (n := n + 10) (s := s) (UInt256.ofNat 1)) hslt
  simpa [dispatcherOffsetMinCalldataGuardExpr] using h

private theorem eval_dispatcher_length_offset_at
    (n : Nat) (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40) :
    eval (n + 6)
      (.Call (Sum.inl .ADD) [.Lit (UInt256.ofNat 4), .Var "offset"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0x44) := by
  have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
    (f := UInt256.add)
    (primCall_add (n := n + 4) (s := s) (UInt256.ofNat 4)
      (EvmYul.Yul.State.lookup! "offset" s))
    (eval_lit (n := n + 1) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 4))
    (eval_var_lookup_at (n + 3) s "offset" hok)
  simpa [hoffset] using h

private theorem eval_dispatcher_length_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval (n + 8) dispatcherLengthFromOffsetExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat raw.len) := by
  have hoff := eval_dispatcher_length_offset_at n s hok hoffset
  have h := eval_unop1_thread (n := n + 4) (co := some forsVerifierRuntime)
    (primCall_calldataload (n := n + 6) s (UInt256.ofNat 0x44)) hoff
  rw [calldataload_encode_length raw digest s.toState hcd] at h
  simpa [dispatcherLengthFromOffsetExpr, dispatcherLengthOffsetExpr] using h

private theorem eval_dispatcher_length_bound_at
    (raw : RawSig) (n : Nat) (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hlength : EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat raw.len)
    (hlen : raw.len = SigLen) :
    eval (n + 6) dispatcherLengthBoundGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .GT)
    (f := UInt256.gt)
    (primCall_gt (n := n + 4) (s := s)
      (EvmYul.Yul.State.lookup! "length" s)
      (UInt256.ofNat 0xffffffffffffffff))
    (eval_var_lookup_at (n + 1) s "length" hok)
    (eval_lit (n := n + 3) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 0xffffffffffffffff))
  simpa [dispatcherLengthBoundGuardExpr, hlength, hlen] using h

private theorem eval_dispatcher_length_bound_word_at
    (raw : RawSig) (n : Nat) (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hlength : EvmYul.Yul.State.lookup! "length" s =
      UInt256.ofNat raw.len) :
    eval (n + 6) dispatcherLengthBoundGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.gt (UInt256.ofNat raw.len)
        (UInt256.ofNat 0xffffffffffffffff)) := by
  have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .GT)
    (f := UInt256.gt)
    (primCall_gt (n := n + 4) (s := s)
      (EvmYul.Yul.State.lookup! "length" s)
      (UInt256.ofNat 0xffffffffffffffff))
    (eval_var_lookup_at (n + 1) s "length" hok)
    (eval_lit (n := n + 3) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 0xffffffffffffffff))
  simpa [dispatcherLengthBoundGuardExpr, hlength] using h

private theorem eval_dispatcher_payload_bound_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40)
    (hlength : EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat raw.len)
    (hsize : s.executionEnv.calldata.size = 2548)
    (hlen : raw.len = SigLen) :
    eval (n + 14) dispatcherPayloadBoundGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0) := by
  have hinner : eval (n + 6)
      (.Call (Sum.inl .ADD) [.Var "offset", .Var "length"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 2512) := by
    have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := n + 4) (s := s)
        (EvmYul.Yul.State.lookup! "offset" s)
        (EvmYul.Yul.State.lookup! "length" s))
      (eval_var_lookup_at (n + 1) s "offset" hok)
      (eval_var_lookup_at (n + 3) s "length" hok)
    simpa [hoffset, hlength, hlen] using h
  have hend : eval (n + 10) dispatcherPayloadEndExpr
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 2548) := by
    have h := eval_binop2 (n := n + 4) (co := some forsVerifierRuntime)
      (OP := .ADD) (f := UInt256.add)
      (primCall_add (n := n + 8) (s := s)
        (UInt256.ofNat 2512) (UInt256.ofNat 36))
      hinner (eval_lit (n := n + 7))
    simpa [dispatcherPayloadEndExpr] using h
  have hcds := eval_dispatcher_calldatasize_at raw digest (n + 10) s hsize
  have h := eval_binop2 (n := n + 8) (co := some forsVerifierRuntime)
    (OP := .GT) (f := UInt256.gt)
    (primCall_gt (n := n + 12) (s := s)
      (UInt256.ofNat 2548) (UInt256.ofNat 2548))
    hend hcds
  simpa [dispatcherPayloadBoundGuardExpr] using h

private theorem eval_dispatcher_payload_bound_word_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40)
    (hlength : EvmYul.Yul.State.lookup! "length" s = UInt256.ofNat raw.len)
    (hsize : s.executionEnv.calldata.size = 2548) :
    eval (n + 14) dispatcherPayloadBoundGuardExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.gt
        ((UInt256.ofNat 0x40).add (UInt256.ofNat raw.len) |>.add
          (UInt256.ofNat 36))
        (UInt256.ofNat 2548)) := by
  have hinner : eval (n + 6)
      (.Call (Sum.inl .ADD) [.Var "offset", .Var "length"])
      (some forsVerifierRuntime) s =
      .ok (s, (UInt256.ofNat 0x40).add (UInt256.ofNat raw.len)) := by
    have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := n + 4) (s := s)
        (EvmYul.Yul.State.lookup! "offset" s)
        (EvmYul.Yul.State.lookup! "length" s))
      (eval_var_lookup_at (n + 1) s "offset" hok)
      (eval_var_lookup_at (n + 3) s "length" hok)
    simpa [hoffset, hlength] using h
  have hend : eval (n + 10) dispatcherPayloadEndExpr
      (some forsVerifierRuntime) s =
      .ok (s, ((UInt256.ofNat 0x40).add (UInt256.ofNat raw.len)).add
        (UInt256.ofNat 36)) := by
    exact eval_binop2 (n := n + 4) (co := some forsVerifierRuntime)
      (OP := .ADD) (f := UInt256.add)
      (primCall_add (n := n + 8) (s := s)
        ((UInt256.ofNat 0x40).add (UInt256.ofNat raw.len))
        (UInt256.ofNat 36))
      hinner (eval_lit (n := n + 7))
  have hcds := eval_dispatcher_calldatasize_at raw digest (n + 10) s hsize
  have h := eval_binop2 (n := n + 8) (co := some forsVerifierRuntime)
    (OP := .GT) (f := UInt256.gt)
    (primCall_gt (n := n + 12) (s := s)
      (((UInt256.ofNat 0x40).add (UInt256.ofNat raw.len)).add
        (UInt256.ofNat 36))
      (UInt256.ofNat 2548))
    hend hcds
  simpa [dispatcherPayloadBoundGuardExpr] using h

private theorem eval_dispatcher_sig_offset_at
    (n : Nat) (s : EvmYul.Yul.State)
    (hok : ∃ ss vs, s = .Ok ss vs)
    (hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40) :
    eval (n + 6)
      (.Call (Sum.inl .ADD) [.Var "offset", .Lit (UInt256.ofNat 36)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 100) := by
  have h := eval_binop2 (n := n) (co := some forsVerifierRuntime) (OP := .ADD)
    (f := UInt256.add)
    (primCall_add (n := n + 4) (s := s)
      (EvmYul.Yul.State.lookup! "offset" s) (UInt256.ofNat 36))
    (eval_var_lookup_at (n + 1) s "offset" hok)
    (eval_lit (n := n + 3) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 36))
  simpa [hoffset] using h

private theorem eval_dispatcher_digest_at
    (raw : RawSig) (digest : Digest) (n : Nat)
    (s : EvmYul.Yul.State)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest) :
    eval (n + 4) dispatcherDigestExpr (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat digest) := by
  have h := eval_unop1_thread (n := n) (co := some forsVerifierRuntime)
    (primCall_calldataload (n := n + 2) s (UInt256.ofNat 36))
    (eval_lit (n := n + 1))
  rw [calldataload_encode_digest raw digest s.toState hcd] at h
  exact h

/-! ## The selected recover case -/

private def dispatcherCases : List (EvmYul.Literal × List Stmt) :=
  match forsDispatcher with
  | .Block (_ :: .If _ [.Switch _ cases _] :: _) => cases
  | _ => []

private def dispatcherRecoverBody : List Stmt :=
  match dispatcherCases with
  | (_, body) :: _ => body
  | _ => []

private def dispatcherOtherCases : List (EvmYul.Literal × List Stmt) :=
  dispatcherCases.drop 1

private theorem dispatcherCases_shape :
    dispatcherCases =
      (UInt256.ofNat 0x1aad75c5, dispatcherRecoverBody) ::
        dispatcherOtherCases := by
  simp [dispatcherCases, dispatcherRecoverBody, dispatcherOtherCases,
    forsDispatcher]

private theorem dispatcherOtherCases_length :
    dispatcherOtherCases.length = 4 := by
  simp [dispatcherOtherCases, dispatcherCases, forsDispatcher]

private theorem dispatcherRecoverBody_shape :
    dispatcherRecoverBody =
      [.If dispatcherCallvalueExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .If dispatcherMinCalldataGuardExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .Let ["offset"] (.some dispatcherOffsetExpr),
       .If dispatcherOffsetBoundGuardExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .If dispatcherOffsetMinCalldataGuardExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .Let ["length"] (.some dispatcherLengthFromOffsetExpr),
       .If dispatcherLengthBoundGuardExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .If dispatcherPayloadBoundGuardExpr
          [.ExprStmtCall (.Call (Sum.inl .REVERT)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])],
       .Let ["ret"] (.some dispatcherRecoverCallExpr),
       .Let ["memPos"] (.some
          (.Call (Sum.inl .MLOAD) [.Lit (UInt256.ofNat 64)])),
       .ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Var "memPos",
           .Call (Sum.inl .AND)
             [.Var "ret",
              .Call (Sum.inl .SUB)
                [.Call (Sum.inl .SHL)
                  [.Lit (UInt256.ofNat 160), .Lit (UInt256.ofNat 1)],
                 .Lit (UInt256.ofNat 1)]]]),
       .ExprStmtCall (.Call (Sum.inl .RETURN)
          [.Var "memPos", .Lit (UInt256.ofNat 32)])] := by
  simp [dispatcherRecoverBody, dispatcherCases, forsDispatcher,
    dispatcherCallvalueExpr, dispatcherMinCalldataGuardExpr,
    dispatcherOffsetExpr, dispatcherOffsetBoundGuardExpr,
    dispatcherOffsetMinCalldataGuardExpr, dispatcherLengthFromOffsetExpr,
    dispatcherLengthOffsetExpr, dispatcherLengthBoundGuardExpr,
    dispatcherPayloadBoundGuardExpr, dispatcherPayloadEndExpr,
    dispatcherCalldataSizeExpr, dispatcherRecoverCallExpr,
    dispatcherSigDataOffsetExpr, dispatcherDigestExpr]

private theorem exec_dispatcher_let_offset_at
    (raw : RawSig) (digest : Digest) (n : Nat) :
    exec (n + 5) (.Let ["offset"] (.some dispatcherOffsetExpr))
        (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .ok (dispatcherAfterOffset
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
  let s := dispatcherAfterFreeMemPtr (forsInitialState raw digest)
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s]
    rw [dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 4) =
        UInt256.ofNat 0x40 :=
    calldataload_encode_offset raw digest s.toState hcd
  change exec (n + 5)
      (.Let ["offset"] (.some
        (.Call (Sum.inl .CALLDATALOAD) [.Lit (UInt256.ofNat 4)])))
      (some forsVerifierRuntime) s =
    .ok (dispatcherAfterOffset s)
  rw [show n + 5 = (n + 4) + 1 by omega,
    exec_let_prim (n := n + 4)]
  change execPrimCall (n + 4) .CALLDATALOAD ["offset"]
      (reverse' (evalArgs (n + 4) [.Lit (UInt256.ofNat 4)]
        (some forsVerifierRuntime) s)) =
    .ok (dispatcherAfterOffset s)
  rw [evalArgs_cons_ok (n := n + 3)
    (h := eval_lit (n := n + 2) (co := some forsVerifierRuntime) (s := s)
      (val := UInt256.ofNat 4))]
  rw [evalTail_cons_ok (n := n + 2), evalArgs_nil (n := n + 1)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [execPrimCall_ok
    (h := by
      simpa [hload] using
        (primCall_calldataload (n := n + 3) s (UInt256.ofNat 4)))]
  cases s <;> rfl

private theorem exec_dispatcher_let_length_at
    (raw : RawSig) (digest : Digest) (n : Nat) :
    exec (n + 9) (.Let ["length"] (.some dispatcherLengthFromOffsetExpr))
        (some forsVerifierRuntime)
        (dispatcherAfterOffset
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) =
      .ok (dispatcherAfterLength raw
        (dispatcherAfterOffset
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)))) := by
  let s := dispatcherAfterOffset
    (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
  have hok : ∃ ss vs, s = .Ok ss vs := by
    simp [s, dispatcherAfterOffset, dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.insert]
  have hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s]
    rw [dispatcherAfterOffset_toState, dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 0x44) =
        UInt256.ofNat raw.len :=
    calldataload_encode_length raw digest s.toState hcd
  change exec (n + 9)
      (.Let ["length"] (.some
        (.Call (Sum.inl .CALLDATALOAD)
          [dispatcherLengthOffsetExpr])))
      (some forsVerifierRuntime) s =
    .ok (dispatcherAfterLength raw s)
  rw [show n + 9 = (n + 8) + 1 by omega,
    exec_let_prim (n := n + 8)]
  change execPrimCall (n + 8) .CALLDATALOAD ["length"]
      (reverse' (evalArgs (n + 8) [dispatcherLengthOffsetExpr]
        (some forsVerifierRuntime) s)) =
    .ok (dispatcherAfterLength raw s)
  rw [evalArgs_cons_ok (n := n + 7)
    (h := by
      simpa [dispatcherLengthOffsetExpr] using
        eval_dispatcher_length_offset_at (n + 1) s hok hoffset)]
  rw [evalTail_cons_ok (n := n + 6), evalArgs_nil (n := n + 5)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [execPrimCall_ok
    (h := by
      simpa [hload] using
        (primCall_calldataload (n := n + 7) s (UInt256.ofNat 0x44)))]
  cases s <;> rfl

private theorem evalArgs_dispatcher_recover_at
    (raw : RawSig) (digest : Digest) (n : Nat) :
    reverse' (evalArgs (n + 12)
        [dispatcherDigestExpr, .Var "length", dispatcherSigDataOffsetExpr]
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest)) =
      .ok (dispatcherBeforeRecoverState raw digest,
        [UInt256.ofNat 100, UInt256.ofNat raw.len, UInt256.ofNat digest]) := by
  let s := dispatcherBeforeRecoverState raw digest
  have hok : ∃ ss vs, s = .Ok ss vs := by
    simp [s, dispatcherBeforeRecoverState, dispatcherAfterLength,
      dispatcherAfterOffset, dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.insert]
  have hoffset : EvmYul.Yul.State.lookup! "offset" s = UInt256.ofNat 0x40 := by
    dsimp [s, dispatcherBeforeRecoverState]
    exact dispatcherAfterLength_lookup_offset_after_offset raw digest
  have hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest := by
    dsimp [s, dispatcherBeforeRecoverState]
    rw [dispatcherAfterLength_toState, dispatcherAfterOffset_toState,
      dispatcherAfterFreeMemPtr_toState]
    exact forsInitialState_toState_calldata raw digest
  rw [evalArgs_cons_ok (n := n + 11)
    (h := eval_dispatcher_digest_at raw digest (n + 7) s hcd)]
  rw [evalTail_cons_ok (n := n + 10)]
  rw [evalArgs_cons_ok (n := n + 9)
    (h := eval_var_lookup_at (n + 8) s "length" hok)]
  rw [evalTail_cons_ok (n := n + 8)]
  rw [evalArgs_cons_ok (n := n + 7)
    (h := by
      simpa [dispatcherSigDataOffsetExpr] using
        eval_dispatcher_sig_offset_at (n + 1) s hok hoffset)]
  rw [evalTail_cons_ok (n := n + 6), evalArgs_nil (n := n + 5)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rfl

private theorem exec_dispatcher_recover_call_halts
    (raw : RawSig) (digest : Digest) (n : Nat)
    (S : EvmYul.Yul.State)
    (hcall :
      call (n + 11) (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error (.YulHalt S ⟨1⟩)) :
    exec (n + 13) (.Let ["ret"] (.some dispatcherRecoverCallExpr))
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
      .error (.YulHalt S ⟨1⟩) := by
  change exec (n + 13)
      (.Let ["ret"] (.some
        (.Call (Sum.inr "fun_recover")
          [dispatcherSigDataOffsetExpr, .Var "length", dispatcherDigestExpr])))
      (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
    .error (.YulHalt S ⟨1⟩)
  rw [show n + 13 = (n + 12) + 1 by omega,
    exec_let_call (n := n + 12)]
  change execCall (n + 12) "fun_recover" ["ret"] (some forsVerifierRuntime)
      (reverse' (evalArgs (n + 12)
        [dispatcherDigestExpr, .Var "length", dispatcherSigDataOffsetExpr]
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest))) =
    .error (.YulHalt S ⟨1⟩)
  rw [evalArgs_dispatcher_recover_at raw digest n]
  rw [execCall_ok (n := n + 11)]
  rw [show [UInt256.ofNat 100, UInt256.ofNat raw.len, UInt256.ofNat digest] =
      forsRecoverArgs raw digest by rfl, hcall]
  rfl

private theorem exec_dispatcher_recover_call_err
    (raw : RawSig) (digest : Digest) (n : Nat) (e : Yul.Exception)
    (hcall :
      call (n + 11) (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error e) :
    exec (n + 13) (.Let ["ret"] (.some dispatcherRecoverCallExpr))
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
      .error e := by
  change exec (n + 13)
      (.Let ["ret"] (.some
        (.Call (Sum.inr "fun_recover")
          [dispatcherSigDataOffsetExpr, .Var "length", dispatcherDigestExpr])))
      (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
    .error e
  rw [show n + 13 = (n + 12) + 1 by omega,
    exec_let_call (n := n + 12)]
  change execCall (n + 12) "fun_recover" ["ret"] (some forsVerifierRuntime)
      (reverse' (evalArgs (n + 12)
        [dispatcherDigestExpr, .Var "length", dispatcherSigDataOffsetExpr]
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest))) =
    .error e
  rw [evalArgs_dispatcher_recover_at raw digest n]
  rw [execCall_ok (n := n + 11)]
  rw [show [UInt256.ofNat 100, UInt256.ofNat raw.len, UInt256.ofNat digest] =
      forsRecoverArgs raw digest by rfl, hcall]
  rfl

private theorem exec_revert_zero_zero
    (n : Nat) (co : Option YulContract) (s : EvmYul.Yul.State) :
    exec (n + 6) (.ExprStmtCall (.Call (Sum.inl .REVERT)
        [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])) co s =
      .error .Revert := by
  rw [exec_exprstmt_prim (n := n + 5)]
  show execPrimCall (n + 5) .REVERT []
      (reverse' (evalArgs (n + 5)
        [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)] co s)) =
    .error .Revert
  rw [evalArgs_cons_ok (n := n + 4) (h := eval_lit (n := n + 3)),
    evalTail_cons_ok (n := n + 3),
    evalArgs_cons_ok (n := n + 2) (h := eval_lit (n := n + 1)),
    evalTail_cons_ok (n := n + 1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  exact execPrimCall_err
    (h := primCall_revert (n := n + 4) s (UInt256.ofNat 0)
      (UInt256.ofNat 0))

private theorem exec_revert_body
    (n : Nat) (co : Option YulContract) (s : EvmYul.Yul.State) :
    exec (n + 7)
        (.Block [.ExprStmtCall (.Call (Sum.inl .REVERT)
          [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])]) co s =
      .error .Revert := by
  exact exec_block_cons_err (n := n + 6) (co := co)
    (h := exec_revert_zero_zero n co s)

private theorem exec_dispatcher_recover_case_good
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen)
    (S : EvmYul.Yul.State)
    (hcall :
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error (.YulHalt S ⟨1⟩)) :
    exec 99994 (.Block dispatcherRecoverBody) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .error (.YulHalt S ⟨1⟩) := by
  let s0 := dispatcherAfterFreeMemPtr (forsInitialState raw digest)
  let s1 := dispatcherAfterOffset s0
  let s2 := dispatcherAfterLength raw s1
  have hs0ok : ∃ ss vs, s0 = .Ok ss vs := by
    simp [s0, dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState]
  have hs1ok : ∃ ss vs, s1 = .Ok ss vs := by
    simp [s1, s0, dispatcherAfterOffset, dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.insert]
  have hs2ok : ∃ ss vs, s2 = .Ok ss vs := by
    simp [s2, s1, s0, dispatcherAfterLength, dispatcherAfterOffset,
      dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.insert]
  have hs0size : s0.executionEnv.calldata.size = 2548 := by
    dsimp [s0]
    rw [dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_calldata_size raw digest
  have hs0value : s0.executionEnv.weiValue = UInt256.ofNat 0 := by
    dsimp [s0]
    rw [dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_callvalue raw digest
  have hs1size : s1.executionEnv.calldata.size = 2548 := by
    dsimp [s1]
    rw [dispatcherAfterOffset_executionEnv]
    exact hs0size
  have hs2size : s2.executionEnv.calldata.size = 2548 := by
    dsimp [s2]
    rw [dispatcherAfterLength_executionEnv]
    exact hs1size
  have hs1offset : EvmYul.Yul.State.lookup! "offset" s1 =
      UInt256.ofNat 0x40 := by
    dsimp [s1, s0]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  have hs2offset : EvmYul.Yul.State.lookup! "offset" s2 =
      UInt256.ofNat 0x40 := by
    dsimp [s2, s1, s0]
    exact dispatcherAfterLength_lookup_offset_after_offset raw digest
  have hs2length : EvmYul.Yul.State.lookup! "length" s2 =
      UInt256.ofNat raw.len := by
    dsimp [s2, s1, s0]
    exact dispatcherAfterLength_lookup_length_after_offset raw digest
  rw [dispatcherRecoverBody_shape]
  rw [exec_block_cons_ok (n := 99993)
    (h := exec_if_false
      (eval_dispatcher_callvalue_at 99990 s0 hs0value))]
  rw [exec_block_cons_ok (n := 99992)
    (h := exec_if_false
      (eval_dispatcher_min_calldata_at raw digest 99981 s0 hs0size))]
  rw [exec_block_cons_ok (n := 99991)
    (h := by
      simpa [s0, s1] using
        exec_dispatcher_let_offset_at raw digest 99986)]
  rw [exec_block_cons_ok (n := 99990)
    (h := exec_if_false
      (eval_dispatcher_offset_bound_at 99983 s1 hs1ok hs1offset))]
  rw [exec_block_cons_ok (n := 99989)
    (h := exec_if_false
      (eval_dispatcher_offset_min_at raw digest 99976 s1 hs1ok hs1offset hs1size))]
  rw [exec_block_cons_ok (n := 99988)
    (h := by
      simpa [s0, s1, s2] using
        exec_dispatcher_let_length_at raw digest 99979)]
  rw [exec_block_cons_ok (n := 99987)
    (h := exec_if_false
      (eval_dispatcher_length_bound_at raw 99980 s2 hs2ok hs2length hlen))]
  rw [exec_block_cons_ok (n := 99986)
    (h := exec_if_false
      (eval_dispatcher_payload_bound_at raw digest 99971 s2 hs2ok
        hs2offset hs2length hs2size hlen))]
  apply exec_block_cons_err (n := 99985) (co := some forsVerifierRuntime)
  simpa [s2, s1, s0, recoverFuel] using
    exec_dispatcher_recover_call_halts raw digest 99972 S hcall

private theorem exec_dispatcher_recover_case_bad
    (raw : RawSig) (digest : Digest)
    (hcall :
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error .OutOfFuel) :
    exec 99994 (.Block dispatcherRecoverBody) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error .OutOfFuel
      ∨
    exec 99994 (.Block dispatcherRecoverBody) (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error .Revert := by
  let s0 := dispatcherAfterFreeMemPtr (forsInitialState raw digest)
  let s1 := dispatcherAfterOffset s0
  let s2 := dispatcherAfterLength raw s1
  let lengthGuard := UInt256.gt (UInt256.ofNat raw.len)
    (UInt256.ofNat 0xffffffffffffffff)
  let payloadGuard := UInt256.gt
    (((UInt256.ofNat 0x40).add (UInt256.ofNat raw.len)).add
      (UInt256.ofNat 36))
    (UInt256.ofNat 2548)
  have hs0ok : ∃ ss vs, s0 = .Ok ss vs := by
    simp [s0, dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState]
  have hs1ok : ∃ ss vs, s1 = .Ok ss vs := by
    simp [s1, s0, dispatcherAfterOffset, dispatcherAfterFreeMemPtr,
      forsInitialState, EvmYul.Yul.State.setMachineState,
      EvmYul.Yul.State.insert]
  have hs2ok : ∃ ss vs, s2 = .Ok ss vs := by
    simp [s2, s1, s0, dispatcherAfterLength, dispatcherAfterOffset,
      dispatcherAfterFreeMemPtr, forsInitialState,
      EvmYul.Yul.State.setMachineState, EvmYul.Yul.State.insert]
  have hs0size : s0.executionEnv.calldata.size = 2548 := by
    dsimp [s0]
    rw [dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_calldata_size raw digest
  have hs0value : s0.executionEnv.weiValue = UInt256.ofNat 0 := by
    dsimp [s0]
    rw [dispatcherAfterFreeMemPtr_executionEnv]
    exact forsInitialState_callvalue raw digest
  have hs1size : s1.executionEnv.calldata.size = 2548 := by
    dsimp [s1]
    rw [dispatcherAfterOffset_executionEnv]
    exact hs0size
  have hs2size : s2.executionEnv.calldata.size = 2548 := by
    dsimp [s2]
    rw [dispatcherAfterLength_executionEnv]
    exact hs1size
  have hs1offset : EvmYul.Yul.State.lookup! "offset" s1 =
      UInt256.ofNat 0x40 := by
    dsimp [s1, s0]
    exact dispatcherAfterOffset_lookup_offset_after_free_mem_ptr raw digest
  have hs2offset : EvmYul.Yul.State.lookup! "offset" s2 =
      UInt256.ofNat 0x40 := by
    dsimp [s2, s1, s0]
    exact dispatcherAfterLength_lookup_offset_after_offset raw digest
  have hs2length : EvmYul.Yul.State.lookup! "length" s2 =
      UInt256.ofNat raw.len := by
    dsimp [s2, s1, s0]
    exact dispatcherAfterLength_lookup_length_after_offset raw digest
  have hlengthEval :
      eval 99986 dispatcherLengthBoundGuardExpr (some forsVerifierRuntime) s2 =
        .ok (s2, lengthGuard) := by
    simpa [lengthGuard] using
      eval_dispatcher_length_bound_word_at raw 99980 s2 hs2ok hs2length
  have hpayloadEval :
      eval 99985 dispatcherPayloadBoundGuardExpr (some forsVerifierRuntime) s2 =
        .ok (s2, payloadGuard) := by
    simpa [payloadGuard] using
      eval_dispatcher_payload_bound_word_at raw digest 99971 s2 hs2ok
        hs2offset hs2length hs2size
  rw [dispatcherRecoverBody_shape]
  rw [exec_block_cons_ok (n := 99993)
    (h := exec_if_false
      (eval_dispatcher_callvalue_at 99990 s0 hs0value))]
  rw [exec_block_cons_ok (n := 99992)
    (h := exec_if_false
      (eval_dispatcher_min_calldata_at raw digest 99981 s0 hs0size))]
  rw [exec_block_cons_ok (n := 99991)
    (h := by simpa [s0, s1] using
      exec_dispatcher_let_offset_at raw digest 99986)]
  rw [exec_block_cons_ok (n := 99990)
    (h := exec_if_false
      (eval_dispatcher_offset_bound_at 99983 s1 hs1ok hs1offset))]
  rw [exec_block_cons_ok (n := 99989)
    (h := exec_if_false
      (eval_dispatcher_offset_min_at raw digest 99976 s1 hs1ok
        hs1offset hs1size))]
  rw [exec_block_cons_ok (n := 99988)
    (h := by simpa [s0, s1, s2] using
      exec_dispatcher_let_length_at raw digest 99979)]
  by_cases hlength : lengthGuard = UInt256.ofNat 0
  · rw [exec_block_cons_ok (n := 99987)
      (h := exec_if_false (by simpa [hlength] using hlengthEval))]
    by_cases hpayload : payloadGuard = UInt256.ofNat 0
    · left
      rw [exec_block_cons_ok (n := 99986)
        (h := exec_if_false (by simpa [hpayload] using hpayloadEval))]
      apply exec_block_cons_err (n := 99985) (co := some forsVerifierRuntime)
      simpa [s2, s1, s0, recoverFuel] using
        exec_dispatcher_recover_call_err raw digest 99972 .OutOfFuel
          hcall
    · right
      apply exec_block_cons_err (n := 99986) (co := some forsVerifierRuntime)
      rw [exec_if_true hpayloadEval hpayload]
      simpa using exec_revert_body 99978 (some forsVerifierRuntime) s2
  · right
    apply exec_block_cons_err (n := 99987) (co := some forsVerifierRuntime)
    rw [exec_if_true hlengthEval hlength]
    simpa using exec_revert_body 99979 (some forsVerifierRuntime) s2

private theorem execSwitchCases_cons_result
    {n : Nat} {co : Option YulContract} {s : EvmYul.Yul.State}
    {val : EvmYul.Literal} {body : List Stmt}
    {cases : List (EvmYul.Literal × List Stmt)}
    {result : Except Yul.Exception EvmYul.Yul.State} {rest}
    (hbody : exec n (.Block body) co s = result)
    (hrest : execSwitchCases n co s cases = .ok rest) :
    execSwitchCases (n + 1) co s ((val, body) :: cases) =
      .ok ((val, result) :: rest) := by
  rw [show n + 1 = Nat.succ n by omega, execSwitchCases, hbody, hrest]
  cases result with
  | ok _ => rfl
  | error e =>
      cases e <;> rfl

private theorem execSwitchCases_exists_of_length_le
    (fuel : Nat) (co : Option YulContract) (s : EvmYul.Yul.State)
    (cases : List (EvmYul.Literal × List Stmt)) (h : cases.length ≤ fuel) :
    ∃ branches, execSwitchCases fuel co s cases = .ok branches := by
  induction cases generalizing fuel with
  | nil =>
      refine ⟨[], ?_⟩
      exact execSwitchCases_nil
  | cons c cases ih =>
      cases fuel with
      | zero => simp at h
      | succ fuel =>
          have htail : cases.length ≤ fuel := by simpa using h
          obtain ⟨rest, hrest⟩ := ih fuel htail
          cases hbody : exec fuel (.Block c.2) co s with
          | ok s' =>
              refine ⟨(c.1, .ok s') :: rest, ?_⟩
              simpa using execSwitchCases_cons_result hbody hrest
          | error e =>
              refine ⟨(c.1, .error e) :: rest, ?_⟩
              simpa using execSwitchCases_cons_result hbody hrest

private theorem exec_dispatcher_switch_good
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen)
    (S : EvmYul.Yul.State)
    (hcall :
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error (.YulHalt S ⟨1⟩)) :
    exec 99996
        (.Switch dispatcherSelectorExpr dispatcherCases [.Break])
        (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .error (.YulHalt S ⟨1⟩) := by
  have hrecover :=
    exec_dispatcher_recover_case_good raw digest hlen S hcall
  obtain ⟨rest, hrest⟩ :=
    execSwitchCases_exists_of_length_le 99994 (some forsVerifierRuntime)
      (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      dispatcherOtherCases (by rw [dispatcherOtherCases_length]; omega)
  have hcases :
      execSwitchCases 99995 (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
          dispatcherCases =
        .ok ((UInt256.ofNat 0x1aad75c5, .error (.YulHalt S ⟨1⟩)) :: rest) := by
    rw [dispatcherCases_shape]
    simpa using execSwitchCases_cons_result hrecover hrest
  have hdefault :
      exec 99995 (.Block [.Break]) (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .ok (💔 (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
    rw [exec_block_cons_ok (n := 99994)
      (h := exec_break (n := 99993))]
    exact exec_block_nil
  rw [exec_switch_ok
    (hcond := eval_dispatcher_selector_at raw digest 99989
      (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      (by
        rw [dispatcherAfterFreeMemPtr_toState]
        exact forsInitialState_toState_calldata raw digest))
    (hcases := hcases) (hdef := hdefault)]
  simp

private theorem forsDispatcher_shape :
    forsDispatcher =
      .Block
        [dispatcherFreeMemPtrStmt,
         .If dispatcherHasSelectorGuardExpr
           [.Switch dispatcherSelectorExpr dispatcherCases [.Break]],
         .ExprStmtCall (.Call (Sum.inl .REVERT)
           [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)])] := by
  simp [forsDispatcher, dispatcherFreeMemPtrStmt, dispatcherHasSelectorGuardExpr,
    dispatcherCalldataSizeExpr, dispatcherSelectorExpr, dispatcherCases]

private theorem exec_dispatcher_good
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen)
    (S : EvmYul.Yul.State)
    (hcall :
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
        .error (.YulHalt S ⟨1⟩)) :
    exec 100000 forsDispatcher (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .error (.YulHalt S ⟨1⟩) := by
  have hswitch :=
    exec_dispatcher_switch_good raw digest hlen S hcall
  have hfree :
      exec 99999 dispatcherFreeMemPtrStmt (some forsVerifierRuntime)
          (forsInitialState raw digest) =
        .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) := by
    simpa [dispatcherFreeMemPtrStmt] using
      (exec_mstore_lit (n := 99993) (co := some forsVerifierRuntime)
        (s := forsInitialState raw digest)
        (a := UInt256.ofNat 64) (v := UInt256.ofNat 0x80)
        (e := .Lit (UInt256.ofNat 0x80))
        (he := eval_lit (n := 99996)))
  have hif :
      exec 99998
          (.If dispatcherHasSelectorGuardExpr
            [.Switch dispatcherSelectorExpr dispatcherCases [.Break]])
          (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error (.YulHalt S ⟨1⟩) := by
    rw [exec_if_true
      (h := eval_dispatcher_has_selector_at raw digest 99989
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
        (by
          rw [dispatcherAfterFreeMemPtr_executionEnv]
          exact forsInitialState_calldata_size raw digest))
      (hc := by decide)]
    exact exec_block_cons_err (n := 99996) (co := some forsVerifierRuntime)
      (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      (sts := []) (h := hswitch)
  rw [forsDispatcher_shape]
  rw [exec_block_cons_ok (n := 99999) (h := hfree)]
  exact exec_block_cons_err (n := 99998) (co := some forsVerifierRuntime)
    (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (h := hif)

/-- The full dispatcher and the aligned scoped runner agree at the valid FORS
    signature length. -/
theorem evmRun_eq_recover_of_sigLen
    (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen) :
    evmRun raw digest = evmRunRecover raw digest := by
  obtain ⟨S, hcall⟩ := call_recover_good_length_halts raw digest hlen
  have hfull := exec_dispatcher_good raw digest hlen S hcall
  unfold evmRun evmRunRecover
  rw [if_pos hlen]
  rw [runForsCalldata_encode_unfold, hfull]
  unfold runForsRecover
  rw [hcall]

/-! ## Malformed-length leave path

The interpreter keeps executing a block after `.Leave`. When the checkpoint
reaches the tree loop, `mkOk` supplies the default state for one iteration and
`overwrite?` restores the same leave checkpoint before the recursive call.
The fixed fuel therefore decreases by three forever and ends in `OutOfFuel`. -/

private theorem exec_tree_selector4_oof_16
    (co : Option YulContract) (s : EvmYul.Yul.State) :
    exec 16 (treeSelectorLetStmt "usr_s_4" 1 (.Var "ret")) co s =
      .error .OutOfFuel := by
  have hshl :
      eval 4 (.Call (Sum.inl .SHL)
        [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"]) co s =
        .error .OutOfFuel := by
    rw [eval_call_prim]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rw [evalArgs_cons_ok (n := 2) (h := eval_var (n := 1))]
    rw [evalTail_cons_ok (n := 1)]
    rw [show evalArgs 1 [.Lit (UInt256.ofNat 1)] co s =
        .error .OutOfFuel by
      rw [evalArgs, eval, evalTail]]
    simp [cons', reverse', evalPrimCall]
  have hinner :
      eval 8
        (.Call (Sum.inl .AND)
          [.Call (Sum.inl .SHL)
            [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"],
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 31)]])
        co s = .error .OutOfFuel := by
    rw [eval_call_prim]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rw [evalArgs_cons_ok (n := 6)
      (h := eval_not_mask (n := 2) (UInt256.ofNat 31))]
    rw [evalTail_cons_ok (n := 5)]
    rw [show evalArgs 5
        [.Call (Sum.inl .SHL)
          [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"]] co s =
        .error .OutOfFuel by
      rw [evalArgs, hshl, evalTail]]
    simp [cons', reverse', evalPrimCall]
  have hmid :
      eval 12
        (.Call (Sum.inl .AND)
          [.Call (Sum.inl .AND)
            [.Call (Sum.inl .SHL)
              [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"],
             .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 31)]],
           .Var "ret"])
        co s = .error .OutOfFuel := by
    rw [eval_call_prim]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append]
    rw [evalArgs_cons_ok (n := 10) (h := eval_var (n := 9))]
    rw [evalTail_cons_ok (n := 9)]
    rw [show evalArgs 9
        [.Call (Sum.inl .AND)
          [.Call (Sum.inl .SHL)
            [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"],
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 31)]]] co s =
        .error .OutOfFuel by
      rw [evalArgs, hinner, evalTail]]
    simp [cons', reverse', evalPrimCall]
  unfold treeSelectorLetStmt
  conv_lhs => rw [exec]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [evalArgs_cons_ok (n := 14) (h := eval_var (n := 13))]
  rw [evalTail_cons_ok (n := 13)]
  rw [show evalArgs 13
      [.Call (Sum.inl .AND)
        [.Call (Sum.inl .AND)
          [.Call (Sum.inl .SHL)
            [.Lit (UInt256.ofNat 1), .Var "usr_dCursor"],
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 31)]],
         .Var "ret"]] co s =
      .error .OutOfFuel by
    rw [evalArgs, hmid, evalTail]]
  simp [cons', reverse', execPrimCall]

private theorem exec_tree_body_oof_40
    (co : Option YulContract) (ss : SharedState .Yul) (vs : VarStore) :
    exec 40 (.Block forsTreeBody) co (.Ok ss vs) =
      .error .OutOfFuel := by
  rw [show 40 = 27 + 13 by omega,
    exec_tree_body_leaf_prefix 27 co ss vs]
  rw [show 27 + 10 = 17 + 20 by omega, exec_tree_body_node1 17 co]
  rw [show 17 + 15 = 12 + 20 by omega, exec_tree_body_node2 12 co]
  rw [show 12 + 15 = 7 + 20 by omega, exec_tree_body_node3 7 co]
  rw [show 7 + 15 = 2 + 20 by omega, exec_tree_body_node4 2 co]
  rw [show forsTreeBody.drop 23 =
      treeSelectorLetStmt "usr_s_4" 1 (.Var "ret") ::
        forsTreeBody.drop 24 from rfl]
  exact exec_block_cons_err (n := 16) (co := co)
    (h := exec_tree_selector4_oof_16 co _)

private theorem exec_tree_for_leave_oof
    (co : Option YulContract) (ss : SharedState .Yul) (vs : VarStore) (k : Nat) :
    exec (43 + 3 * k) (.For forsTreeCond forsTreePost forsTreeBody) co
        (🚪 (EvmYul.Yul.State.Ok ss vs)) =
      .error .OutOfFuel := by
  induction k with
  | zero =>
      have hcond :
          eval 40 forsTreeCond co (👌 (🚪 (EvmYul.Yul.State.Ok ss vs))) =
            .ok (Inhabited.default, UInt256.ofNat 1) := by
        have h := eval_tree_cond (n := 34) (co := co)
          (s := (Inhabited.default : EvmYul.Yul.State))
        rw [show (Inhabited.default : EvmYul.Yul.State)[usrTId]! =
            UInt256.ofNat 0 from rfl] at h
        simpa [EvmYul.Yul.State.mkOk] using h
      rw [show 43 = 42 + 1 by omega, exec_for]
      conv_lhs => rw [loop]
      rw [hcond]
      simp only
      rw [if_neg uint256_one_ne_zero]
      rw [show (Inhabited.default : EvmYul.Yul.State) =
          .Ok Inhabited.default Inhabited.default from rfl]
      rw [exec_tree_body_oof_40]
  | succ k ih =>
      let d : EvmYul.Yul.State := Inhabited.default
      have hcond :
          eval (43 + 3 * k) forsTreeCond co
              (👌 (🚪 (EvmYul.Yul.State.Ok ss vs))) =
            .ok (d, UInt256.ofNat 1) := by
        have h := eval_tree_cond (n := 37 + 3 * k) (co := co) (s := d)
        rw [show d[usrTId]! = UInt256.ofNat 0 from rfl] at h
        simpa [d, EvmYul.Yul.State.mkOk, show
          37 + 3 * k + 6 = 43 + 3 * k by omega] using h
      have hbody :
          exec (43 + 3 * k) (.Block forsTreeBody) co d =
            .ok (treeIterState d) := by
        change exec (43 + 3 * k) (.Block forsTreeBody) co
            (.Ok Inhabited.default Inhabited.default) = _
        simpa [d, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          exec_tree_body_iter (3 * k) co
            (Inhabited.default : SharedState .Yul)
            (Inhabited.default : VarStore)
      have hpost :
          exec (43 + 3 * k) (.Block forsTreePost) co
              (🧟 (treeIterState d)) =
            .ok (treePostState (treeIterState d)) := by
        have hok := treeIterState_ok
          (Inhabited.default : SharedState .Yul)
          (Inhabited.default : VarStore)
        change exec (43 + 3 * k) (.Block forsTreePost) co
            (treeIterState d) = _
        simpa [show 43 + 3 * k = (32 + 3 * k) + 11 by omega] using
          exec_tree_post (32 + 3 * k) co (treeIterState d)
      have hrec :
          exec (43 + 3 * k) (.For forsTreeCond forsTreePost forsTreeBody) co
              ((treePostState (treeIterState d))
                ✏️⟦🚪 (EvmYul.Yul.State.Ok ss vs)⟧?) =
            .error .OutOfFuel := by
        simpa [EvmYul.Yul.State.overwrite?] using ih
      rw [show 43 + 3 * (k + 1) = ((43 + 3 * k) + 2) + 1 by omega,
        exec_for]
      conv_lhs => rw [loop]
      rw [hcond]
      simp only
      rw [if_neg uint256_one_ne_zero]
      rw [hbody]
      obtain ⟨ss', vs', hok⟩ := treeIterState_ok
        (Inhabited.default : SharedState .Yul)
        (Inhabited.default : VarStore)
      change treeIterState d = .Ok ss' vs' at hok
      rw [hok] at hpost hrec
      rw [hok]
      simp only
      rw [hpost]
      simp only
      rw [hrec]

private def recoverLengthLeaveState
    (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  🚪 ((recoverAfterRet3FromRet2 raw digest).insert
    "var" (UInt256.ofNat 0))

private theorem recoverLengthLeaveState_lookup_dVal
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "usr_dVal"
        (recoverLengthLeaveState raw digest) =
      UInt256.ofNat 0 := by
  rfl

private theorem exec_recover_hmsg_checkpoint
    (raw : RawSig) (digest : Digest) (co : Option YulContract) (n : Nat) :
    exec (n + 37) (.Block (forsFunRecover.body.drop 18)) co
        (recoverLengthLeaveState raw digest) =
      exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co
        (recoverLengthLeaveState raw digest) := by
  let C := recoverLengthLeaveState raw digest
  obtain ⟨ss, vs, hs⟩ :
      ∃ ss vs, recoverAfterRet3FromRet2 raw digest = .Ok ss vs :=
    ⟨_, _, rfl⟩
  have hC :
      C = .Checkpoint (.Leave ss (vs.insert "var" (UInt256.ofNat 0))) := by
    simp [C, recoverLengthLeaveState, hs, EvmYul.Yul.State.insert,
      EvmYul.Yul.State.setLeave]
  change exec (n + 37) (.Block (forsFunRecover.body.drop 18)) co C =
    exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co C
  rw [show forsFunRecover.body.drop 18
      = (.Let ["usr_pkSeed"] (.some (.Call (Sum.inl .AND)
          [.Call (Sum.inl .CALLDATALOAD)
            [.Call (Sum.inl .ADD)
              [.Var "var_sig_offset", .Lit (UInt256.ofNat 0x10)]],
           .Call (Sum.inl .NOT)
             [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]])))
        :: forsFunRecover.body.drop 19 from rfl]
  rw [exec_block_cons_ok (n := n + 36) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_let_masked_addvlit (n := n + 24) (co := co) (s := C)
        (x := "usr_pkSeed") (var := "var_sig_offset")
        (b := UInt256.ofNat 0x10)
        (mask := UInt256.ofNat 0xffffffffffffffffffffffffffffffff)))]
  rw [show forsFunRecover.body.drop 19
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0), .Var "usr_pkSeed"]))
        :: forsFunRecover.body.drop 20 from rfl]
  rw [exec_block_cons_ok (n := n + 35) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_lit (n := n + 29) (co := co) (s := C)
        (a := UInt256.ofNat 0) (e := .Var "usr_pkSeed")
        (he := eval_var)))]
  rw [show forsFunRecover.body.drop 20
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Var "ret",
           .Call (Sum.inl .AND)
             [.Call (Sum.inl .CALLDATALOAD) [.Var "var_sig_offset"],
              .Call (Sum.inl .NOT)
                [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]]))
        :: forsFunRecover.body.drop 21 from rfl]
  rw [exec_block_cons_ok (n := n + 34) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_expr (n := n + 28) (co := co) (s := C)
        (e₁ := .Var "ret")
        (he₁ := eval_var)
        (he₂ := eval_tree_masked_calldata (n := n + 24)
          (he := eval_var (n := n + 25)))))]
  rw [show forsFunRecover.body.drop 21
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0x40), .Var "var_digest"]))
        :: forsFunRecover.body.drop 22 from rfl]
  rw [exec_block_cons_ok (n := n + 33) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_lit (n := n + 27) (co := co) (s := C)
        (a := UInt256.ofNat 0x40) (e := .Var "var_digest")
        (he := eval_var)))]
  rw [show forsFunRecover.body.drop 22
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Var "ret_2", .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 2)]]))
        :: forsFunRecover.body.drop 23 from rfl]
  rw [exec_block_cons_ok (n := n + 32) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_expr (n := n + 26) (co := co) (s := C)
        (e₁ := .Var "ret_2") (he₁ := eval_var)
        (he₂ := eval_not_mask (n := n + 26) (UInt256.ofNat 2))))]
  rw [show forsFunRecover.body.drop 23
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 128),
           .Call (Sum.inl .AND)
             [.Call (Sum.inl .CALLDATALOAD)
               [.Call (Sum.inl .ADD)
                 [.Call (Sum.inl .ADD)
                   [.Var "var_sig_offset", .Var "product"],
                  .Var "ret"]],
              .Call (Sum.inl .NOT)
                [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]]))
        :: forsFunRecover.body.drop 24 from rfl]
  rw [exec_block_cons_ok (n := n + 31) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_lit (n := n + 25) (co := co) (s := C)
        (a := UInt256.ofNat 128)
        (he := eval_tree_masked_calldata (n := n + 21)
          (he := eval_binop2 (n := n + 17) (OP := .ADD)
            (f := UInt256.add)
            (hprim := primCall_add (n := n + 21) _ _)
            (he₁ := eval_tree_add_var_var (n := n + 13))
            (he₂ := eval_var (n := n + 20))))))]
  rw [show forsFunRecover.body.drop 24
      = (.Let ["usr_dVal"] (.some (.Call (Sum.inl .KECCAK256)
          [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0xa0)])))
        :: forsFunRecover.body.drop 25 from rfl]
  rw [exec_block_cons_ok (n := n + 30) (h := by
    simpa [hC, EvmYul.Yul.State.insert, EvmYul.Yul.State.setMachineState] using
      (exec_let_keccak_lit_lit (n := n + 22) (co := co) (s := C)))]
  rw [hC]

private theorem exec_recover_checkpoint_to_tree
    (raw : RawSig) (digest : Digest) (co : Option YulContract) (n : Nat) :
    exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co
        (recoverLengthLeaveState raw digest) =
      exec (n + 23) (.Block (forsFunRecover.body.drop 32)) co
        (recoverLengthLeaveState raw digest) := by
  let C := recoverLengthLeaveState raw digest
  obtain ⟨ss, vs, hs⟩ :
      ∃ ss vs, recoverAfterRet3FromRet2 raw digest = .Ok ss vs :=
    ⟨_, _, rfl⟩
  have hC :
      C = .Checkpoint (.Leave ss (vs.insert "var" (UInt256.ofNat 0))) := by
    simp [C, recoverLengthLeaveState, hs, EvmYul.Yul.State.insert,
      EvmYul.Yul.State.setLeave]
  change exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co C =
    exec (n + 23) (.Block (forsFunRecover.body.drop 32)) co C
  have hdv : EvmYul.Yul.State.lookup! "usr_dVal" C = UInt256.ofNat 0 := by
    simpa [C] using recoverLengthLeaveState_lookup_dVal raw digest
  have hshr :
      eval (n + 24)
          (.Call (Sum.inl .SHR)
            [.Lit (UInt256.ofNat 125), .Var "usr_dVal"]) co C =
        .ok (C, UInt256.ofNat 0) := by
    have h := eval_tree_shr_lit_var (n := n + 18) (co := co) (s := C)
      (b := UInt256.ofNat 125) (x := "usr_dVal")
    have hdv' : C[(show Identifier from "usr_dVal")]! = UInt256.ofNat 0 := by
      rw [hC]
      rfl
    rw [hdv'] at h
    simpa using h
  have hguard :
      eval (n + 28)
          (.Call (Sum.inl .AND)
            [.Call (Sum.inl .SHR)
              [.Lit (UInt256.ofNat 125), .Var "usr_dVal"],
             .Lit (UInt256.ofNat 31)]) co C =
        .ok (C, UInt256.ofNat 0) := by
    have h := eval_binop2 (n := n + 22) (co := co) (s := C)
      (OP := .AND) (f := UInt256.land)
      (hprim := primCall_and (n := n + 26) (s := C)
        (UInt256.ofNat 0) (UInt256.ofNat 31))
      (he₁ := hshr) (he₂ := eval_lit (n := n + 25))
    simpa using h
  rw [show forsFunRecover.body.drop 25
      = (.If (.Call (Sum.inl .AND)
            [.Call (Sum.inl .SHR)
              [.Lit (UInt256.ofNat 125), .Var "usr_dVal"],
             .Lit (UInt256.ofNat 31)])
          [.ExprStmtCall (.Call (Sum.inl .MSTORE)
            [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0)]),
           .ExprStmtCall (.Call (Sum.inl .RETURN)
            [.Lit (UInt256.ofNat 0), .Var "ret"])])
        :: forsFunRecover.body.drop 26 from rfl]
  rw [exec_block_cons_ok (n := n + 29)
    (h := exec_if_false (n := n + 28) hguard)]
  rw [show forsFunRecover.body.drop 26
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0x380), .Var "usr_pkSeed"]))
        :: forsFunRecover.body.drop 27 from rfl]
  rw [exec_block_cons_ok (n := n + 28) (h := by
    simpa [hC, EvmYul.Yul.State.setMachineState] using
      (exec_mstore_lit (n := n + 22) (co := co) (s := C)
        (a := UInt256.ofNat 0x380) (e := .Var "usr_pkSeed")
        (he := eval_var)))]
  rw [show forsFunRecover.body.drop 27
      = (.Let ["usr_t"] (.some (.Lit (UInt256.ofNat 0))))
        :: forsFunRecover.body.drop 28 from rfl]
  rw [exec_block_cons_ok (n := n + 27) (h := by
    simpa [hC, EvmYul.Yul.State.insert] using
      (exec_let_lit (n := n + 26) (co := co) (s := C)
        (vars := ["usr_t"]) (lit := UInt256.ofNat 0)))]
  rw [show forsFunRecover.body.drop 28
      = (.Let ["usr_treePtr"] (.some (.Call (Sum.inl .ADD)
          [.Var "var_sig_offset", .Var "ret"])))
        :: forsFunRecover.body.drop 29 from rfl]
  rw [exec_block_cons_ok (n := n + 26) (h := by
    simpa [hC, EvmYul.Yul.State.insert] using
      (exec_let_binop (n := n + 20) (co := co) (s := C)
        (x := "usr_treePtr") (OP := .ADD)
        (e₁ := .Var "var_sig_offset") (e₂ := .Var "ret")
        (hprim := primCall_add (n := n + 24) _ _)
        (he₁ := eval_var (n := n + 21))
        (he₂ := eval_var (n := n + 23))))]
  rw [show forsFunRecover.body.drop 29
      = (.Let ["usr_rootPtr"] (.some (.Lit (UInt256.ofNat 0x40))))
        :: forsFunRecover.body.drop 30 from rfl]
  rw [exec_block_cons_ok (n := n + 25) (h := by
    simpa [hC, EvmYul.Yul.State.insert] using
      (exec_let_lit (n := n + 24) (co := co) (s := C)
        (vars := ["usr_rootPtr"]) (lit := UInt256.ofNat 0x40)))]
  rw [show forsFunRecover.body.drop 30
      = (.Let ["usr_tLeafBase"] (.some (.Lit (UInt256.ofNat 0))))
        :: forsFunRecover.body.drop 31 from rfl]
  rw [exec_block_cons_ok (n := n + 24) (h := by
    simpa [hC, EvmYul.Yul.State.insert] using
      (exec_let_lit (n := n + 23) (co := co) (s := C)
        (vars := ["usr_tLeafBase"]) (lit := UInt256.ofNat 0)))]
  rw [show forsFunRecover.body.drop 31
      = (.Let ["usr_dCursor"] (.some (.Var "usr_dVal")))
        :: forsFunRecover.body.drop 32 from rfl]
  rw [exec_block_cons_ok (n := n + 23) (h := by
    simpa [hC, EvmYul.Yul.State.insert] using
      (exec_let_var (n := n + 22) (co := co) (s := C)
        (vars := ["usr_dCursor"]) (id := "usr_dVal")))]
  rw [hC]

private theorem exec_recover_bad_length_oof
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw) (hlen : raw.len ≠ SigLen) :
    exec 99982 (.Block forsFunRecover.body) (some forsVerifierRuntime)
        (recoverEntryState raw digest) =
      .error .OutOfFuel := by
  have hword := recover_length_word_ne_of_raw_ne raw hfit hlen
  rw [show 99982 = 99935 + 47 by omega,
    exec_recover_prefix_to_length_guard raw digest 99935]
  rw [exec_block_cons_ok (n := 99964)
    (h := exec_recover_length_reject_if_word_ne raw digest 99935 hword)]
  change exec 99964 (.Block (forsFunRecover.body.drop 18))
      (some forsVerifierRuntime) (recoverLengthLeaveState raw digest) = _
  rw [show 99964 = 99927 + 37 by omega,
    exec_recover_hmsg_checkpoint raw digest (some forsVerifierRuntime) 99927]
  rw [show 99927 + 30 = 99927 + 30 by rfl,
    exec_recover_checkpoint_to_tree raw digest (some forsVerifierRuntime) 99927]
  rw [show forsFunRecover.body.drop 32 =
      (.For forsTreeCond forsTreePost forsTreeBody) ::
        forsFunRecover.body.drop 33 from rfl]
  apply exec_block_cons_err (n := 99949) (co := some forsVerifierRuntime)
  obtain ⟨ss, vs, hs⟩ :
      ∃ ss vs, recoverAfterRet3FromRet2 raw digest = .Ok ss vs :=
    ⟨_, _, rfl⟩
  change exec 99949 (.For forsTreeCond forsTreePost forsTreeBody)
      (some forsVerifierRuntime)
      (🚪 ((recoverAfterRet3FromRet2 raw digest).insert
        "var" (UInt256.ofNat 0))) = _
  simpa [hs, show 99949 = 43 + 3 * 33302 by omega] using
    exec_tree_for_leave_oof (some forsVerifierRuntime) ss
      (vs.insert "var" (UInt256.ofNat 0)) 33302

private theorem call_recover_bad_length_oof
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw) (hlen : raw.len ≠ SigLen) :
    call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
        (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest) =
      .error .OutOfFuel := by
  unfold recoverFuel
  apply call_err
    (dispatcherBeforeRecoverState_account_find raw digest)
    (by simpa using forsVerifierRuntime_lookup_fun_recover)
  simpa [recoverEntryState, recoverGoodArgs, forsRecoverArgs] using
    exec_recover_bad_length_oof raw digest hfit hlen

private theorem exec_dispatcher_switch_err
    (raw : RawSig) (digest : Digest) (e : Yul.Exception)
    (hrecover :
      exec 99994 (.Block dispatcherRecoverBody) (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error e) :
    exec 99996
        (.Switch dispatcherSelectorExpr dispatcherCases [.Break])
        (some forsVerifierRuntime)
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
      .error e := by
  obtain ⟨rest, hrest⟩ :=
    execSwitchCases_exists_of_length_le 99994 (some forsVerifierRuntime)
      (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      dispatcherOtherCases (by rw [dispatcherOtherCases_length]; omega)
  have hcases :
      execSwitchCases 99995 (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
          dispatcherCases =
        .ok ((UInt256.ofNat 0x1aad75c5, .error e) :: rest) := by
    rw [dispatcherCases_shape]
    simpa using execSwitchCases_cons_result hrecover hrest
  have hdefault :
      exec 99995 (.Block [.Break]) (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .ok (💔 (dispatcherAfterFreeMemPtr (forsInitialState raw digest))) := by
    rw [exec_block_cons_ok (n := 99994)
      (h := exec_break (n := 99993))]
    exact exec_block_nil
  rw [exec_switch_ok
    (hcond := eval_dispatcher_selector_at raw digest 99989
      (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      (by
        rw [dispatcherAfterFreeMemPtr_toState]
        exact forsInitialState_toState_calldata raw digest))
    (hcases := hcases) (hdef := hdefault)]
  simp

private theorem exec_dispatcher_err
    (raw : RawSig) (digest : Digest) (e : Yul.Exception)
    (hswitch :
      exec 99996
          (.Switch dispatcherSelectorExpr dispatcherCases [.Break])
          (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error e) :
    exec 100000 forsDispatcher (some forsVerifierRuntime)
        (forsInitialState raw digest) =
      .error e := by
  have hfree :
      exec 99999 dispatcherFreeMemPtrStmt (some forsVerifierRuntime)
          (forsInitialState raw digest) =
        .ok (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) := by
    simpa [dispatcherFreeMemPtrStmt] using
      (exec_mstore_lit (n := 99993) (co := some forsVerifierRuntime)
        (s := forsInitialState raw digest)
        (a := UInt256.ofNat 64) (v := UInt256.ofNat 0x80)
        (e := .Lit (UInt256.ofNat 0x80))
        (he := eval_lit (n := 99996)))
  have hif :
      exec 99998
          (.If dispatcherHasSelectorGuardExpr
            [.Switch dispatcherSelectorExpr dispatcherCases [.Break]])
          (some forsVerifierRuntime)
          (dispatcherAfterFreeMemPtr (forsInitialState raw digest)) =
        .error e := by
    rw [exec_if_true
      (h := eval_dispatcher_has_selector_at raw digest 99989
        (dispatcherAfterFreeMemPtr (forsInitialState raw digest))
        (by
          rw [dispatcherAfterFreeMemPtr_executionEnv]
          exact forsInitialState_calldata_size raw digest))
      (hc := by decide)]
    exact exec_block_cons_err (n := 99996) (co := some forsVerifierRuntime)
      (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
      (sts := []) (h := hswitch)
  rw [forsDispatcher_shape]
  rw [exec_block_cons_ok (n := 99999) (h := hfree)]
  exact exec_block_cons_err (n := 99998) (co := some forsVerifierRuntime)
    (s := dispatcherAfterFreeMemPtr (forsInitialState raw digest))
    (h := hif)

private theorem exec_dispatcher_bad_length
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw) (hlen : raw.len ≠ SigLen) :
    exec 100000 forsDispatcher (some forsVerifierRuntime)
        (forsInitialState raw digest) =
        .error .OutOfFuel
      ∨
    exec 100000 forsDispatcher (some forsVerifierRuntime)
        (forsInitialState raw digest) =
        .error .Revert := by
  have hcall := call_recover_bad_length_oof raw digest hfit hlen
  rcases exec_dispatcher_recover_case_bad raw digest hcall with
    hrecover | hrecover
  · left
    exact exec_dispatcher_err raw digest .OutOfFuel
      (exec_dispatcher_switch_err raw digest .OutOfFuel hrecover)
  · right
    exact exec_dispatcher_err raw digest .Revert
      (exec_dispatcher_switch_err raw digest .Revert hrecover)

private theorem evmRun_zero_of_bad_length
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw) (hlen : raw.len ≠ SigLen) :
    evmRun raw digest = 0 := by
  rcases exec_dispatcher_bad_length raw digest hfit hlen with hrun | hrun
  · unfold evmRun
    rw [runForsCalldata_encode_unfold, hrun]
    rfl
  · unfold evmRun
    rw [runForsCalldata_encode_unfold, hrun]
    rfl

/-- The reviewed dispatcher transcription and the aligned direct `fun_recover` runner have
    the same observable result for every ABI-representable raw length. -/
theorem dispatcher_routes_to_recover
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw) :
    evmRun raw digest = evmRunRecover raw digest := by
  by_cases hlen : raw.len = SigLen
  · exact evmRun_eq_recover_of_sigLen raw digest hlen
  · rw [evmRun_zero_of_bad_length raw digest hfit hlen,
      evmRunRecover_bad_length raw digest hlen]

end NiceTry.Fors.Bridge
