import NiceTry.Fors.Bridge.EvmRunRecover
import NiceTry.Fors.Bridge.TreeEntryFront
import NiceTry.Fors.Proofs.Basic

/-!
# Phase 4 accept branch glue

The successful branch currently needs explicit ABI-representability hypotheses.
`Digest` and `RawSig.read16` are both `Nat` at the model layer, while the EVM
path observes `UInt256.ofNat` encodings. The theorems here therefore expose the
strongest checked glue available without silently changing that model domain.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors
open NiceTry.Fors.Proofs.Basic

set_option maxHeartbeats 2000000

/-- The hmsg word computed by `fun_recover` is the model `dValOf`, provided all
    raw signature chunks and the digest are ABI-representable. -/
theorem recoverHmsgDVal_toNat_eq_dValOf
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest) :
    (recoverHmsgDVal raw digest).toNat = dValOf raw digest := by
  unfold DigestFitsEvmWord at hdigest
  rw [recoverHmsgDVal_toNat]
  rw [recoverHmsgPkWord_toNat_of_wellFormed raw digest hwf]
  rw [recoverHmsgRWord_toNat_of_wellFormed raw digest hwf]
  rw [recoverHmsgDigestWord_toNat_of_lt raw digest hdigest]
  rw [recoverHmsgCounterWord_toNat_of_wellFormed raw digest hwf]
  rfl

/-- Model forced-zero implies the exact UInt256 guard value consumed by the
    pre-loop trace. -/
theorem recoverHmsg_guard_eq_zero_of_forcedZero
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
      (UInt256.ofNat 31) = (⟨0⟩ : UInt256) := by
  have hdv := recoverHmsgDVal_toNat_eq_dValOf raw digest hwf hdigest
  have hshape := forcedZero_eq_evm_shape (dValOf raw digest)
  rw [hfz] at hshape
  have hmod : (dValOf raw digest / 2 ^ 125) % 32 = 0 := by
    simpa [evmOmittedIndexShape] using hshape
  apply uint256_eq_of_toNat
  rw [uint256_land_toNat]
  rw [uint256_shiftRight_toNat _ _ (by
    rw [show (UInt256.ofNat 125).toNat = 125 from uint256_ofNat_toNat_of_lt _ (by decide)]
    decide)]
  rw [hdv]
  rw [show (UInt256.ofNat 125).toNat = 125 from uint256_ofNat_toNat_of_lt _ (by decide)]
  rw [show (UInt256.ofNat 31).toNat = 31 from uint256_ofNat_toNat_of_lt _ (by decide)]
  rw [show ((⟨0⟩ : UInt256).toNat) = 0 from rfl]
  rw [Nat.shiftRight_eq_div_pow]
  rw [show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact hmod

/-- The loop's closed-form root value is the corresponding typed model tree. -/
theorem loopRootV_eq_reconstructTree_of_wellFormed
    (raw : RawSig) (digest : Digest) (T : EvmYul.State .Yul)
    (pk : UInt256) (dVal : Word) (j : Nat) (hj : j < 25)
    (hcd : T.executionEnv.calldata = encodeForsCalldata raw digest)
    (hwf : RawSigWellFormed raw)
    (hpk : pk.toNat = (decodeTyped raw).pkSeed) :
    loopRootV pk T dVal 132 j =
      reconstructTree (decodeTyped raw).pkSeed ⟨j, by simpa [RealTrees] using hj⟩
        (indexAt dVal j)
        ((decodeTyped raw).openings ⟨j, by simpa [RealTrees] using hj⟩) := by
  unfold loopRootV reconstructTree
  rw [hpk]
  rw [loopSk_read16 raw digest T j hj hcd hwf]
  rw [show loopSib T 132 j 16 = loopSib T 132 j (16 * 1) by rfl]
  rw [loopSib_read16 raw digest T j 1 hj ⟨by omega, by omega⟩ hcd hwf]
  rw [show loopSib T 132 j 32 = loopSib T 132 j (16 * 2) by rfl]
  rw [loopSib_read16 raw digest T j 2 hj ⟨by omega, by omega⟩ hcd hwf]
  rw [show loopSib T 132 j 48 = loopSib T 132 j (16 * 3) by rfl]
  rw [loopSib_read16 raw digest T j 3 hj ⟨by omega, by omega⟩ hcd hwf]
  rw [show loopSib T 132 j 64 = loopSib T 132 j (16 * 4) by rfl]
  rw [loopSib_read16 raw digest T j 4 hj ⟨by omega, by omega⟩ hcd hwf]
  rw [show loopSib T 132 j 80 = loopSib T 132 j (16 * 5) by rfl]
  rw [loopSib_read16 raw digest T j 5 hj ⟨by omega, by omega⟩ hcd hwf]
  simp [decodeTyped, decodeOpening, readHash16, treeOffset, authOffset, SectionOffset,
    PkSeedOffset, ROffset, TreeLen, RLen, PkSeedLen, A]
  ring_nf

/-- A loop result expressed with `loopRootV` compresses to the typed recovery root. -/
theorem compressRoots_loop_roots_eq_recoverRoot_of_wellFormed
    (raw : RawSig) (digest : Digest) (T : EvmYul.State .Yul)
    (pk : UInt256) (dVal : Word) (rootsW : Nat → UInt256)
    (hcd : T.executionEnv.calldata = encodeForsCalldata raw digest)
    (hwf : RawSigWellFormed raw)
    (hpk : pk.toNat = (decodeTyped raw).pkSeed)
    (hroots : ∀ j, j < 25 → (rootsW j).toNat = loopRootV pk T dVal 132 j) :
    compressRoots pk.toNat (fun i : TreeIndex => (rootsW i.val).toNat) =
      recoverRoot (decodeTyped raw) dVal := by
  exact compressRoots_eq_recoverRoot_of_model_roots (decodeTyped raw) dVal pk
    (fun i : TreeIndex => rootsW i.val) hpk (by
      intro tree
      rw [hroots tree.val tree.isLt]
      exact loopRootV_eq_reconstructTree_of_wellFormed raw digest T pk dVal
        tree.val tree.isLt hcd hwf hpk)

/-- Checked accept-path composition through the 25-tree loop. This stops exactly
    before `body.drop 33` (roots compression/address return), carrying the model
    root handoff needed by that suffix. -/
theorem exec_accept_loop_roots_from_hmsg_prefix
    (raw : RawSig) (digest : Digest) (co : Option YulContract) (n : Nat)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    ∃ (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore)
      (ssf : SharedState .Yul) (vsf : EvmYul.Yul.VarStore)
      (rootsW : Nat → UInt256),
      exec (n + 136) (.Block (forsFunRecover.body.drop 18)) co
          (recoverAfterRet3FromRet2 raw digest)
        = exec (n + 121) (.Block (forsFunRecover.body.drop 33)) co (.Ok ssf vsf)
      ∧ LoopInv
          (loopEntryState ss vs (recoverHmsgPkWord raw digest)
            (recoverHmsgDVal raw digest)).toState
          (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest).toNat 132 25
          (.Ok ssf vsf)
      ∧ (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract 0 32 =
          (recoverHmsgPkWord raw digest).toByteArray.data
      ∧ (∀ j, j < 25 →
          (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.data.extract
            (0x40 + 32 * j) (0x40 + 32 * j + 32) = (rootsW j).toByteArray.data
          ∧ (rootsW j).toNat =
              loopRootV (recoverHmsgPkWord raw digest)
                (loopEntryState ss vs (recoverHmsgPkWord raw digest)
                  (recoverHmsgDVal raw digest)).toState
                (dValOf raw digest) 132 j)
      ∧ compressRoots (recoverHmsgPkWord raw digest).toNat
          (fun i : TreeIndex => (rootsW i.val).toNat) =
          recoverRoot (decodeTyped raw) (dValOf raw digest) := by
  have hfzGuard := recoverHmsg_guard_eq_zero_of_forcedZero raw digest hwf hdigest hfz
  obtain ⟨ss, vs, hs⟩ := recoverAfterHmsg_ok raw digest
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
  have hpkLookup : EvmYul.Yul.State.lookup! "usr_pkSeed" (.Ok ss vs) =
      recoverHmsgPkWord raw digest := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_pkSeed raw digest
  have hmem : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size = 0xa0 := by
    rw [← hs]
    exact recoverAfterHmsg_memory_size raw digest
  obtain ⟨htail, hinv⟩ := exec_recover_tail_to_loopInv ss vs co
    (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest) (n + 99)
    hret hret2 hoff hdv hpkLookup hmem hfzGuard
  have hpre :
      exec (n + 136) (.Block (forsFunRecover.body.drop 18)) co
          (recoverAfterRet3FromRet2 raw digest)
        = exec (n + 122) (.Block (forsFunRecover.body.drop 32)) co
            (loopEntryState ss vs (recoverHmsgPkWord raw digest)
              (recoverHmsgDVal raw digest)) := by
    rw [show n + 136 = (n + 99) + 37 by omega]
    rw [exec_recover_hmsg_named raw digest co (n + 99), hs]
    exact htail
  rw [loopEntryState_ok] at hinv
  obtain ⟨ssf, vsf, rootsW, hloop, hinvf, hlow, hroots⟩ :=
    tree_loop_run_from_zero
      (loopEntryState ss vs (recoverHmsgPkWord raw digest)
        (recoverHmsgDVal raw digest)).toState
      (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest).toNat 132
      co _ _ hinv n
  refine ⟨ss, vs, ssf, vsf, rootsW, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpre]
    rw [show n + 122 = n + 121 + 1 by omega]
    rw [show forsFunRecover.body.drop 32 =
        (.For forsTreeCond forsTreePost forsTreeBody) :: forsFunRecover.body.drop 33 from rfl]
    rw [loopEntryState_ok]
    exact exec_block_cons_ok (n := n + 121) (co := co)
      hloop
  · simpa [loopEntryState_ok] using hinvf
  · rw [hlow 0 32 (by omega)]
    change ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore
      (UInt256.ofNat 0x380) (recoverHmsgPkWord raw digest)).memory.data.extract 0 32 =
        (recoverHmsgPkWord raw digest).toByteArray.data
    have hpad : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size ≤
        (UInt256.ofNat 0x380).toNat := by
      rw [← hs, recoverAfterHmsg_memory_size]
      decide
    rw [mstore_pad_extract_below _ _ _ _ _ hpad (by omega)]
    rw [← hs]
    exact recoverAfterHmsg_pk_extract raw digest
  · intro j hj
    obtain ⟨hslot, hval⟩ := hroots j hj
    refine ⟨hslot, ?_⟩
    rw [hval]
    rw [recoverHmsgDVal_toNat_eq_dValOf raw digest hwf hdigest]
  · have hpk := recoverHmsgPkWord_toNat_of_wellFormed raw digest hwf
    have hcd :
        (loopEntryState ss vs (recoverHmsgPkWord raw digest)
          (recoverHmsgDVal raw digest)).toState.executionEnv.calldata =
          encodeForsCalldata raw digest := by
      change (EvmYul.Yul.State.Ok ss vs).toState.executionEnv.calldata =
        encodeForsCalldata raw digest
      rw [← hs]
      rfl
    apply compressRoots_loop_roots_eq_recoverRoot_of_wellFormed
      raw digest
      (loopEntryState ss vs (recoverHmsgPkWord raw digest)
        (recoverHmsgDVal raw digest)).toState
      (recoverHmsgPkWord raw digest) (dValOf raw digest) rootsW hcd hwf hpk
    intro j hj
    exact (hroots j hj).2.trans
      (by rw [recoverHmsgDVal_toNat_eq_dValOf raw digest hwf hdigest])

/-- The setup prefix of `fun_recover`, through the good-length guard. -/
theorem exec_recover_good_prefix_to_hmsg
    (raw : RawSig) (digest : Digest) (n : Nat) (hlen : raw.len = SigLen) :
    exec (n + 47) (.Block forsFunRecover.body) (some forsVerifierRuntime)
        (recoverEntryState raw digest) =
      exec (n + 29) (.Block (forsFunRecover.body.drop 18))
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
    exec (n + 29) (.Block (forsFunRecover.body.drop 18))
      (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest)
  rw [show forsFunRecover.body.drop 1 =
      (.Let ["expr"] (.some (.Call (Sum.inr "constant_FORS_SIG_LEN") []))) ::
        forsFunRecover.body.drop 2 from rfl]
  rw [exec_block_cons_ok (n := n + 45)
    (h := exec_recover_let_expr_const (base := n + 2) raw digest)]
  rw [exec_recover_ret_init_after_expr (base := n) raw digest]
  rw [exec_recover_prefix_to_ret1_product (base := n) raw digest]
  exact exec_recover_through_length_guard (base := n) raw digest hlen

/-- Successful execution from the hmsg prefix through the final return. -/
theorem exec_accept_from_hmsg_prefix
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 136) (.Block (forsFunRecover.body.drop 18))
          (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return =
          addressFromRoot (decodeTyped raw).pkSeed
            (recoverRoot (decodeTyped raw) (dValOf raw digest))
      ∧ addressFromRoot (decodeTyped raw).pkSeed
          (recoverRoot (decodeTyped raw) (dValOf raw digest)) < 2 ^ 160 := by
  obtain ⟨ss, vs, ssf, vsf, rootsW, hloop, hinv, hpk0, hslots, hcompress⟩ :=
    exec_accept_loop_roots_from_hmsg_prefix raw digest
      (some forsVerifierRuntime) n hwf hdigest hfz
  have hsize : 0x400 ≤
      (EvmYul.Yul.State.Ok ssf vsf).toMachineState.memory.size := by
    rcases hinv.size400 with hzero | hsize
    · omega
    · exact hsize
  obtain ⟨S, hpost, hvalue, hbound⟩ :=
    post_loop_trace (n + 103) (some forsVerifierRuntime) ssf vsf
      (recoverHmsgPkWord raw digest) rootsW hinv.ret hpk0
      (fun j hj => (hslots j hj).1) hsize
  refine ⟨S, hloop.trans ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpost
  · rw [hvalue, hcompress,
      recoverHmsgPkWord_toNat_of_wellFormed raw digest hwf]
  · rw [hcompress,
      recoverHmsgPkWord_toNat_of_wellFormed raw digest hwf] at hbound
    exact hbound

/-- Successful execution of the complete `fun_recover` body. -/
theorem exec_accept_body
    (raw : RawSig) (digest : Digest) (n : Nat)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 154) (.Block forsFunRecover.body) (some forsVerifierRuntime)
          (recoverEntryState raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return =
          addressFromRoot (decodeTyped raw).pkSeed
            (recoverRoot (decodeTyped raw) (dValOf raw digest))
      ∧ addressFromRoot (decodeTyped raw).pkSeed
          (recoverRoot (decodeTyped raw) (dValOf raw digest)) < 2 ^ 160 := by
  obtain ⟨S, hsuffix, hvalue, hbound⟩ :=
    exec_accept_from_hmsg_prefix raw digest n hwf hdigest hfz
  refine ⟨S, ?_, hvalue, hbound⟩
  rw [show n + 154 = (n + 107) + 47 by omega,
    exec_recover_good_prefix_to_hmsg raw digest (n + 107) hlen]
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsuffix

/-- The checked accept trace entered through the actual scoped function call. -/
theorem call_accept
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    ∃ S : EvmYul.Yul.State,
      call recoverFuel (forsRecoverArgs raw digest) (some "fun_recover")
          (some forsVerifierRuntime) (dispatcherBeforeRecoverState raw digest)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return =
          addressFromRoot (decodeTyped raw).pkSeed
            (recoverRoot (decodeTyped raw) (dValOf raw digest))
      ∧ addressFromRoot (decodeTyped raw).pkSeed
          (recoverRoot (decodeTyped raw) (dValOf raw digest)) < 2 ^ 160 := by
  obtain ⟨S, hbody, hvalue, hbound⟩ :=
    exec_accept_body raw digest 0 hlen hwf hdigest hfz
  refine ⟨S, ?_, hvalue, hbound⟩
  unfold recoverFuel
  apply call_err
    (dispatcherBeforeRecoverState_account_find raw digest)
    (by simpa using forsVerifierRuntime_lookup_fun_recover)
  simpa [recoverEntryState, recoverGoodArgs, forsRecoverArgs] using hbody

/-- The scoped executable returns the model address on the accept branch. -/
theorem evmRunRecover_accept
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    evmRunRecover raw digest =
      addressFromRoot (decodeTyped raw).pkSeed
        (recoverRoot (decodeTyped raw) (dValOf raw digest)) := by
  obtain ⟨S, hcall, hvalue, hbound⟩ :=
    call_accept raw digest hlen hwf hdigest hfz
  unfold evmRunRecover
  rw [if_pos hlen]
  unfold runForsRecover
  rw [hcall]
  simp only [Option.map_some, Option.getD_some]
  rw [hvalue, uint256_ofNat_toNat_of_lt _ (lt_trans hbound (by decide)),
    Nat.mod_eq_of_lt hbound]

end NiceTry.Fors.Bridge
