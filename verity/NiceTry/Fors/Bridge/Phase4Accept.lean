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

/-- ABI-representable bytes32 digest values. -/
def DigestFitsEvmWord (digest : Digest) : Prop :=
  digest < UInt256.size

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
  obtain ⟨ssf, vsf, rootsW, hloop, hinvf, _hlow, hroots⟩ :=
    tree_loop_run_from_zero
      (loopEntryState ss vs (recoverHmsgPkWord raw digest)
        (recoverHmsgDVal raw digest)).toState
      (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest).toNat 132
      co _ _ hinv n
  refine ⟨ss, vs, ssf, vsf, rootsW, ?_, ?_, ?_, ?_⟩
  · rw [hpre]
    rw [show n + 122 = n + 121 + 1 by omega]
    rw [show forsFunRecover.body.drop 32 =
        (.For forsTreeCond forsTreePost forsTreeBody) :: forsFunRecover.body.drop 33 from rfl]
    rw [loopEntryState_ok]
    exact exec_block_cons_ok (n := n + 121) (co := co)
      hloop
  · simpa [loopEntryState_ok] using hinvf
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

end NiceTry.Fors.Bridge
