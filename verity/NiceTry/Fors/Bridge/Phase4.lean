import NiceTry.Fors.Bridge.DispatcherRoute

/-!
# Phase 4: FORS verifier runtime refinement

This module assembles the checked dispatcher and recovery execution traces into
the runtime-transcription refinement theorem. The selector/ABI route, reject
branches, 25-tree loop, roots compression, and final address return are proved.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors

/-- The deployed observable returns zero for malformed signature lengths. -/
theorem evmRun_bad_length
    (raw : RawSig) (digest : Digest)
    (hfit : RawSigLenFitsEvmWord raw)
    (hlen : raw.len ≠ SigLen) :
    evmRun raw digest = 0 := by
  rw [dispatcher_routes_to_recover raw digest hfit]
  exact evmRunRecover_bad_length raw digest hlen

/-- The deployed observable returns zero when the grinding guard rejects. -/
theorem evmRun_forced_zero_reject
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = false) :
    evmRun raw digest = 0 := by
  rw [evmRun_eq_recover_of_sigLen raw digest hlen]
  exact evmRunRecover_forced_zero_reject raw digest hlen hwf hdigest hfz

/-- The deployed observable returns the model recovery address on acceptance. -/
theorem evmRun_accept
    (raw : RawSig) (digest : Digest)
    (hlen : raw.len = SigLen)
    (hwf : RawSigWellFormed raw)
    (hdigest : DigestFitsEvmWord digest)
    (hfz : forcedZero (dValOf raw digest) = true) :
    evmRun raw digest =
      addressFromRoot (decodeTyped raw).pkSeed
        (recoverRoot (decodeTyped raw) (dValOf raw digest)) := by
  rw [evmRun_eq_recover_of_sigLen raw digest hlen]
  exact evmRunRecover_accept raw digest hlen hwf hdigest hfz

/-- **Phase 4 complete.** The reviewed optimized-IR runtime transcription
    refines the Lean recovery model on the exact ABI-representable input domain. -/
theorem phase4_forsRefines : ForsRefines :=
  forsRefines_of_branches evmRun_bad_length
    evmRun_forced_zero_reject evmRun_accept

end NiceTry.Fors.Bridge
