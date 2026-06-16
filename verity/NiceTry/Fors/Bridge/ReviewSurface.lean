import NiceTry.Fors.Bridge.ParsedRuntime
import NiceTry.Fors.Proofs.Basic

/-!
# Reviewer-facing theorem surface

This module contains the small set of statements a reviewer should read first.
The proofs are deliberately thin wrappers around the detailed proof modules:

1. the pinned optimized-Yul artifact parses to the checked EVMYulLean runtime;
2. the checked runtime returns the same address as the FORS+C recovery model;
3. the two facts compose without an existential hiding the reviewed runtime;
4. a legitimate FORS+C signature recovers the expected address in the model.

The long files under `Bridge/` prove the execution details. This file is the
human review surface.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors
open NiceTry.Fors.Spec
open NiceTry.Fors.Proofs.Basic

/-- The verifier's public failure convention: model `none` is returned on-chain
as `address(0)`. -/
def recoverOrZero (raw : RawSig) (digest : Digest) : Address :=
  (recoverRaw? raw digest).getD 0

/-- The tracked optimized-Yul artifact parses to exactly the runtime used by the
execution proof. -/
theorem pinned_yul_is_checked_runtime :
    YulParser.parseDeployedRuntime pinnedForsOptimizedYul =
      .ok forsVerifierRuntime :=
  parse_pinned_fors_runtime

/-- Running the checked EVMYulLean runtime agrees with the clean FORS+C recovery
model on every ABI-representable input. -/
theorem checked_runtime_matches_recover_model :
    ∀ raw digest, ForsAbiInput raw digest →
      evmRun raw digest = recoverOrZero raw digest := by
  intro raw digest habi
  simpa [recoverOrZero] using phase4_forsRefines raw digest habi

/-- No-existential reviewer theorem: the pinned artifact parses to the reviewed
runtime, and that runtime agrees with the clean FORS+C recovery model. -/
theorem pinned_yul_runtime_matches_recover_model :
    YulParser.parseDeployedRuntime pinnedForsOptimizedYul =
        .ok forsVerifierRuntime ∧
      ∀ raw digest, ForsAbiInput raw digest →
        evmRunWithRuntime forsVerifierRuntime raw digest =
          recoverOrZero raw digest := by
  constructor
  · exact pinned_yul_is_checked_runtime
  · intro raw digest habi
    simpa [recoverOrZero] using
      forsVerifierRuntime_refines raw digest habi

/-- Model sanity theorem: a legitimate raw FORS+C signature recovers the expected
address. -/
theorem legitimate_fors_signature_recovers_expected_address
    (raw : RawSig) (digest : Digest) (pkRoot : Hash16)
    (h : RawLegitSignatureFor raw digest pkRoot) :
    ∃ sig : TypedSig,
      decodeRaw raw = some sig ∧
        recoverOrZero raw digest =
          addressFromRoot sig.pkSeed pkRoot := by
  obtain ⟨sig, hlen, hdecode, hlegit⟩ := h
  refine ⟨sig, hdecode, ?_⟩
  have hrec :
      recoverRaw? raw digest =
        some (addressFromRoot sig.pkSeed pkRoot) :=
    legit_raw_signature_recovers_expected_address
      raw digest sig pkRoot hlen hdecode hlegit
  simp [recoverOrZero, hrec]

end NiceTry.Fors.Bridge
