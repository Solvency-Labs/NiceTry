import NiceTry.Fors.Bridge.ForsYulArtifact
import NiceTry.Fors.Bridge.Phase4

/-!
# Refinement of the runtime parsed from pinned optimized Yul

`forsVerifierRuntime` remains the stable scaffold used by the execution proof.
`parse_pinned_fors_runtime` now certifies that this scaffold is exactly the
runtime imported from the tracked `solc` optimized-Yul artifact.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

def runForsCalldataWithRuntime
    (runtime : YulContract) (cd : ByteArray) (fuel : Nat) : Option UInt256 :=
  let ee : EvmYul.ExecutionEnv .Yul :=
    { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with calldata := cd }
  let ss : EvmYul.SharedState .Yul :=
    { (Inhabited.default : EvmYul.SharedState .Yul) with
        executionEnv := ee
        accountMap :=
          (Inhabited.default : EvmYul.SharedState .Yul).accountMap.insert
            ee.codeOwner
            { (Inhabited.default : EvmYul.Account .Yul) with code := runtime } }
  match exec fuel runtime.dispatcher (some runtime)
      (.Ok ss Inhabited.default) with
  | .error (.YulHalt s _) =>
      some (.ofNat (fromByteArrayBigEndian s.sharedState.H_return))
  | _ => none

def evmRunWithRuntime
    (runtime : YulContract) (raw : RawSig) (digest : Digest) : Address :=
  ((runForsCalldataWithRuntime runtime
      (encodeForsCalldata raw digest) 100000).map
    (fun word => word.toNat % 2 ^ 160)).getD 0

def ForsRuntimeRefines (runtime : YulContract) : Prop :=
  ∀ (raw : RawSig) (digest : Digest), ForsAbiInput raw digest →
    evmRunWithRuntime runtime raw digest =
      (recoverRaw? raw digest).getD 0

theorem forsVerifierRuntime_refines :
    ForsRuntimeRefines forsVerifierRuntime := by
  simpa [ForsRuntimeRefines, evmRunWithRuntime,
    runForsCalldataWithRuntime, ForsRefines, evmRun, runForsCalldata,
    forsVerifierRuntime] using phase4_forsRefines

theorem pinned_optimized_yul_refines :
    ∃ runtime,
      YulParser.parseDeployedRuntime pinnedForsOptimizedYul = .ok runtime ∧
      ForsRuntimeRefines runtime :=
  ⟨forsVerifierRuntime, parse_pinned_fors_runtime,
    forsVerifierRuntime_refines⟩

end NiceTry.Fors.Bridge
