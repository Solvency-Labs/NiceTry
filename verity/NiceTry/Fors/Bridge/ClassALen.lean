import NiceTry.Fors.Bridge.ClassA
import NiceTry.Fors.Bridge.EvmRun

/-!
# `h_len` — the bad-length reject obligation (`evmRun = 0` when `raw.len ≠ SigLen`)

The first of the three `Refinement.lean` obligations, discharged against the real
contract. With the fixed ABI calldata (`calldatasize = 2548`), a model length
`raw.len ≠ SigLen` (and `< 2²⁵⁶`) makes the contract return `address(0)` two ways:

* `raw.len > 2448` → a dispatcher guard reverts (`.error .Revert`) → `runForsCalldata`
  returns `none`;
* `raw.len < 2448` → `fun_recover`'s length guard fires → `var := 0; leave` → the
  dispatcher `mstore 0; return`s → `YulHalt` with `H_return = 0`.

## T1 — terminal-state plumbing
The two ways the bad-length paths terminate, lifted to `evmRun = 0`. Built on
`runForsCalldata_encode_unfold` (`ClassA.lean`), which exposes the dispatcher run on
`forsInitialState`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast NiceTry.Fors

variable {raw : RawSig} {digest : Digest}

/-- A `none` run (revert / non-`YulHalt`) ⇒ `evmRun = 0`. -/
theorem evmRun_zero_of_run_none
    (h : runForsCalldata (encodeForsCalldata raw digest) 100000 = none) :
    evmRun raw digest = 0 := by
  unfold evmRun; rw [h]; rfl

/-- A run returning any word that masks to zero ⇒ `evmRun = 0`. -/
theorem evmRun_zero_of_run_some {w : UInt256}
    (h : runForsCalldata (encodeForsCalldata raw digest) 100000 = some w)
    (hw : w.toNat % 2 ^ 160 = 0) :
    evmRun raw digest = 0 := by
  unfold evmRun; rw [h]; simpa using hw

/-- The zero word masks to zero (the `RETURN address(0)` case). -/
theorem ofNat_zero_mask : (UInt256.ofNat 0).toNat % 2 ^ 160 = 0 := by decide

/-- Dispatcher reverts ⇒ `evmRun = 0`. -/
theorem evmRun_zero_of_exec_revert
    (h : exec 100000 forsDispatcher (some forsVerifierRuntime) (forsInitialState raw digest)
          = .error .Revert) :
    evmRun raw digest = 0 := by
  apply evmRun_zero_of_run_none
  rw [runForsCalldata_encode_unfold, h]

/-- Contract `RETURN`s with zero return data ⇒ `evmRun = 0`. -/
theorem evmRun_zero_of_exec_yulhalt_zero {s v}
    (h : exec 100000 forsDispatcher (some forsVerifierRuntime) (forsInitialState raw digest)
          = .error (.YulHalt s v))
    (hret : fromByteArrayBigEndian s.sharedState.H_return = 0) :
    evmRun raw digest = 0 := by
  apply evmRun_zero_of_run_some (w := UInt256.ofNat 0) _ ofNat_zero_mask
  rw [runForsCalldata_encode_unfold, h]; simp [hret]

end NiceTry.Fors.Bridge
