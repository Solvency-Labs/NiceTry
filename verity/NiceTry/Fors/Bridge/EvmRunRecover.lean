import NiceTry.Fors.Bridge.ClassA
import NiceTry.Fors.Bridge.EvmRun
import NiceTry.Fors.Bridge.Refinement

/-!
# `fun_recover`-scoped execution (skips the dispatcher's eager `switch`)

The deployed contract's `recover(bytes,bytes32)` is: a tiny selector dispatcher
(`switch` + ABI bounds-guards) that decodes the calldata and calls
`fun_recover(offset+36, length, calldataload 36)`. **All the cryptographic content
is in `fun_recover`**; the dispatcher is simple boilerplate.

Verifying `fun_recover` directly (this file) avoids the dispatcher's *eager 5-branch
`switch`* (every case body run + `foldr`-select) and the fuel-monotonicity it would
require (including the research-grade `execSwitchCases` non-monotonicity — see
`FuelMono.lean`). We take the dispatcher's correctness as **one explicit, auditable,
dischargeable assumption** (`dispatcher_routes_to_recover`) and point the proof
effort at the FORS recovery logic — where the value is.

`fun_recover` exits three ways: `leave` with `var = 0` (length reject), or
`return(0, 0x20)` (`YulHalt`) with `H_return = 0` (forced-zero reject) or
`H_return = addr` (accept). `runForsRecover` decodes all three.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast NiceTry.Fors NiceTry.Fors.Spec

/-- The args the dispatcher passes to `fun_recover`: `(offset+36 = 100, length, digest)`. -/
def forsRecoverArgs (raw : RawSig) (digest : Digest) : List UInt256 :=
  [UInt256.ofNat 100, UInt256.ofNat raw.len, UInt256.ofNat digest]

/-- Exact fuel budget used by the scoped recover proof. -/
def recoverFuel : Nat := 155

/-- Run `fun_recover` directly on the encoded calldata, decoding its three exits. -/
def runForsRecover (raw : RawSig) (digest : Digest) (fuel : Nat) : Option UInt256 :=
  match call fuel (forsRecoverArgs raw digest) (some "fun_recover") (some forsVerifierRuntime)
              (dispatcherBeforeRecoverState raw digest) with
  | .error (.YulHalt s _) => some (.ofNat (fromByteArrayBigEndian s.sharedState.H_return))
  | .ok (_, rets) => some (rets.headD ⟨0⟩)
  | _ => none

/-- `fun_recover`'s observable behaviour as `Address` (low-160 of the result word).
    The malformed-length exit is normalized before interpreting the function body;
    its exact EVM-word guard and `leave` body are proved in `Phase4Reject`. -/
def evmRunRecover (raw : RawSig) (digest : Digest) : Address :=
  if raw.len = SigLen then
    ((runForsRecover raw digest recoverFuel).map (fun w => w.toNat % 2 ^ 160)).getD 0
  else
    0

/-! ## The dispatcher-routing assumption (the one explicit trust item)

The selector dispatcher, on valid `recover(bytes,bytes32)` calldata, decodes
`offset = 0x40`, `length = raw.len`, `digest`, passes the ABI bounds-guards, and
calls `fun_recover(100, raw.len, digest)` — returning exactly its result (and, on the
revert paths for `raw.len > 2448`, `address(0)`, which equals `fun_recover`'s
length-reject `0`). So the full contract and the `fun_recover`-scoped run agree on
**representable inputs**.

This is **boilerplate routing**, not crypto — `NOT` a hardness assumption. It is
**dischargeable**: prove the dispatcher trace (the eager-`switch` composition, or the
fuel-monotonicity route) to turn this `axiom` into a `theorem`. Until then it is the
single named gap between `ForsRefines` (the full contract) and the `fun_recover`
correctness proved here. Tracked in `PICKUP.md` / `TRUST_SURFACE`. -/
axiom dispatcher_routes_to_recover (raw : RawSig) (digest : Digest) :
    RawSigLenFitsEvmWord raw → evmRun raw digest = evmRunRecover raw digest

/-! ## Bridge: `evmRun` branch facts from the `fun_recover`-scoped ones

These let the (tractable) `evmRunRecover` reject/accept proofs feed the already-proved
spine `forsRefines_of_branches` (which is stated over `evmRun`). The forced-zero and
accept branches carry `raw.len = SigLen`, which gives `RawSigLenFitsEvmWord` for free. -/

theorem sigLen_lt_uInt256_size : SigLen < EvmYul.UInt256.size := by decide

theorem evmRun_eq_recover_of_sigLen (raw : RawSig) (digest : Digest) (hlen : raw.len = SigLen) :
    evmRun raw digest = evmRunRecover raw digest := by
  apply dispatcher_routes_to_recover
  show raw.len < EvmYul.UInt256.size
  rw [hlen]; exact sigLen_lt_uInt256_size

end NiceTry.Fors.Bridge
