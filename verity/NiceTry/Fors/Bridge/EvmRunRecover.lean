import NiceTry.Fors.Bridge.ClassA
import NiceTry.Fors.Bridge.EvmRun
import NiceTry.Fors.Bridge.Refinement

/-!
# `fun_recover`-scoped execution

The deployed contract's `recover(bytes,bytes32)` is: a tiny selector dispatcher
(`switch` + ABI bounds-guards) that decodes the calldata and calls
`fun_recover(offset+36, length, calldataload 36)`. **All the cryptographic content
is in `fun_recover`**; the dispatcher is simple boilerplate.

The scoped runner uses exactly the fuel received by `fun_recover` inside
`runForsCalldata ... 100000`. This lets `DispatcherRoute.lean` compare the same
`call` term directly, despite the interpreter's eager five-branch `switch`,
without a fuel-monotonicity assumption.

`fun_recover` exits three ways: `leave` with `var = 0` (length reject), or
`return(0, 0x20)` (`YulHalt`) with `H_return = 0` (forced-zero reject) or
`H_return = addr` (accept). `runForsRecover` decodes all three.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast NiceTry.Fors NiceTry.Fors.Spec

/-- The args the dispatcher passes to `fun_recover`: `(offset+36 = 100, length, digest)`. -/
def forsRecoverArgs (raw : RawSig) (digest : Digest) : List UInt256 :=
  [UInt256.ofNat 100, UInt256.ofNat raw.len, UInt256.ofNat digest]

/-- Fuel received by `fun_recover` inside the full dispatcher run at fuel
    `100000`: 17 interpreter layers are consumed by the dispatcher prefix. -/
def recoverFuel : Nat := 99983

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

end NiceTry.Fors.Bridge
