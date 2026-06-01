import NiceTry.Fors.Bridge.ForsRuntime

/-!
# `evmRun`: run `forsVerifierRuntime` on calldata via the EVMYulLean interpreter

Runs the deployed `ForsVerifier` dispatcher on given calldata (codeOverride supplies
the helper functions; `execTopLevel` can't be used since it hardcodes `.none`),
and reads the 32-byte word returned by the contract's `RETURN` (in `H_return`).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

/-- Run the contract on raw calldata; the returned 32-byte word (the recovered
    address word) if it `RETURN`s, else `none`. -/
def runForsCalldata (cd : ByteArray) (fuel : Nat) : Option UInt256 :=
  let ss : EvmYul.SharedState .Yul :=
    { (Inhabited.default : EvmYul.SharedState .Yul) with
        executionEnv :=
          { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with calldata := cd } }
  match exec fuel forsDispatcher (some forsVerifierRuntime) (.Ok ss Inhabited.default) with
  | .error (.YulHalt s _) => some (.ofNat (fromByteArrayBigEndian s.sharedState.H_return))
  | _ => none

end NiceTry.Fors.Bridge
