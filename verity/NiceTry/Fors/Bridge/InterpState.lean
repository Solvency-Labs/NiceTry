import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp

/-!
# Builtin (`primCall`) step lemmas — stateful ops (WS-1 brick 2)

The contract's *stateful* opcodes, reduced through EVMYulLean's `step`:

* **Reads (state-preserving):** `calldataload` (via `unaryStateOp`, which rebuilds
  the state to an `=`-state — discharged by `cases s <;> rfl`), and the environment
  ops `callvalue` / `calldatasize` (via `executionEnvOp`, state kept verbatim).
* **Memory write:** `mstore` — result threads `s.setMachineState (s.toMachineState.mstore a b)`,
  no return value (`none`).
* **Hash (symbolic):** `keccak256` — returns `(val, mState')` from `MachineState.keccak256`;
  the digest stays opaque (`ffi.KEC`), connecting to the `evm_keccak_*` axioms in
  `AddressShape.lean`.
* **Halts:** `return` ⇒ `.error (.YulHalt s' ⟨1⟩)` (return data in the threaded
  machine state's `H_return`), `revert` ⇒ `.error .Revert`. In `runForsCalldata`
  these are the two reject/return exits (`YulHalt` → `some`, `Revert`/other → `none`).

Same recipe as the pure ops (`InterpOps.lean`): `unfold primCall; simp [<step OP>]`
with the inner `step` equation `unfold step; rfl` (or `unfold step; cases s <;> rfl`
when the op rebuilds the state record).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 1000000

variable {n : Nat} (s : EvmYul.Yul.State) (a b off : UInt256)

/-- `calldataload(off)` reads a 32-byte word from calldata; state preserved. -/
theorem primCall_calldataload :
    primCall (n+1) s .CALLDATALOAD [off] = .ok (s, [EvmYul.State.calldataload s.toState off]) := by
  have hstep : step (τ := .Yul) Operation.CALLDATALOAD .none s [off]
      = .ok (s, some (EvmYul.State.calldataload s.toState off)) := by
    unfold step; cases s <;> rfl
  unfold primCall; simp [hstep]

/-- `callvalue()` reads the call's wei value; state preserved. -/
theorem primCall_callvalue :
    primCall (n+1) s .CALLVALUE [] = .ok (s, [s.executionEnv.weiValue]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.CALLVALUE .none s []
          = .ok (s, some s.executionEnv.weiValue) from by unfold step; rfl]

/-- `calldatasize()` reads the calldata length; state preserved. -/
theorem primCall_calldatasize :
    primCall (n+1) s .CALLDATASIZE [] = .ok (s, [UInt256.ofNat s.executionEnv.calldata.size]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.CALLDATASIZE .none s []
          = .ok (s, some (UInt256.ofNat s.executionEnv.calldata.size)) from by unfold step; rfl]

/-- `mstore(a, b)` writes word `b` at memory offset `a`; no return value. -/
theorem primCall_mstore :
    primCall (n+1) s .MSTORE [a, b]
      = .ok (s.setMachineState (s.toMachineState.mstore a b), []) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.MSTORE .none s [a, b]
          = .ok (s.setMachineState (s.toMachineState.mstore a b), none) from by unfold step; rfl]

/-- `keccak256(a, b)` hashes the memory window; digest stays opaque (`ffi.KEC`). -/
theorem primCall_keccak256 :
    primCall (n+1) s .KECCAK256 [a, b]
      = .ok (s.setMachineState (s.toMachineState.keccak256 a b).2,
             [(s.toMachineState.keccak256 a b).1]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.KECCAK256 .none s [a, b]
          = .ok (s.setMachineState (s.toMachineState.keccak256 a b).2,
                 some (s.toMachineState.keccak256 a b).1) from by unfold step; rfl]

/-- `return(a, b)` halts with the return window copied into `H_return`. In
    `runForsCalldata` this is the `YulHalt` exit that yields `some <returned word>`. -/
theorem primCall_return :
    primCall (n+1) s .RETURN [a, b]
      = .error (.YulHalt (s.setMachineState (s.toMachineState.evmReturn a b)) ⟨1⟩) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.RETURN .none s [a, b]
          = .error (.YulHalt (s.setMachineState (s.toMachineState.evmReturn a b)) ⟨1⟩) from by
    unfold step; rfl]

/-- `revert(a, b)` aborts. In `runForsCalldata` this is the non-`YulHalt` exit that
    yields `none` (decoded as `address(0)`). -/
theorem primCall_revert :
    primCall (n+1) s .REVERT [a, b] = .error .Revert := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.REVERT .none s [a, b] = .error .Revert from by
    unfold step; rfl]

end NiceTry.Fors.Bridge
