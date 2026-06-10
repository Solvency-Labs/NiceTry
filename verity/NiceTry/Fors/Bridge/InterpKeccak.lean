import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.InterpState

/-!
# Keccak execution → `AddressShape` bridge (WS-2 hash wiring)

Every hash in `fun_recover` (leaf, 5 nodes/iteration, roots, hmsg, address) is a
`keccak256(off,len)`. The interpreter computes it via `MachineState.keccak256`, which
is *exactly* `UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memory.readWithPadding
off len)))` — the form the proved `AddressShape` shape lemmas
(`leaf_derivation_eq_*`, `node_derivation_eq_climbLevel_*`, …) consume.

These bridges connect the interpreter's keccak result to that form, and record that
keccak leaves `memory` unchanged (it only bumps `activeWords`). They are the per-hash
glue the per-iteration loop-body trace uses.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

/-- The interpreter's keccak value = `ffi.KEC` of the memory window (the `AddressShape`
    form). -/
theorem keccak256_value (m : MachineState) (mstart sz : UInt256) :
    (m.keccak256 mstart sz).1
      = UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC (m.memory.readWithPadding mstart.toNat sz.toNat))) := by
  unfold MachineState.keccak256; rfl

/-- Keccak only touches `activeWords`, not `memory`. -/
theorem keccak256_memory (m : MachineState) (mstart sz : UInt256) :
    (m.keccak256 mstart sz).2.memory = m.memory := by
  unfold MachineState.keccak256; rfl

/-! ## Memory bridge — interpreter `mstore` ↔ the `MachineState` `AddressShape` uses

The loop body runs on an `.Ok` state; `setMachineState`/`mstore` thread through it so
the `toMachineState` after a `mstore(a,v)` sequence is exactly the chained
`MachineState.mstore` the `AddressShape` shape lemmas take as input. -/

theorem setMachineState_toMachineState_ok (ss : SharedState .Yul) (vs : VarStore) (m : MachineState) :
    ((EvmYul.Yul.State.Ok ss vs).setMachineState m).toMachineState = m := rfl

/-- Running `mstore(a,v)` (via `primCall_mstore`) on an `.Ok` state leaves a machine
    state that is exactly the `AddressShape`-form `mstore`. -/
theorem mstore_run_toMachineState_ok (ss : SharedState .Yul) (vs : VarStore) (a v : UInt256) :
    (((EvmYul.Yul.State.Ok ss vs).setMachineState
        ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore a v)).toMachineState)
      = (EvmYul.Yul.State.Ok ss vs).toMachineState.mstore a v := rfl

end NiceTry.Fors.Bridge
