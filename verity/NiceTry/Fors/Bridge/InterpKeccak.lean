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

end NiceTry.Fors.Bridge
