import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.InterpState
import NiceTry.Fors.TreeKeccak

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

/-! ## Masking reconciliation — the contract's `and(_, not 0xff..)` ↔ the model's `&&& NMaskWord`

Each hash in `fun_recover` is `and(keccak256(off,len), not(0xff…ff))`, i.e.
`UInt256.land` against `not(2¹²⁸-1) = NMaskWord`. The shape lemmas conclude in terms
of the model's `Nat`-level `_ &&& NMaskWord`. These bridge the two: on a hashed word
(`< 2²⁵⁶`), the masked UInt256's `.toNat` is exactly the model's masked `Nat`. -/

theorem size_pos : (0 : ℕ) < EvmYul.UInt256.size := Nat.pos_of_ne_zero (NeZero.ne _)

theorem uint256_ofNat_land_toNat (a b : Nat) :
    ((UInt256.ofNat a).land (UInt256.ofNat b)).toNat
      = (a % EvmYul.UInt256.size) &&& (b % EvmYul.UInt256.size) := by
  show (Fin.land (UInt256.ofNat a).val (UInt256.ofNat b).val).val = _
  rw [Fin.land]
  simp only [UInt256.ofNat, Id.run, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ size_pos))

/-- The per-hash bridge: a hashed word masked by `NMaskWord` (the contract's `land`)
    is exactly the model's `kec &&& NMaskWord`. -/
theorem uint256_kec_mask_toNat (kec : Nat) (hk : kec < EvmYul.UInt256.size) :
    ((UInt256.ofNat kec).land (UInt256.ofNat NiceTry.Fors.NMaskWord)).toNat
      = kec &&& NiceTry.Fors.NMaskWord := by
  have hmask : NiceTry.Fors.NMaskWord < EvmYul.UInt256.size := by
    unfold NiceTry.Fors.NMaskWord
    have : (2 : ℕ) ^ 256 = EvmYul.UInt256.size := by decide
    omega
  rw [uint256_ofNat_land_toNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hmask]

end NiceTry.Fors.Bridge
