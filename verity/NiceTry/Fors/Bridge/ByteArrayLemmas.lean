import EvmYul.MachineStateOps
import NiceTry.Fors.Bridge.EvmFfiSpec

/-!
# Class-M foundational `ByteArray` lemmas (route i)

Built on batteries' `data_append`/`size_append`/`*_extract` and the `EvmFfiSpec`
zeroes axioms. Core `ByteArray.write`/`copySlice`/`append`/`extract` are all
defined via reducible `.data` (Array) ops, so equalities reduce to Array reasoning.

Key lemma: a `ByteArray.write` that appends `source` at the end of `dest`
(`destAddr = dest.size`, full 16/32-byte word) just concatenates — the model of
consecutive `mstore`s into growing EVM memory.
-/

namespace NiceTry.Fors.Bridge

open EvmYul

@[simp] theorem byteArray_append_empty (a : ByteArray) : a ++ ByteArray.empty = a := by
  apply ByteArray.ext
  simp [ByteArray.data_append]

/-- A zero-length `zeroes` has empty `.data` (no `USize` literal juggling needed). -/
theorem zeroes_data_nil {n : USize} (h : n.toNat = 0) :
    (ffi.ByteArray.zeroes n).data = #[] := by
  have he := ffi_zeroes_eq_empty n h
  rw [he]; rfl

/--
Append-at-end characterization of `ByteArray.write` — the model of one `mstore`
into growing EVM memory: writing `source` exactly at `dest`'s end concatenates.

    destAddr = dest.size  →  0 < source.size  →
      (ByteArray.write source 0 dest destAddr source.size).data
        = dest.data ++ source.data

Both `ByteArray.write` paddings have length 0 here, collapsed via `zeroes_data_nil`;
the three `copySlice` extracts then reduce by `Array.extract_eq_self_of_le` /
`extract_empty_of_size_le_start`. The only trust used (besides Lean's) is
`ffi_zeroes_eq_empty` (confirmed via `#print axioms`). Non-overlap side-conditions
for multi-write composition are in `MemoryLayout.lean`.
-/
theorem byteArray_write_append
    (source dest : ByteArray) (destAddr : Nat)
    (hd : destAddr = dest.size) (hpos : 0 < source.size) :
    (ByteArray.write source 0 dest destAddr source.size).data
      = dest.data ++ source.data := by
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  subst hd
  have hz : ({ toBitVec := (↑(0 : Nat)) } : USize).toNat = 0 := by simp [USize.toNat]
  have hE : ({ toBitVec := (↑(min dest.size (dest.size + source.size)
                  - (dest.size + source.size))) } : USize).toNat = 0 := by
    have hk : min dest.size (dest.size + source.size) - (dest.size + source.size) = 0 := by omega
    rw [hk]; exact hz
  have hds : dest.data.size = dest.size := rfl
  have hss : source.data.size = source.size := rfl
  simp only [ByteArray.copySlice, ByteArray.data_append, Nat.sub_zero, Nat.min_self,
    Nat.sub_self, zeroes_data_nil hE, zeroes_data_nil hz, Array.append_empty]
  rw [Array.extract_eq_self_of_le (by omega), Array.extract_eq_self_of_le (by omega),
      Array.extract_empty_of_size_le_start (by omega), Array.append_empty]

end NiceTry.Fors.Bridge
