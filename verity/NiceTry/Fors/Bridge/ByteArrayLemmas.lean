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
    (source dest : ByteArray) (destAddr len : Nat)
    (hd : destAddr = dest.size) (hlen : len = source.size) (hpos : 0 < len) :
    (ByteArray.write source 0 dest destAddr len).data
      = dest.data ++ source.data := by
  subst hlen
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

/-- Reading a full byte array back (offset 0, length = size) is the identity —
    what `keccak256(0, size)` reads after the memory has been written exactly.
    `readWithoutPadding` returns the whole array; the trailing `zeroes 0` padding
    collapses. -/
theorem readWithPadding_exact (s : ByteArray) (n : Nat)
    (hn : n = s.size) (hpos : 0 < s.size) (hlt : s.size < 2 ^ 64) :
    s.readWithPadding 0 n = s := by
  have hds : s.data.size = s.size := rfl
  have hr : s.readWithoutPadding 0 n = s := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by omega)]
    apply ByteArray.ext
    simp only [hn, Nat.min_self, Nat.zero_add, ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by omega)
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  simp only [hr]
  have hz : ({ toBitVec := (↑n - ↑s.size : BitVec System.Platform.numBits) } : USize).toNat = 0 := by
    rw [hn]; simp
  rw [ffi_zeroes_eq_empty _ hz, byteArray_append_empty]

/-- Two consecutive 32-byte word writes at offsets 0 and 32 into empty memory
    concatenate their encodings — the `mstore(0x00, w0); mstore(0x20, w1)` pattern
    underlying the FORS address-derivation transcript. -/
theorem two_word_writes (w0 w1 : UInt256) :
    (ByteArray.write w1.toByteArray 0
        (ByteArray.write w0.toByteArray 0 ByteArray.empty 0 32) 32 32).data
      = w0.toByteArray.data ++ w1.toByteArray.data := by
  have hs0 : w0.toByteArray.size = 32 := uint256_toByteArray_size w0
  have hs1 : w1.toByteArray.size = 32 := uint256_toByteArray_size w1
  have hin : (ByteArray.write w0.toByteArray 0 ByteArray.empty 0 32).data
              = w0.toByteArray.data := by
    rw [byteArray_write_append w0.toByteArray ByteArray.empty 0 32 (by decide) hs0.symm (by omega)]
    simp
  have hisize : (ByteArray.write w0.toByteArray 0 ByteArray.empty 0 32).size = 32 := by
    show (ByteArray.write w0.toByteArray 0 ByteArray.empty 0 32).data.size = 32
    rw [hin]; exact hs0
  rw [byteArray_write_append w1.toByteArray
        (ByteArray.write w0.toByteArray 0 ByteArray.empty 0 32) 32 32
        hisize.symm hs1.symm (by omega), hin]

end NiceTry.Fors.Bridge
