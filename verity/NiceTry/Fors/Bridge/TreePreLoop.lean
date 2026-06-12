import NiceTry.Fors.Bridge.TreeCalldata
import NiceTry.Fors.Bridge.ClassARecover

/-!
# Pre-loop trace support: padding `mstore` calculus and the hmsg window

`fun_recover`'s pre-loop prefix (statements 18–31) builds the hmsg transcript
with five `mstore`s on the 96-byte dispatcher memory (`mstore(64, 0x80)` ran
before the call), hashes `[0, 0xa0)`, and then parks `pkSeed` at `0x380` — a
*padding* store (`0x380 > 0xa0`) that zero-extends memory to `0x3a0`, the
loop-entry size `LoopInv` expects.

The in-bounds (`mstore_extract_*`) and boundary (`mstore_extract_*'`,
`a.toNat ≤ size`) calculi from `TreeMemory` don't cover that padding store;
the first section here adds the `size ≤ a.toNat` case. The second section
assembles the five-word hmsg keccak window, mirroring
`scratch_leaf_read_of_extracts`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

/-! ## Padding `mstore` calculus (`size ≤ destAddr`) -/

/-- `USize` round-trip for platform-independent small literals. -/
theorem usize_mk_toNat_of_lt (k : Nat) (h : k < 2 ^ 32) :
    ({ toBitVec := (↑k : BitVec System.Platform.numBits) } : USize).toNat = k := by
  show (BitVec.ofNat System.Platform.numBits k).toNat = k
  rw [BitVec.toNat_ofNat]
  rcases System.Platform.numBits_eq with hb | hb <;> rw [hb]
  · exact Nat.mod_eq_of_lt h
  · exact Nat.mod_eq_of_lt (lt_of_lt_of_le h (by norm_num))

/-- A `ByteArray.write` past the end of `dest` appends zero padding and then
    the word: the padding twin of `byteArray_write_overwrite`. -/
theorem byteArray_write_pad (source dest : ByteArray) (destAddr : Nat)
    (hs : source.size = 32) (hbound : dest.size ≤ destAddr) :
    (ByteArray.write source 0 dest destAddr 32).data
      = dest.data
        ++ (ffi.ByteArray.zeroes
            ({ toBitVec := (↑(destAddr - dest.size) :
                BitVec System.Platform.numBits) } : USize)).data
        ++ source.data := by
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  have hds : dest.data.size = dest.size := rfl
  have hss : source.data.size = source.size := rfl
  have hz0 : ({ toBitVec := (↑(0 : Nat)) } : USize).toNat = 0 := by simp [USize.toNat]
  simp only [ByteArray.copySlice, ByteArray.data_append, Nat.sub_zero]
  rw [show min 32 source.size = 32 from by omega,
    show min dest.size (destAddr + 32) = dest.size from by omega,
    show dest.size - (destAddr + 32) = 0 from by omega,
    zeroes_data_nil hz0, Array.append_empty]
  set Z : Array UInt8 := (ffi.ByteArray.zeroes
    ({ toBitVec := (↑(destAddr - dest.size) :
        BitVec System.Platform.numBits) } : USize)).data with hZdef
  have hZle : Z.size ≤ destAddr - dest.size := by
    rw [hZdef,
      show (ffi.ByteArray.zeroes
        ({ toBitVec := (↑(destAddr - dest.size) :
            BitVec System.Platform.numBits) } : USize)).data.size
      = (ffi.ByteArray.zeroes
          ({ toBitVec := (↑(destAddr - dest.size) :
              BitVec System.Platform.numBits) } : USize)).size from rfl,
      ffi_zeroes_size]
    show (BitVec.ofNat System.Platform.numBits (destAddr - dest.size)).toNat ≤ _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  rw [show min 32 source.data.size = 32 from by omega]
  rw [Array.extract_eq_self_of_le (as := source.data) (j := 32) (by omega)]
  rw [Array.extract_eq_self_of_le (as := dest.data ++ Z) (j := destAddr) (by
    rw [Array.size_append]
    omega)]
  rw [Array.extract_empty_of_size_le_start (by
    rw [Array.size_append]
    omega : (dest.data ++ Z).size ≤ destAddr + 32)]
  rw [Array.append_empty]

/-- Memory size after a padding `mstore`: exactly `destAddr + 32`. -/
theorem mstore_pad_size (m : MachineState) (a v : UInt256)
    (hb : m.memory.size ≤ a.toNat) (hsmall : a.toNat < 2 ^ 32) :
    (m.mstore a v).memory.size = a.toNat + 32 := by
  show (m.mstore a v).memory.data.size = a.toNat + 32
  rw [mstore_memory]
  rw [byteArray_write_pad v.toByteArray m.memory a.toNat
    (uint256_toByteArray_size v) hb]
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hvs : v.toByteArray.data.size = 32 := uint256_toByteArray_size v
  have hpad : (ffi.ByteArray.zeroes
      ({ toBitVec := (↑(a.toNat - m.memory.size) :
          BitVec System.Platform.numBits) } : USize)).data.size
        = a.toNat - m.memory.size := by
    rw [show (ffi.ByteArray.zeroes
        ({ toBitVec := (↑(a.toNat - m.memory.size) :
            BitVec System.Platform.numBits) } : USize)).data.size
      = (ffi.ByteArray.zeroes
          ({ toBitVec := (↑(a.toNat - m.memory.size) :
              BitVec System.Platform.numBits) } : USize)).size from rfl,
      ffi_zeroes_size, usize_mk_toNat_of_lt _ (by omega)]
  simp only [Array.size_append]
  omega

/-- The written window of a padding `mstore` reads back the word. -/
theorem mstore_pad_extract_self (m : MachineState) (a v : UInt256)
    (hb : m.memory.size ≤ a.toNat) (hsmall : a.toNat < 2 ^ 32) :
    (m.mstore a v).memory.data.extract a.toNat (a.toNat + 32)
      = v.toByteArray.data := by
  show (m.mstore a v).memory.data.extract a.toNat (a.toNat + 32) = _
  rw [mstore_memory]
  rw [byteArray_write_pad v.toByteArray m.memory a.toNat
    (uint256_toByteArray_size v) hb]
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hvs : v.toByteArray.data.size = 32 := uint256_toByteArray_size v
  have hpad : (ffi.ByteArray.zeroes
      ({ toBitVec := (↑(a.toNat - m.memory.size) :
          BitVec System.Platform.numBits) } : USize)).data.size
        = a.toNat - m.memory.size := by
    rw [show (ffi.ByteArray.zeroes
        ({ toBitVec := (↑(a.toNat - m.memory.size) :
            BitVec System.Platform.numBits) } : USize)).data.size
      = (ffi.ByteArray.zeroes
          ({ toBitVec := (↑(a.toNat - m.memory.size) :
              BitVec System.Platform.numBits) } : USize)).size from rfl,
      ffi_zeroes_size, usize_mk_toNat_of_lt _ (by omega)]
  have hA : (m.memory.data ++ (ffi.ByteArray.zeroes
      ({ toBitVec := (↑(a.toNat - m.memory.size) :
          BitVec System.Platform.numBits) } : USize)).data).size = a.toNat := by
    rw [Array.size_append]
    omega
  rw [Array.extract_append_right'
    (a := m.memory.data ++ (ffi.ByteArray.zeroes
      ({ toBitVec := (↑(a.toNat - m.memory.size) :
          BitVec System.Platform.numBits) } : USize)).data)
    (b := v.toByteArray.data) (i := a.toNat) (j := a.toNat + 32) (by omega)]
  rw [hA, Nat.sub_self, show a.toNat + 32 - a.toNat = 32 from by omega]
  exact Array.extract_eq_self_of_le (by omega)

/-- Extracts inside the old memory are unchanged by a padding `mstore`. -/
theorem mstore_pad_extract_below (m : MachineState) (a v : UInt256) (lo hi : Nat)
    (hb : m.memory.size ≤ a.toNat) (hhi : hi ≤ m.memory.size) :
    (m.mstore a v).memory.data.extract lo hi = m.memory.data.extract lo hi := by
  rw [mstore_memory]
  rw [byteArray_write_pad v.toByteArray m.memory a.toNat
    (uint256_toByteArray_size v) hb]
  have hmd : m.memory.data.size = m.memory.size := rfl
  rw [Array.extract_append_left' (h := by
    rw [Array.size_append]
    omega)]
  exact Array.extract_append_left' (h := by omega)

/-! ## The hmsg keccak window -/

/-- The 160-byte hmsg window `[0, 0xa0)` as five extracted words —
    `scratch_leaf_read_of_extracts` at base 0. -/
theorem hmsg_read_of_extracts (m : MachineState) (w0 w1 w2 w3 w4 : UInt256)
    (hsize : 0xa0 ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x00 0x20 = w0.toByteArray.data)
    (h1 : m.memory.data.extract 0x20 0x40 = w1.toByteArray.data)
    (h2 : m.memory.data.extract 0x40 0x60 = w2.toByteArray.data)
    (h3 : m.memory.data.extract 0x60 0x80 = w3.toByteArray.data)
    (h4 : m.memory.data.extract 0x80 0xa0 = w4.toByteArray.data) :
    (ByteArray.readWithPadding m.memory 0 0xa0).data
      = concatData ([w0, w1, w2, w3, w4].map UInt256.toByteArray) := by
  have hmd : m.memory.data.size = m.memory.size := rfl
  have hsz : (0xa0 : Nat) ≤ m.memory.data.size := by omega
  rw [readWithPadding_window _ 0 0xa0 (by omega) (by decide) (by decide)]
  rw [ByteArray.data_extract]
  show m.memory.data.extract 0 0xa0 = _
  rw [extract_split m.memory.data 0 0x20 0xa0 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x20 0x40 0xa0 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x40 0x60 0xa0 (by omega) (by omega) hsz,
      extract_split m.memory.data 0x60 0x80 0xa0 (by omega) (by omega) hsz,
      h0, h1, h2, h3, h4]
  simp [concatData]

/-- The hmsg keccak value from per-slot extract facts: the interpreter's
    `keccak256(0, 0xa0)` is the model's `hMsg` of the stored transcript. -/
theorem hmsg_derivation_of_extracts
    (m : MachineState) (pkSeed r digest domain counter : UInt256)
    (hdomain : domain.toNat = ForsDomainWord)
    (hsize : 0xa0 ≤ m.memory.size)
    (h0 : m.memory.data.extract 0x00 0x20 = pkSeed.toByteArray.data)
    (h1 : m.memory.data.extract 0x20 0x40 = r.toByteArray.data)
    (h2 : m.memory.data.extract 0x40 0x60 = digest.toByteArray.data)
    (h3 : m.memory.data.extract 0x60 0x80 = domain.toByteArray.data)
    (h4 : m.memory.data.extract 0x80 0xa0 = counter.toByteArray.data) :
    ((m.keccak256 (UInt256.ofNat 0) (UInt256.ofNat 0xa0)).1).toNat
      = hMsg pkSeed.toNat r.toNat digest.toNat counter.toNat := by
  rw [keccak256_value,
    show (UInt256.ofNat 0).toNat = 0 from uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 0xa0).toNat = 0xa0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  rw [uint256_ofNat_toNat_of_lt _ (ffi_kec_lt _)]
  exact evm_keccak_hmsg _ pkSeed r digest domain counter hdomain
    (hmsg_read_of_extracts m pkSeed r digest domain counter hsize h0 h1 h2 h3 h4)

end NiceTry.Fors.Bridge
