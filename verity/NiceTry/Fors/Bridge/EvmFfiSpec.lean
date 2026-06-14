import EvmYul.MachineStateOps
import NiceTry.Fors.FullKeccak
import Lean

/-!
# Class-M trusted memory-primitive layer (EVMYulLean FFI specs)

**Finding (this is why Class-M is not "just prove the bytes"):** EVMYulLean's
byte-level memory ops route through `@[extern] opaque` FFI primitives that have no
reducible body and no lemmas anywhere in the EVMYulLean tree:

* `ffi.ByteArray.zeroes : USize → ByteArray` — memory padding, used by BOTH
  `ByteArray.write` (hence `mstore`/`writeWord`) and `UInt256.toByteArray`.
* `ffi.keccak256` / `ffi.KEC` — the hash (already our trusted keccak).

Consequently byte-level memory equalities are **not kernel-reducible**. We localize
that into this small trusted spec — the minimal TCB additions for Class-M. These
are total-correctness specs of EVM memory primitives, NOT cryptographic
assumptions, so they don't touch the soundness story.

The transcript model now has one opaque `keccakWord`; `keccakHash16` and
`keccakAddress` are proved masks of that shared word. `TranscriptEncoding.lean`
provides the canonical EVM-byte encoding, and `evm_keccak_transcript` is the
single remaining cryptographic bridge. See `CLASS-M.md`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open Lean Elab Tactic Meta

/-- `ffi.ByteArray.zeroes n` produces exactly `n` bytes. -/
theorem ffi_zeroes_size (n : USize) :
    (ffi.ByteArray.zeroes n).size = n.toNat := by
  simp [ffi.ByteArray.zeroes, ByteArray.size]

/-- `ffi.ByteArray.zeroes n` is all-zero. -/
theorem ffi_zeroes_get! (n : USize) (i : Nat) (h : i < n.toNat) :
    (ffi.ByteArray.zeroes n).get! i = (0 : UInt8) := by
  simp [ffi.ByteArray.zeroes, ByteArray.get!, h]

/-- Zero-length padding is the empty array. Keyed on `.toNat` so it collapses the
    `zeroes ⟨k⟩` terms that `ByteArray.write`/`readWithPadding` leave behind
    regardless of how the `USize` literal is constructed. -/
theorem ffi_zeroes_eq_empty (n : USize) (h : n.toNat = 0) :
    ffi.ByteArray.zeroes n = ByteArray.empty := by
  simp [ffi.ByteArray.zeroes, h]
  rfl

/-! ## Word codec

EVMYulLean keeps the recursive little-endian encoder and its length theorem
private. The theorem is nevertheless present in the compiled environment; this
small elaborator hook applies that declaration by its generated name. This is
kernel-checked and introduces no trust, but should be replaced by the public
upstream theorem when the pinned dependency exposes one. -/
elab "apply_evmyul_toBytes_uint256_length_le" : tactic => do
  let theoremName :=
    Name.str
      (Name.str
        (Name.num
          (Name.str (Name.str (Name.str .anonymous "_private") "EvmYul") "UInt256")
          0)
        "EvmYul")
      "toBytes'_UInt256_le"
  let goals ← (← getMainGoal).apply (mkConst theoremName)
  replaceMainGoal goals

private theorem toBytesBigEndian_uint256_length_le
    {n : Nat} (h : n < EvmYul.UInt256.size) :
    (EvmYul.toBytesBigEndian n).length ≤ 32 := by
  unfold EvmYul.toBytesBigEndian
  simp
  apply_evmyul_toBytes_uint256_length_le
  exact h

private theorem list_toByteArray_loop_size (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).size = acc.size + bytes.length := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, Nat.add_assoc]
      omega

private theorem list_toByteArray_loop_data_toList (bytes : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop bytes acc).data.toList = acc.data.toList ++ bytes := by
  induction bytes generalizing acc with
  | nil =>
      simp [List.toByteArray.loop]
  | cons _ bytes ih =>
      simp [List.toByteArray.loop, ih, List.append_assoc]

private theorem list_toByteArray_size (bytes : List UInt8) :
    bytes.toByteArray.size = bytes.length := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_size]
  simp

private theorem list_toByteArray_data_toList (bytes : List UInt8) :
    bytes.toByteArray.data.toList = bytes := by
  unfold List.toByteArray
  rw [list_toByteArray_loop_data_toList]
  simp

private theorem usize_sub_toNat_of_le_32 (n : Nat) (hn : n ≤ 32) :
    ((OfNat.ofNat 32 : USize) - (OfNat.ofNat n : USize)).toNat = 32 - n := by
  rw [USize.toNat_sub, USize.toNat_ofNat, USize.toNat_ofNat]
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits]
    have hnMod : n % 4294967296 = n := Nat.mod_eq_of_lt (by omega)
    rw [hnMod]
    omega
  · rw [hbits]
    have hnMod : n % 18446744073709551616 = n := Nat.mod_eq_of_lt (by omega)
    rw [hnMod]
    omega

theorem uint256_toByteArray_size (v : UInt256) : (UInt256.toByteArray v).size = 32 := by
  have hBytesSize :
      (EvmYul.toBytesBigEndian v.toNat).toByteArray.data.size =
        (EvmYul.toBytesBigEndian v.toNat).length := by
    simpa [ByteArray.size] using
      list_toByteArray_size (EvmYul.toBytesBigEndian v.toNat)
  have hLen : (EvmYul.toBytesBigEndian v.toNat).length ≤ 32 :=
    toBytesBigEndian_uint256_length_le (n := v.toNat) v.val.isLt
  unfold EvmYul.UInt256.toByteArray BE
  rw [ByteArray.size_append]
  simp [ffi.ByteArray.zeroes, ByteArray.size]
  rw [hBytesSize]
  rw [usize_sub_toNat_of_le_32 _ hLen]
  omega

/-- Big-endian word encoding is a left inverse for EVM word decoding.

The private `fromBytes'_toBytes'` theorem is tagged `[simp]` upstream, so Lean's
simplifier can use it while checking this public wrapper. -/
theorem uint256_toByteArray_roundtrip (v : UInt256) :
    EvmYul.uInt256OfByteArray v.toByteArray = v := by
  cases v with
  | mk val =>
      simp [EvmYul.uInt256OfByteArray, EvmYul.UInt256.toByteArray, BE,
        ffi.ByteArray.zeroes, ByteArray.data_append, list_toByteArray_data_toList,
        EvmYul.toBytesBigEndian, EvmYul.UInt256.ofNat]
      apply congrArg UInt256.mk
      apply Fin.ext
      simp [UInt256.toNat]

end NiceTry.Fors.Bridge
