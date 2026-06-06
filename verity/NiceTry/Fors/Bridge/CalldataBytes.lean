import NiceTry.Fors.Bridge.EvmRun
import NiceTry.Fors.Bridge.ByteArrayLemmas
import NiceTry.Fors.Proofs.Basic

/-!
# Class-A calldata byte facts

Foundational size and word-codec facts for `encodeForsCalldata`. The later
`calldataload` lemmas build on these constants plus `ByteArray.readBytes`
window reasoning.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

theorem word32_size (n : Nat) : (word32 n).size = 32 := by
  exact uint256_toByteArray_size (UInt256.ofNat n)

theorem word32_uInt256_roundtrip (n : Nat) :
    EvmYul.uInt256OfByteArray (word32 n) = UInt256.ofNat n := by
  exact uint256_toByteArray_roundtrip (UInt256.ofNat n)

theorem word32_uInt256_roundtrip_toNat (n : Nat) (h : n < UInt256.size) :
    (EvmYul.uInt256OfByteArray (word32 n)).toNat = n := by
  rw [word32_uInt256_roundtrip]
  change (Fin.ofNat UInt256.size n).val = n
  simp [Fin.ofNat]
  exact Nat.mod_eq_of_lt h

theorem word32_extract_16_32_size (n : Nat) :
    ((word32 n).extract 16 32).size = 16 := by
  simp [word32, ByteArray.size_extract, uint256_toByteArray_size (UInt256.ofNat n)]

theorem forsSelector_size : forsSelector.size = 4 := by
  simp [forsSelector, word32, ByteArray.size_extract,
    uint256_toByteArray_size (UInt256.ofNat 0x1aad75c5)]

private theorem forsPayload_fold_size (raw : RawSig) (xs : List Nat) (acc : ByteArray) :
    (xs.foldl
        (fun acc i =>
          acc ++ ((UInt256.ofNat (raw.read16 (16 * i))).toByteArray).extract 16 32)
        acc).size = acc.size + 16 * xs.length := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      rw [ByteArray.size_append]
      rw [show (((UInt256.ofNat (raw.read16 (16 * i))).toByteArray).extract 16 32).size = 16 by
        simpa [word32] using word32_extract_16_32_size (raw.read16 (16 * i))]
      omega

theorem forsPayload_size (raw : RawSig) : (forsPayload raw).size = 2448 := by
  unfold forsPayload
  rw [forsPayload_fold_size]
  simp

theorem encodeForsCalldata_size (raw : RawSig) (digest : Digest) :
    (encodeForsCalldata raw digest).size = 2548 := by
  simp [encodeForsCalldata, ByteArray.size_append, forsSelector_size, word32_size,
    forsPayload_size]

theorem encodeForsCalldata_calldatasize_word (raw : RawSig) (digest : Digest) :
    UInt256.ofNat (encodeForsCalldata raw digest).size = UInt256.ofNat 2548 := by
  rw [encodeForsCalldata_size]

end NiceTry.Fors.Bridge
