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

set_option maxHeartbeats 800000

theorem uint256_ofNat_toNat_of_lt (n : Nat) (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  change (Fin.ofNat UInt256.size n).val = n
  simp [Fin.ofNat]
  exact Nat.mod_eq_of_lt h

theorem word32_size (n : Nat) : (word32 n).size = 32 := by
  exact uint256_toByteArray_size (UInt256.ofNat n)

theorem word32_uInt256_roundtrip (n : Nat) :
    EvmYul.uInt256OfByteArray (word32 n) = UInt256.ofNat n := by
  exact uint256_toByteArray_roundtrip (UInt256.ofNat n)

theorem word32_uInt256_roundtrip_toNat (n : Nat) (h : n < UInt256.size) :
    (EvmYul.uInt256OfByteArray (word32 n)).toNat = n := by
  rw [word32_uInt256_roundtrip]
  exact uint256_ofNat_toNat_of_lt n h

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

theorem readBytes_window_32 (source : ByteArray) (start : Nat)
    (hstart : start < 2 ^ 64)
    (hbound : start + 32 ≤ source.size) :
    source.readBytes start 32 = source.extract start (start + 32) := by
  unfold ByteArray.readBytes
  have hstart' : start < 18446744073709551616 := by
    simpa using hstart
  have hsmall : (decide (start < 2 ^ 64) && decide (32 < 2 ^ 64)) = true := by
    simp [hstart']
  simp only [hsmall, ↓reduceIte]
  rw [show source.copySlice start ByteArray.empty 0 32 =
      source.extract start (start + 32) by
    simp [ByteArray.extract]]
  let z : USize :=
    { toBitVec := (↑32 - ↑(source.extract start (start + 32)).size :
      BitVec System.Platform.numBits) }
  change source.extract start (start + 32) ++ ffi.ByteArray.zeroes z =
    source.extract start (start + 32)
  have hsize : (source.extract start (start + 32)).size = 32 := by
    simp [ByteArray.size_extract]
    omega
  have hz : z.toNat = 0 := by
    dsimp [z]
    rw [hsize]
    simp
  rw [ffi_zeroes_eq_empty z hz, byteArray_append_empty]

theorem byteArray_append_assoc (a b c : ByteArray) : a ++ b ++ c = a ++ (b ++ c) := by
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem byteArray_extract_second (a b c : ByteArray) :
    ((a ++ b ++ c).extract a.size (a.size + b.size)) = b := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  change (a ++ b ++ c).data.extract a.data.size (a.data.size + b.data.size) = b.data
  rw [show (a ++ b ++ c).data = a.data ++ b.data ++ c.data by
    simp [ByteArray.data_append]]
  exact extract_middle a.data b.data c.data

theorem encodeForsCalldata_readBytes_offset (raw : RawSig) (digest : Digest) :
    (encodeForsCalldata raw digest).readBytes 4 32 = word32 0x40 := by
  rw [readBytes_window_32]
  · unfold encodeForsCalldata
    let tail := word32 digest ++ word32 raw.len ++ forsPayload raw
    have hsel : forsSelector.size = 4 := forsSelector_size
    have hoff : (word32 0x40).size = 32 := word32_size 0x40
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    have hdata :
        (forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len ++
            forsPayload raw).data =
          forsSelector.data ++ (word32 0x40).data ++ tail.data := by
      dsimp [tail]
      simp [ByteArray.data_append, Array.append_assoc]
    rw [hdata]
    have hselData : forsSelector.data.size = 4 := hsel
    have hoffData : (word32 0x40).data.size = 32 := hoff
    rw [hselData.symm]
    rw [hoffData.symm]
    exact extract_middle forsSelector.data (word32 0x40).data tail.data
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

theorem encodeForsCalldata_readBytes_digest (raw : RawSig) (digest : Digest) :
    (encodeForsCalldata raw digest).readBytes 36 32 = word32 digest := by
  rw [readBytes_window_32]
  · unfold encodeForsCalldata
    let pref := forsSelector ++ word32 0x40
    let tail := word32 raw.len ++ forsPayload raw
    have hprefix_size : pref.size = 36 := by
      dsimp [pref]
      rw [ByteArray.size_append, forsSelector_size, word32_size]
    have hdigest : (word32 digest).size = 32 := word32_size digest
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    have hdata :
        (forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len ++
            forsPayload raw).data =
          pref.data ++ (word32 digest).data ++ tail.data := by
      dsimp [pref, tail]
      simp [ByteArray.data_append, Array.append_assoc]
    rw [hdata]
    have hprefData : pref.data.size = 36 := hprefix_size
    have hdigestData : (word32 digest).data.size = 32 := hdigest
    rw [hprefData.symm]
    rw [hdigestData.symm]
    exact extract_middle pref.data (word32 digest).data tail.data
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

theorem encodeForsCalldata_readBytes_length (raw : RawSig) (digest : Digest) :
    (encodeForsCalldata raw digest).readBytes 0x44 32 = word32 raw.len := by
  rw [readBytes_window_32]
  · unfold encodeForsCalldata
    let pref := forsSelector ++ word32 0x40 ++ word32 digest
    let tail := forsPayload raw
    have hprefix_size : pref.size = 0x44 := by
      dsimp [pref]
      simp [ByteArray.size_append, forsSelector_size, word32_size]
    have hlen : (word32 raw.len).size = 32 := word32_size raw.len
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    have hdata :
        (forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len ++
            forsPayload raw).data =
          pref.data ++ (word32 raw.len).data ++ tail.data := by
      dsimp [pref, tail]
      simp [ByteArray.data_append, Array.append_assoc]
    rw [hdata]
    have hprefData : pref.data.size = 0x44 := hprefix_size
    have hlenData : (word32 raw.len).data.size = 32 := hlen
    rw [hprefData.symm]
    rw [hlenData.symm]
    exact extract_middle pref.data (word32 raw.len).data tail.data
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

theorem encodeForsCalldata_uInt256_offset (raw : RawSig) (digest : Digest) :
    EvmYul.uInt256OfByteArray
        ((encodeForsCalldata raw digest).readBytes 4 32) =
      UInt256.ofNat 0x40 := by
  rw [encodeForsCalldata_readBytes_offset, word32_uInt256_roundtrip]

theorem encodeForsCalldata_uInt256_digest (raw : RawSig) (digest : Digest) :
    EvmYul.uInt256OfByteArray
        ((encodeForsCalldata raw digest).readBytes 36 32) =
      UInt256.ofNat digest := by
  rw [encodeForsCalldata_readBytes_digest, word32_uInt256_roundtrip]

theorem encodeForsCalldata_uInt256_length (raw : RawSig) (digest : Digest) :
    EvmYul.uInt256OfByteArray
        ((encodeForsCalldata raw digest).readBytes 0x44 32) =
      UInt256.ofNat raw.len := by
  rw [encodeForsCalldata_readBytes_length, word32_uInt256_roundtrip]

theorem calldataload_encode_offset (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    EvmYul.State.calldataload s (UInt256.ofNat 4) = UInt256.ofNat 0x40 := by
  unfold EvmYul.State.calldataload
  rw [uint256_ofNat_toNat_of_lt 4 (by norm_num [UInt256.size])]
  rw [hcd]
  exact encodeForsCalldata_uInt256_offset raw digest

theorem calldataload_encode_digest (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    EvmYul.State.calldataload s (UInt256.ofNat 36) = UInt256.ofNat digest := by
  unfold EvmYul.State.calldataload
  rw [uint256_ofNat_toNat_of_lt 36 (by norm_num [UInt256.size])]
  rw [hcd]
  exact encodeForsCalldata_uInt256_digest raw digest

theorem calldataload_encode_length (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    EvmYul.State.calldataload s (UInt256.ofNat 0x44) = UInt256.ofNat raw.len := by
  unfold EvmYul.State.calldataload
  rw [uint256_ofNat_toNat_of_lt 0x44 (by norm_num [UInt256.size])]
  rw [hcd]
  exact encodeForsCalldata_uInt256_length raw digest

end NiceTry.Fors.Bridge
