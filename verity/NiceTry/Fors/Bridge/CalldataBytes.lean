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

private theorem uint256_ofNat_eq_mk (n : Nat) (h : n < UInt256.size) :
    UInt256.ofNat n = ⟨⟨n, h⟩⟩ := by
  apply congrArg UInt256.mk
  apply Fin.ext
  simp [Nat.mod_eq_of_lt h]

theorem uint256_eq_of_toNat_eq (a b : UInt256) (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk av =>
  cases b with
  | mk bv =>
  apply congrArg UInt256.mk
  apply Fin.ext
  simpa [UInt256.toNat] using h

theorem uint256_shiftRight_224_ofNat_toNat (n : Nat) (h : n < UInt256.size) :
    (UInt256.shiftRight (UInt256.ofNat n) (UInt256.ofNat 224)).toNat = n / 2 ^ 224 := by
  rw [uint256_ofNat_eq_mk n h]
  rw [uint256_ofNat_eq_mk 224 (by norm_num [UInt256.size])]
  simp [UInt256.shiftRight, UInt256.toNat, Nat.shiftRight_eq_div_pow, UInt256.size]

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
  rfl

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

/-! ## Boundary note: `RawSig.len` is unbounded, ABI length words are not. -/

theorem rawLen_uint256_collision :
    UInt256.ofNat (SigLen + UInt256.size) = UInt256.ofNat SigLen := by
  apply uint256_eq_of_toNat_eq
  simp [UInt256.ofNat, UInt256.toNat, Fin.ofNat]

theorem rawLen_collision_bad_length : SigLen + UInt256.size ≠ SigLen := by
  unfold UInt256.size
  omega

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

private theorem byteArray_data_toList_get?_of_get? (ba : ByteArray)
    (i : Nat) (b : UInt8) (h : ba.get? i = some b) :
    ba.data.toList[i]? = some b := by
  unfold ByteArray.get? at h
  split at h
  · cases h
    rw [Array.getElem?_toList]
    simp [ByteArray.get]
  · contradiction

private theorem list_reverse_eq_drop4_reverse_append_four {α : Type}
    (xs : List α) (b0 b1 b2 b3 : α)
    (h0 : xs[0]? = some b0)
    (h1 : xs[1]? = some b1)
    (h2 : xs[2]? = some b2)
    (h3 : xs[3]? = some b3) :
    xs.reverse = (xs.drop 4).reverse ++ [b3, b2, b1, b0] := by
  cases xs with
  | nil => simp at h0
  | cons x0 xs =>
      simp at h0
      subst x0
      cases xs with
      | nil => simp at h1
      | cons x1 xs =>
          simp at h1
          subst x1
          cases xs with
          | nil => simp at h2
          | cons x2 xs =>
              simp at h2
              subst x2
              cases xs with
              | nil => simp at h3
              | cons x3 xs =>
                  simp at h3
                  subst x3
                  simp

private theorem fromBytes'_append (xs ys : List UInt8) :
    EvmYul.fromBytes' (xs ++ ys) =
      EvmYul.fromBytes' xs + 2 ^ (8 * xs.length) * EvmYul.fromBytes' ys := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      simp only [List.cons_append, EvmYul.fromBytes']
      rw [ih]
      rw [show 8 * (x :: xs).length = 8 + 8 * xs.length by
        simp [Nat.mul_add, Nat.add_comm]]
      rw [Nat.pow_add]
      ring

private theorem fromBytes'_lt (xs : List UInt8) :
    EvmYul.fromBytes' xs < 2 ^ (8 * xs.length) := by
  induction xs with
  | nil =>
      simp [EvmYul.fromBytes']
  | cons x xs ih =>
      unfold EvmYul.fromBytes'
      have hx : x.toFin.val < 2 ^ 8 := by
        have := x.toFin.isLt
        norm_num at this ⊢
        exact this
      simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
      have _ :=
        Nat.add_le_of_le_sub
          (Nat.one_le_pow _ _ (by decide))
          (Nat.le_sub_one_of_lt ih)
      linarith

private theorem fromBytes'_four (b0 b1 b2 b3 : UInt8) :
    EvmYul.fromBytes' [b3, b2, b1, b0] =
      b3.toFin.val + 2 ^ 8 * b2.toFin.val +
        2 ^ 16 * b1.toFin.val + 2 ^ 24 * b0.toFin.val := by
  simp [EvmYul.fromBytes']
  omega

private theorem fromBytes'_tail4_shift
    (b0 b1 b2 b3 : UInt8) (tail : List UInt8) (hlen : tail.length = 28) :
    EvmYul.fromBytes' (tail.reverse ++ [b3, b2, b1, b0]) / 2 ^ 224 =
      b0.toFin.val * 2 ^ 24 +
        b1.toFin.val * 2 ^ 16 +
        b2.toFin.val * 2 ^ 8 +
        b3.toFin.val := by
  rw [fromBytes'_append]
  have htailLen : tail.reverse.length = 28 := by
    simp [hlen]
  have htailBound : EvmYul.fromBytes' tail.reverse < 2 ^ 224 := by
    have h := fromBytes'_lt tail.reverse
    simpa [htailLen] using h
  rw [fromBytes'_four]
  rw [htailLen]
  norm_num
  omega

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

theorem encodeForsCalldata_readBytes_selector_size (raw : RawSig) (digest : Digest) :
    ((encodeForsCalldata raw digest).readBytes 0 32).size = 32 := by
  rw [readBytes_window_32]
  · simp [ByteArray.size_extract, encodeForsCalldata_size]
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

private theorem encodeForsCalldata_readBytes_selectorByte0
    (raw : RawSig) (digest : Digest) :
    ((encodeForsCalldata raw digest).readBytes 0 32).get? 0 =
      some (UInt8.ofNat 0x1a) := by
  rw [readBytes_window_32]
  · unfold ByteArray.get?
    rw [dif_pos (by simp [ByteArray.size_extract, encodeForsCalldata_size])]
    simp [ByteArray.get, encodeForsCalldata, forsSelector, ByteArray.data_extract,
      ByteArray.data_append]
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

private theorem encodeForsCalldata_readBytes_selectorByte1
    (raw : RawSig) (digest : Digest) :
    ((encodeForsCalldata raw digest).readBytes 0 32).get? 1 =
      some (UInt8.ofNat 0xad) := by
  rw [readBytes_window_32]
  · unfold ByteArray.get?
    rw [dif_pos (by simp [ByteArray.size_extract, encodeForsCalldata_size])]
    simp [ByteArray.get, encodeForsCalldata, forsSelector, ByteArray.data_extract,
      ByteArray.data_append]
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

private theorem encodeForsCalldata_readBytes_selectorByte2
    (raw : RawSig) (digest : Digest) :
    ((encodeForsCalldata raw digest).readBytes 0 32).get? 2 =
      some (UInt8.ofNat 0x75) := by
  rw [readBytes_window_32]
  · unfold ByteArray.get?
    rw [dif_pos (by simp [ByteArray.size_extract, encodeForsCalldata_size])]
    simp [ByteArray.get, encodeForsCalldata, forsSelector, ByteArray.data_extract,
      ByteArray.data_append]
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

private theorem encodeForsCalldata_readBytes_selectorByte3
    (raw : RawSig) (digest : Digest) :
    ((encodeForsCalldata raw digest).readBytes 0 32).get? 3 =
      some (UInt8.ofNat 0xc5) := by
  rw [readBytes_window_32]
  · unfold ByteArray.get?
    rw [dif_pos (by simp [ByteArray.size_extract, encodeForsCalldata_size])]
    simp [ByteArray.get, encodeForsCalldata, forsSelector, ByteArray.data_extract,
      ByteArray.data_append]
  · norm_num
  · rw [encodeForsCalldata_size]
    norm_num

private theorem encodeForsCalldata_selectorPrefix_reverse
    (raw : RawSig) (digest : Digest) :
    let bytes := (encodeForsCalldata raw digest).readBytes 0 32
    bytes.data.toList.reverse =
      (bytes.data.toList.drop 4).reverse ++
        [UInt8.ofNat 0xc5, UInt8.ofNat 0x75, UInt8.ofNat 0xad, UInt8.ofNat 0x1a] := by
  intro bytes
  apply list_reverse_eq_drop4_reverse_append_four
  · exact byteArray_data_toList_get?_of_get? bytes 0 _
      (by dsimp [bytes]; exact encodeForsCalldata_readBytes_selectorByte0 raw digest)
  · exact byteArray_data_toList_get?_of_get? bytes 1 _
      (by dsimp [bytes]; exact encodeForsCalldata_readBytes_selectorByte1 raw digest)
  · exact byteArray_data_toList_get?_of_get? bytes 2 _
      (by dsimp [bytes]; exact encodeForsCalldata_readBytes_selectorByte2 raw digest)
  · exact byteArray_data_toList_get?_of_get? bytes 3 _
      (by dsimp [bytes]; exact encodeForsCalldata_readBytes_selectorByte3 raw digest)

theorem encodeForsCalldata_selector_shift_toNat (raw : RawSig) (digest : Digest) :
    (UInt256.shiftRight
        (EvmYul.uInt256OfByteArray ((encodeForsCalldata raw digest).readBytes 0 32))
        (UInt256.ofNat 224)).toNat = 0x1aad75c5 := by
  let bytes := (encodeForsCalldata raw digest).readBytes 0 32
  have hsize : bytes.size = 32 := by
    dsimp [bytes]
    exact encodeForsCalldata_readBytes_selector_size raw digest
  have hlen : bytes.data.toList.length = 32 := by
    simpa [ByteArray.size] using hsize
  have hprefix := encodeForsCalldata_selectorPrefix_reverse raw digest
  have htailLen : (bytes.data.toList.drop 4).length = 28 := by
    rw [List.length_drop, hlen]
  have hvalLt : EvmYul.fromBytes' bytes.data.toList.reverse < UInt256.size := by
    have h := fromBytes'_lt bytes.data.toList.reverse
    have hrevLen : bytes.data.toList.reverse.length = 32 := by
      simp [hlen]
    simpa [hrevLen, UInt256.size] using h
  have hshiftNat :
      EvmYul.fromBytes' bytes.data.toList.reverse / 2 ^ 224 = 0x1aad75c5 := by
    dsimp [bytes] at hprefix
    rw [hprefix]
    have htail :=
      fromBytes'_tail4_shift
        (UInt8.ofNat 0x1a) (UInt8.ofNat 0xad)
        (UInt8.ofNat 0x75) (UInt8.ofNat 0xc5)
        (bytes.data.toList.drop 4) htailLen
    simpa [UInt8.ofNat, UInt8.size] using htail
  unfold EvmYul.uInt256OfByteArray
  rw [uint256_shiftRight_224_ofNat_toNat _ hvalLt]
  exact hshiftNat

theorem encodeForsCalldata_selector_shift (raw : RawSig) (digest : Digest) :
    UInt256.shiftRight
        (EvmYul.uInt256OfByteArray ((encodeForsCalldata raw digest).readBytes 0 32))
        (UInt256.ofNat 224) =
      UInt256.ofNat 0x1aad75c5 := by
  apply uint256_eq_of_toNat_eq
  rw [encodeForsCalldata_selector_shift_toNat]
  rw [uint256_ofNat_toNat_of_lt 0x1aad75c5 (by norm_num [UInt256.size])]

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

theorem calldataload_encode_selector (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    UInt256.shiftRight (EvmYul.State.calldataload s (UInt256.ofNat 0))
        (UInt256.ofNat 224) =
      UInt256.ofNat 0x1aad75c5 := by
  unfold EvmYul.State.calldataload
  rw [uint256_ofNat_toNat_of_lt 0 (by norm_num [UInt256.size])]
  rw [hcd]
  exact encodeForsCalldata_selector_shift raw digest

end NiceTry.Fors.Bridge
