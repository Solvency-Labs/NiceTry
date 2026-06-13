import NiceTry.Fors.Bridge.TreeFinal
import NiceTry.Fors.Bridge.CalldataBytes

/-!
# M4: the general calldata glue — masked payload reads are `read16` values

Generalizes `CalldataBytes`' fixed-offset payload lemmas over all 16-aligned
payload offsets, and proves the masked-word value identity: for a well-formed
chunk (`read16` packed in the top half), the contract's
`and(calldataload(100 + 16k), not(0xff…ff))` is exactly `raw.read16 (16k)`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul
open NiceTry.Fors

set_option maxHeartbeats 2000000

/-! ## Byte-value toolkit -/

theorem fromBytes'_append (l₁ l₂ : List UInt8) :
    fromBytes' (l₁ ++ l₂) = fromBytes' l₁ + 2 ^ (8 * l₁.length) * fromBytes' l₂ := by
  induction l₁ with
  | nil => simp [fromBytes']
  | cons b bs ih =>
    show b.toFin.val + 2 ^ 8 * fromBytes' (bs ++ l₂) = _
    rw [ih]
    show _ = b.toFin.val + 2 ^ 8 * fromBytes' bs + 2 ^ (8 * (bs.length + 1)) * fromBytes' l₂
    rw [show 8 * (bs.length + 1) = 8 * bs.length + 8 from by ring, pow_add]
    ring

/-- Big-endian decode of a concatenation. -/
theorem fromBE_append (A B : ByteArray) :
    fromByteArrayBigEndian (A ++ B)
      = fromByteArrayBigEndian A * 2 ^ (8 * B.size) + fromByteArrayBigEndian B := by
  show fromBytes' (A ++ B).toList.reverse = _
  rw [byteArray_toList_eq,
    show (A ++ B).data = A.data ++ B.data from ByteArray.data_append .., 
    Array.toList_append, List.reverse_append, fromBytes'_append]
  show fromBytes' B.data.toList.reverse
      + 2 ^ (8 * B.data.toList.reverse.length) * fromBytes' A.data.toList.reverse = _
  rw [List.length_reverse, Array.length_toList]
  have hA : fromBytes' A.data.toList.reverse = fromByteArrayBigEndian A := by
    show _ = fromBytes' A.toList.reverse
    rw [byteArray_toList_eq]
  have hB : fromBytes' B.data.toList.reverse = fromByteArrayBigEndian B := by
    show _ = fromBytes' B.toList.reverse
    rw [byteArray_toList_eq]
  rw [hA, hB]
  show fromByteArrayBigEndian B + 2 ^ (8 * B.size) * fromByteArrayBigEndian A = _
  ring

/-- `fromBE` of any byte array is bounded by its length. -/
theorem fromBE_lt (b : ByteArray) :
    fromByteArrayBigEndian b < 2 ^ (8 * b.size) := by
  show fromBytes' b.toList.reverse < _
  have h := fromBytes'_lt b.toList.reverse
  rw [List.length_reverse, byteArray_toList_eq, Array.length_toList] at h
  rw [show b.data.size = b.size from rfl] at h
  rw [show b.toList = b.data.toList from byteArray_toList_eq b]
  exact h

theorem uInt256OfByteArray_toNat (b : ByteArray) (h : fromByteArrayBigEndian b < 2 ^ 256) :
    (uInt256OfByteArray b).toNat = fromByteArrayBigEndian b := by
  show (UInt256.ofNat (fromBytes' b.data.toList.reverse)).toNat = _
  have hk : fromBytes' b.data.toList.reverse = fromByteArrayBigEndian b := by
    show _ = fromBytes' b.toList.reverse
    rw [byteArray_toList_eq]
  rw [hk, uint256_ofNat_toNat_of_lt _ (by
    have : UInt256.size = 2 ^ 256 := by decide
    omega)]

/-- Splitting a byte array at an interior point. -/
theorem byteArray_split (b : ByteArray) (k : Nat) (hk : k ≤ b.size) :
    b = b.extract 0 k ++ b.extract k b.size := by
  apply ByteArray.ext
  rw [ByteArray.data_append, ByteArray.data_extract, ByteArray.data_extract]
  exact (array_extract_prefix_suffix b.data k hk).symm

/-- The two 16-byte halves of a stored word decode to `toNat / 2^128` and
    `toNat % 2^128`. -/
theorem toByteArray_halves (w : UInt256) :
    fromByteArrayBigEndian (w.toByteArray.extract 0 16) = w.toNat / 2 ^ 128
      ∧ fromByteArrayBigEndian (w.toByteArray.extract 16 32) = w.toNat % 2 ^ 128 := by
  have hsz : w.toByteArray.size = 32 := uint256_toByteArray_size w
  have hsplit := byteArray_split w.toByteArray 16 (by omega)
  rw [hsz] at hsplit
  have hwhole := fromBE_toByteArray w
  rw [hsplit, fromBE_append] at hwhole
  have hszB : (w.toByteArray.extract 16 32).size = 16 := by
    rw [ByteArray.size_extract, hsz]
    omega
  have hszA : (w.toByteArray.extract 0 16).size = 16 := by
    rw [ByteArray.size_extract, hsz]
    omega
  rw [hszB] at hwhole
  have hBlt := fromBE_lt (w.toByteArray.extract 16 32)
  rw [hszB] at hBlt
  have hAlt := fromBE_lt (w.toByteArray.extract 0 16)
  rw [hszA] at hAlt
  constructor
  · omega
  · omega


/-! ## General payload decomposition (any 16-aligned chunk pair) -/

private theorem foldl_chunks_acc (raw : RawSig) (xs : List Nat) (acc : ByteArray) :
    xs.foldl (fun acc i => acc ++ forsPayloadChunk raw i) acc =
      acc ++ xs.foldl (fun acc i => acc ++ forsPayloadChunk raw i) ByteArray.empty := by
  induction xs generalizing acc with
  | nil =>
    show acc = acc ++ ByteArray.empty
    apply ByteArray.ext
    rw [ByteArray.data_append]
    show acc.data = acc.data ++ #[]
    rw [Array.append_empty]
  | cons i xs ih =>
    rw [List.foldl_cons, ih (acc ++ forsPayloadChunk raw i),
      List.foldl_cons, ih (ByteArray.empty ++ forsPayloadChunk raw i)]
    apply ByteArray.ext
    simp [ByteArray.data_append, Array.append_assoc]

private theorem foldl_chunks_size (raw : RawSig) (xs : List Nat) :
    (xs.foldl (fun acc i => acc ++ forsPayloadChunk raw i) ByteArray.empty).size
      = 16 * xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.foldl_cons, foldl_chunks_acc, ByteArray.size_append,
      ByteArray.size_append, forsPayloadChunk_size, ih]
    show ByteArray.empty.size + 16 + 16 * xs.length = 16 * (xs.length + 1)
    show 0 + 16 + 16 * xs.length = 16 * (xs.length + 1)
    ring

/-- `forsPayload` split around chunks `k, k+1`. -/
private theorem forsPayload_decomp (raw : RawSig) (k : Nat) (hk : k + 2 ≤ 153) :
    forsPayload raw
      = ((List.range k).foldl (fun acc i => acc ++ forsPayloadChunk raw i)
          ByteArray.empty)
        ++ forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1)
        ++ (((List.range (153 - (k + 2))).map (fun i => k + 2 + i)).foldl
            (fun acc i => acc ++ forsPayloadChunk raw i) ByteArray.empty) := by
  have hsplit : List.range 153
      = List.range k ++ [k, k + 1]
        ++ ((List.range (153 - (k + 2))).map (fun i => k + 2 + i)) := by
    rw [show (153 : Nat) = k + (153 - k) from by omega, List.range_add]
    rw [show 153 - k = 2 + (153 - (k + 2)) from by omega, List.range_add]
    simp only [List.map_append, List.map_map, List.append_assoc]
    congr 1
    rw [show k + (2 + (153 - (k + 2))) - (k + 2) = 153 - (k + 2) from by omega,
      show List.range 2 = [0, 1] from by decide]
    simp only [List.map_cons, List.map_nil]
    show [k + 0, k + 1] ++ _ = [k, k + 1] ++ _
    rw [show k + 0 = k from by omega]
    congr 1
    apply List.map_congr_left
    intro a _
    show k + (2 + a) = k + 2 + a
    omega
  unfold forsPayload
  show (List.range 153).foldl (fun acc i => acc ++ forsPayloadChunk raw i)
      ByteArray.empty = _
  rw [hsplit, List.foldl_append, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_chunks_acc raw _
    ((((List.range k).foldl (fun acc i => acc ++ forsPayloadChunk raw i)
        ByteArray.empty) ++ forsPayloadChunk raw k) ++ forsPayloadChunk raw (k + 1))]

/-- The general chunk-pair window of the payload. -/
theorem forsPayload_extract_pair (raw : RawSig) (k : Nat) (hk : k + 2 ≤ 153) :
    (forsPayload raw).extract (16 * k) (16 * k + 32)
      = forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1) := by
  let P := (List.range k).foldl (fun acc i => acc ++ forsPayloadChunk raw i)
    ByteArray.empty
  let ck := forsPayloadChunk raw k
  let ck1 := forsPayloadChunk raw (k + 1)
  let T := ((List.range (153 - (k + 2))).map (fun i => k + 2 + i)).foldl
    (fun acc i => acc ++ forsPayloadChunk raw i) ByteArray.empty
  have hdec : forsPayload raw = P ++ ck ++ ck1 ++ T := forsPayload_decomp raw k hk
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append]
  rw [hdec]
  have hdata : (P ++ ck ++ ck1 ++ T).data
      = P.data ++ (ck.data ++ ck1.data) ++ T.data := by
    simp only [ByteArray.data_append, Array.append_assoc]
  rw [hdata]
  have hpre : P.data.size = 16 * k := by
    rw [show P.data.size = P.size from rfl]
    dsimp only [P]
    rw [foldl_chunks_size, List.length_range]
  have hck : ck.data.size = 16 := forsPayloadChunk_size raw k
  have hck1 : ck1.data.size = 16 := by
    show (forsPayloadChunk raw (k + 1)).data.size = 16
    rw [show (forsPayloadChunk raw (k + 1)).data.size
        = (forsPayloadChunk raw (k + 1)).size from rfl]
    exact forsPayloadChunk_size raw (k + 1)
  have hmid : (ck.data ++ ck1.data).size = 32 := by
    rw [Array.size_append, hck, hck1]
  rw [show 16 * k = P.data.size from hpre.symm]
  rw [show P.data.size + 32 = P.data.size + (ck.data ++ ck1.data).size from by
    rw [hmid]]
  exact extract_middle P.data (ck.data ++ ck1.data) T.data


/-! ## General calldata window lemmas (any 16-aligned chunk pair) -/

/-- General version of `encodeForsCalldata_extract_payload_pair_*`:
the 32-byte calldata window at ABI offset `100 + 16k` is the payload
window at offset `16k`. -/
theorem encodeForsCalldata_extract_payload_pair
    (raw : RawSig) (digest : Digest) (k : Nat) :
    (encodeForsCalldata raw digest).extract (100 + 16 * k) (100 + 16 * k + 32) =
      (forsPayload raw).extract (16 * k) (16 * k + 32) := by
  unfold encodeForsCalldata
  let pref := forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len
  have hprefix_size : pref.size = 100 := by
    dsimp [pref]
    simp [ByteArray.size_append, forsSelector_size, word32_size]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  have hdata :
      (forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len ++
          forsPayload raw).data =
        pref.data ++ (forsPayload raw).data := by
    dsimp [pref]
    simp [ByteArray.data_append, Array.append_assoc]
  rw [hdata]
  have hprefData : pref.data.size = 100 := hprefix_size
  have hright :
      (pref.data ++ (forsPayload raw).data).extract
          (100 + 16 * k) (100 + 16 * k + 32) =
        (forsPayload raw).data.extract
          (100 + 16 * k - pref.data.size) (100 + 16 * k + 32 - pref.data.size) :=
    Array.extract_append_right' (a := pref.data) (b := (forsPayload raw).data)
      (i := 100 + 16 * k) (j := 100 + 16 * k + 32) (by rw [hprefData]; omega)
  rw [hprefData] at hright
  rw [show 100 + 16 * k - 100 = 16 * k from by omega,
    show 100 + 16 * k + 32 - 100 = 16 * k + 32 from by omega] at hright
  exact hright

/-- General version of `encodeForsCalldata_readBytes_payload_pair_*`. -/
theorem encodeForsCalldata_readBytes_payload_pair
    (raw : RawSig) (digest : Digest) (k : Nat) (hk : k + 2 ≤ 153) :
    (encodeForsCalldata raw digest).readBytes (100 + 16 * k) 32 =
      forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1) := by
  rw [readBytes_window_32]
  · rw [encodeForsCalldata_extract_payload_pair]
    exact forsPayload_extract_pair raw k hk
  · have h64 : (2516 : Nat) < 2 ^ 64 := by norm_num
    omega
  · rw [encodeForsCalldata_size]
    omega

/-- General version of `encodeForsCalldata_uInt256_payload_pair_*`. -/
theorem encodeForsCalldata_uInt256_payload_pair
    (raw : RawSig) (digest : Digest) (k : Nat) (hk : k + 2 ≤ 153) :
    EvmYul.uInt256OfByteArray
        ((encodeForsCalldata raw digest).readBytes (100 + 16 * k) 32) =
      EvmYul.uInt256OfByteArray
        (forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1)) := by
  rw [encodeForsCalldata_readBytes_payload_pair raw digest k hk]

/-- General version of `calldataload_encode_payload_pair_*`: the EVM
`calldataload` at ABI offset `100 + 16k` decodes the chunk pair `(k, k+1)`. -/
theorem calldataload_encode_payload_pair (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul) (k : Nat) (hk : k + 2 ≤ 153)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    EvmYul.State.calldataload s (UInt256.ofNat (100 + 16 * k)) =
      EvmYul.uInt256OfByteArray
        (forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1)) := by
  unfold EvmYul.State.calldataload
  rw [uint256_ofNat_toNat_of_lt (100 + 16 * k) (by
    have hbig : (2516 : Nat) < UInt256.size := by norm_num [UInt256.size]
    omega)]
  rw [hcd]
  exact encodeForsCalldata_uInt256_payload_pair raw digest k hk


/-! ## Masked calldata reads recover packed raw-signature values -/

/-- Clearing the low 128 bits of `2^128 * a ||| r` (with `a, r < 2^128`)
    leaves `2^128 * a`. -/
private theorem nat_and_high128 (a r : Nat) (ha : a < 2 ^ 128) (hr : r < 2 ^ 128) :
    (2 ^ 128 * a + r) &&& (2 ^ 256 - 2 ^ 128) = 2 ^ 128 * a := by
  have hmask : (2 : Nat) ^ 256 - 2 ^ 128 = (2 ^ 128 - 1) <<< 128 := by
    rw [Nat.shiftLeft_eq]
    norm_num
  have hsh : 2 ^ 128 * a = a <<< 128 := by
    rw [Nat.shiftLeft_eq]
    ring
  rw [Nat.two_pow_add_eq_or_of_lt hr a, hmask, hsh]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 128 ≤ i
  · have hrbit : r.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) h))
    by_cases h2 : i - 128 < 128
    · simp [h, h2, hrbit]
    · have habit : a.testBit (i - 128) = false :=
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h, h2, hrbit, habit]
  · simp [h]

private theorem high_low_lt (q r : Nat) (hq : q < 2 ^ 128) (hr : r < 2 ^ 128) :
    q * 2 ^ 128 + r < 2 ^ 256 := by
  have h2 : (q + 1) * 2 ^ 128 ≤ 2 ^ 128 * 2 ^ 128 := mul_le_mul_right' hq (2 ^ 128)
  have h3 : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← pow_add]
  have h4 : (q + 1) * 2 ^ 128 = q * 2 ^ 128 + 2 ^ 128 := by ring
  omega

/-- A masked `calldataload` at ABI offset `100 + 16k` recovers the packed
    raw-signature value `raw.read16 (16 * k)`, provided that value is
    well-formed: packed (low 128 bits zero) and word-sized. -/
theorem masked_calldataload_read16 (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul) (k : Nat) (hk : k + 2 ≤ 153)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest)
    (hlow : raw.read16 (16 * k) % 2 ^ 128 = 0)
    (hlt : raw.read16 (16 * k) < 2 ^ 256) :
    ((EvmYul.State.calldataload s (UInt256.ofNat (100 + 16 * k))).land
        (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = raw.read16 (16 * k) := by
  have husz : UInt256.size = 2 ^ 256 := by decide
  rw [calldataload_encode_payload_pair raw digest s k hk hcd, uint256_land_toNat]
  have hmask : ((UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = 2 ^ 256 - 2 ^ 128 := by
    rw [show (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot
        = UInt256.ofNat
            0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
      from rfl]
    rw [uint256_ofNat_toNat_of_lt _ (by rw [husz]; norm_num)]
    norm_num
  have hq : raw.read16 (16 * k) / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by
      have h3 : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← pow_add]
      omega)
  have hchk : fromByteArrayBigEndian (forsPayloadChunk raw k)
      = raw.read16 (16 * k) / 2 ^ 128 := by
    rw [show forsPayloadChunk raw k
        = (UInt256.ofNat (raw.read16 (16 * k))).toByteArray.extract 0 16 from rfl]
    rw [(toByteArray_halves (UInt256.ofNat (raw.read16 (16 * k)))).1]
    rw [uint256_ofNat_toNat_of_lt _ (by rw [husz]; exact hlt)]
  have hszk1 : (forsPayloadChunk raw (k + 1)).size = 16 :=
    forsPayloadChunk_size raw (k + 1)
  have hr : fromByteArrayBigEndian (forsPayloadChunk raw (k + 1)) < 2 ^ 128 := by
    have h := fromBE_lt (forsPayloadChunk raw (k + 1))
    rw [hszk1] at h
    norm_num at h
    exact h
  have hcat : fromByteArrayBigEndian
        (forsPayloadChunk raw k ++ forsPayloadChunk raw (k + 1))
      = raw.read16 (16 * k) / 2 ^ 128 * 2 ^ 128
        + fromByteArrayBigEndian (forsPayloadChunk raw (k + 1)) := by
    rw [fromBE_append, hszk1, hchk]
  rw [uInt256OfByteArray_toNat _ (by
    rw [hcat]
    exact high_low_lt _ _ hq hr)]
  rw [hcat, hmask,
    show raw.read16 (16 * k) / 2 ^ 128 * 2 ^ 128
      = 2 ^ 128 * (raw.read16 (16 * k) / 2 ^ 128) from by ring,
    nat_and_high128 _ _ hq hr,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)]

/-- The final counter chunk is followed by ABI zero padding, so it cannot use the
    paired-payload lemma (`k + 2 ≤ 153` would fail at `k = 152`). The same
    high-128-bit mask still recovers the packed final `read16` word. -/
theorem masked_calldataload_counter_read16 (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest)
    (hlow : raw.read16 2432 % 2 ^ 128 = 0)
    (hlt : raw.read16 2432 < 2 ^ 256) :
    ((EvmYul.State.calldataload s (UInt256.ofNat 2532)).land
        (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = raw.read16 2432 := by
  let z : USize :=
    { toBitVec := (↑32 - ↑16 : BitVec System.Platform.numBits) }
  have husz : UInt256.size = 2 ^ 256 := by decide
  rw [calldataload_encode_counter raw digest s hcd]
  change ((EvmYul.uInt256OfByteArray (forsPayloadChunk raw 152 ++ ffi.ByteArray.zeroes z)).land
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat = raw.read16 2432
  rw [uint256_land_toNat]
  have hmask : ((UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
      = 2 ^ 256 - 2 ^ 128 := by
    rw [show (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot
        = UInt256.ofNat
            0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
      from rfl]
    rw [uint256_ofNat_toNat_of_lt _ (by rw [husz]; norm_num)]
    norm_num
  have hq : raw.read16 2432 / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by
      have h3 : (2 : Nat) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← pow_add]
      omega)
  have hchk : fromByteArrayBigEndian (forsPayloadChunk raw 152)
      = raw.read16 2432 / 2 ^ 128 := by
    rw [show forsPayloadChunk raw 152
        = (UInt256.ofNat (raw.read16 (16 * 152))).toByteArray.extract 0 16 from rfl]
    rw [(toByteArray_halves (UInt256.ofNat (raw.read16 (16 * 152)))).1]
    rw [show 16 * 152 = 2432 from by norm_num]
    rw [uint256_ofNat_toNat_of_lt _ (by rw [husz]; exact hlt)]
  have hpadSize : (ffi.ByteArray.zeroes z).size = 16 := by
    dsimp [z]
    rw [ffi_zeroes_size]
    change ((BitVec.ofNat System.Platform.numBits 32) -
      (BitVec.ofNat System.Platform.numBits 16)).toNat = 16
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rcases System.Platform.numBits_eq with hb | hb
    · rw [hb]
    · rw [hb]
  have hr : fromByteArrayBigEndian (ffi.ByteArray.zeroes z) < 2 ^ 128 := by
    have h := fromBE_lt (ffi.ByteArray.zeroes z)
    rw [hpadSize] at h
    norm_num at h
    exact h
  have hcat : fromByteArrayBigEndian
        (forsPayloadChunk raw 152 ++ ffi.ByteArray.zeroes z)
      = raw.read16 2432 / 2 ^ 128 * 2 ^ 128
        + fromByteArrayBigEndian (ffi.ByteArray.zeroes z) := by
    rw [fromBE_append, hpadSize, hchk]
  rw [uInt256OfByteArray_toNat _ (by
    rw [hcat]
    exact high_low_lt _ _ hq hr)]
  rw [hcat, hmask,
    show raw.read16 2432 / 2 ^ 128 * 2 ^ 128
      = 2 ^ 128 * (raw.read16 2432 / 2 ^ 128) from by ring,
    nat_and_high128 _ _ hq hr,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlow)]

/-- The loop's masked sibling/sk read, phrased via `treeMaskedCalldataWord`. -/
theorem treeMaskedCalldataWord_read16 (raw : RawSig) (digest : Digest)
    (s : EvmYul.Yul.State) (k : Nat) (hk : k + 2 ≤ 153)
    (hcd : s.toState.executionEnv.calldata = encodeForsCalldata raw digest)
    (hlow : raw.read16 (16 * k) % 2 ^ 128 = 0)
    (hlt : raw.read16 (16 * k) < 2 ^ 256) :
    (treeMaskedCalldataWord s (UInt256.ofNat (100 + 16 * k))).toNat
      = raw.read16 (16 * k) := by
  unfold treeMaskedCalldataWord
  exact masked_calldataload_read16 raw digest s.toState k hk hcd hlow hlt


/-! ## Well-formed raw signatures and the loop's closed-form reads -/

/-- The loop's masked sk read for tree `j` (at `ptr0 = 132`) is the
    raw-signature field at `treeOffset j = 32 + 96 j`. -/
theorem loopSk_read16 (raw : RawSig) (digest : Digest)
    (T : EvmYul.State .Yul) (j : Nat) (hj : j < 25)
    (hcd : T.executionEnv.calldata = encodeForsCalldata raw digest)
    (hwf : RawSigWellFormed raw) :
    (loopSk T 132 j).toNat = raw.read16 (32 + 96 * j) := by
  obtain ⟨hlow, hlt⟩ := hwf (2 + 6 * j) (by omega)
  unfold loopSk
  rw [show (132 + 96 * j : Nat) = 100 + 16 * (2 + 6 * j) from by ring,
    show (32 + 96 * j : Nat) = 16 * (2 + 6 * j) from by ring]
  exact masked_calldataload_read16 raw digest T (2 + 6 * j) (by omega) hcd hlow hlt

/-- The loop's masked auth-sibling read for tree `j` at byte offset `16 ℓ`
    (at `ptr0 = 132`) is the raw-signature field at
    `authOffset j (ℓ - 1) = 32 + 96 j + 16 ℓ`. -/
theorem loopSib_read16 (raw : RawSig) (digest : Digest)
    (T : EvmYul.State .Yul) (j ℓ : Nat) (hj : j < 25) (hℓ : 1 ≤ ℓ ∧ ℓ ≤ 5)
    (hcd : T.executionEnv.calldata = encodeForsCalldata raw digest)
    (hwf : RawSigWellFormed raw) :
    (loopSib T 132 j (16 * ℓ)).toNat = raw.read16 (32 + 96 * j + 16 * ℓ) := by
  obtain ⟨hlow, hlt⟩ := hwf (2 + 6 * j + ℓ) (by omega)
  unfold loopSib
  rw [show (132 + 96 * j + 16 * ℓ : Nat) = 100 + 16 * (2 + 6 * j + ℓ) from by ring,
    show (32 + 96 * j + 16 * ℓ : Nat) = 16 * (2 + 6 * j + ℓ) from by ring]
  exact masked_calldataload_read16 raw digest T (2 + 6 * j + ℓ) (by omega) hcd
    hlow hlt

end NiceTry.Fors.Bridge
