import EvmYul.MachineStateOps
import Mathlib.Data.Array.Extract
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

/-- Overwrite `source` (a full word) **within** existing memory — `destAddr+len`
    inside `dest` — splicing it between the untouched prefix and tail. This is the
    real-contract `mstore` (memory is already populated), vs `byteArray_write_append`
    which grows memory at the end. -/
theorem byteArray_write_overwrite
    (source dest : ByteArray) (destAddr len : Nat)
    (hlen : len = source.size) (hpos : 0 < len) (hbound : destAddr + len ≤ dest.size) :
    (ByteArray.write source 0 dest destAddr len).data
      = dest.data.extract 0 destAddr ++ source.data
          ++ dest.data.extract (destAddr + len) dest.size := by
  subst hlen
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  have hds : dest.data.size = dest.size := rfl
  have hss : source.data.size = source.size := rfl
  have hz0 : ({ toBitVec := (↑(0 : Nat)) } : USize).toNat = 0 := by simp [USize.toNat]
  have hmin : min dest.size (destAddr + source.size) = destAddr + source.size := by omega
  have hdpl : destAddr - dest.size = 0 := by omega
  simp only [ByteArray.copySlice, ByteArray.data_append, Nat.sub_zero, Nat.min_self,
    hmin, Nat.sub_self, hdpl, zeroes_data_nil hz0, Array.append_empty, hss, hds,
    Nat.zero_add, Nat.add_zero]
  rw [Array.extract_eq_self_of_le (Nat.le_of_eq hss)]

/-- Reading a prefix `[0, n)` of a larger memory back is `dest.extract 0 n` — what
    `keccak256(0, n)` sees when `n ≤ size`. Generalizes `readWithPadding_exact`. -/
theorem readWithPadding_prefix (s : ByteArray) (n : Nat)
    (hn : n ≤ s.size) (h0 : 0 < s.size) (hlt : n < 2 ^ 64) :
    s.readWithPadding 0 n = s.extract 0 n := by
  have hds : s.data.size = s.size := rfl
  have hr : s.readWithoutPadding 0 n = s.extract 0 n := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by omega)]
    apply ByteArray.ext
    simp only [Nat.zero_add, ByteArray.data_extract]
    congr 1
    omega
  have hrs : (s.extract 0 n).size = n := by
    simp only [ByteArray.size_extract]; omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  simp only [hr]
  have hz : ({ toBitVec := (↑n - ↑(s.extract 0 n).size : BitVec System.Platform.numBits) } : USize).toNat = 0 := by
    rw [hrs]; simp
  rw [ffi_zeroes_eq_empty _ hz, byteArray_append_empty]

/-- Reading an in-bounds memory window `[start, start+n)` gives that exact slice.
    This is the nonzero-offset companion to `readWithPadding_prefix`, used for
    the leaf/node scratch region at `0x380`. -/
theorem readWithPadding_window (s : ByteArray) (start n : Nat)
    (hbound : start + n ≤ s.size) (hpos : 0 < n) (hlt : n < 2 ^ 64) :
    s.readWithPadding start n = s.extract start (start + n) := by
  have hstart : start < s.size := by omega
  have hnsize : n ≤ s.size := by omega
  have hr : s.readWithoutPadding start n = s.extract start (start + n) := by
    unfold ByteArray.readWithoutPadding
    rw [if_neg (by omega)]
    rw [Nat.min_eq_left hnsize]
  have hrs : (s.extract start (start + n)).size = n := by
    simp only [ByteArray.size_extract]
    omega
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  simp only [hr]
  have hz : ({ toBitVec := (↑n - ↑(s.extract start (start + n)).size :
      BitVec System.Platform.numBits) } : USize).toNat = 0 := by
    rw [hrs]
    simp
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

/-- Reading the first `A.size + B.size` elements of `A ++ B ++ C` drops the tail
    `C` — used to extract the keccak-input window out of a larger memory. -/
theorem extract_two_prefix {α} (A B C : Array α) (n : Nat) (hn : n = A.size + B.size) :
    (A ++ B ++ C).extract 0 n = A ++ B := by
  subst hn
  have h1 : (A ++ B).size = A.size + B.size := Array.size_append
  rw [Array.extract_append, Array.extract_eq_self_of_le (Nat.le_of_eq h1),
      Array.extract_empty_of_stop_le_start (by rw [h1]; omega), Array.append_empty]

/-- Reading `A ++ B` plus a prefix of `C` out of `A ++ B ++ C`. -/
theorem extract_three_prefix {α} (A B C : Array α) (n : Nat) :
    (A ++ B ++ C).extract 0 (A.size + B.size + n) = A ++ B ++ C.extract 0 n := by
  rw [show A ++ B ++ C = (A ++ B) ++ C by rw [Array.append_assoc]]
  rw [Array.extract_append]
  have hAB : (A ++ B).size = A.size + B.size := Array.size_append
  rw [Array.extract_eq_self_of_le (by rw [hAB]; omega)]
  rw [show 0 - (A ++ B).size = 0 by omega]
  rw [show A.size + B.size + n - (A ++ B).size = n by rw [hAB]; omega]

/-- Reading the middle `B` out of `A ++ B ++ C`. -/
theorem extract_middle {α} (A B C : Array α) :
    (A ++ B ++ C).extract A.size (A.size + B.size) = B := by
  rw [show A ++ B ++ C = A ++ (B ++ C) by rw [Array.append_assoc]]
  rw [Array.extract_append_right' (a := A) (b := B ++ C)
    (i := A.size) (j := A.size + B.size) (by omega)]
  rw [show A.size - A.size = 0 by omega]
  rw [show A.size + B.size - A.size = B.size by omega]
  rw [Array.extract_append_left' (a := B) (b := C) (i := 0) (j := B.size) (by omega)]
  exact Array.extract_eq_self_of_le (by omega)

/-- Splitting an array at `n` into prefix and suffix gives the original array. -/
theorem array_extract_prefix_suffix {α} (a : Array α) (n : Nat) (hn : n ≤ a.size) :
    a.extract 0 n ++ a.extract n a.size = a := by
  apply Array.ext
  · simp only [Array.size_append, Array.size_extract]
    omega
  · intro i h1 h2
    by_cases hi : i < n
    · rw [Array.getElem_append_left (show i < (a.extract 0 n).size by
        simp only [Array.size_extract]; omega)]
      rw [Array.getElem_extract]
      congr
      omega
    · rw [Array.getElem_append_right (show (a.extract 0 n).size ≤ i by
        simp only [Array.size_extract]; omega)]
      rw [Array.getElem_extract]
      congr
      simp only [Array.size_extract]
      omega

/-- Extracting from a suffix-to-end shifts the start by the suffix offset. -/
theorem extract_after_extract_to_end {α} (a : Array α) {start stop off : Nat}
    (hstart : start ≤ stop) (hstop : stop ≤ a.size) (hoff : off ≤ stop - start) :
    (a.extract start stop).extract off (stop - start) = a.extract (start + off) stop := by
  apply Array.ext
  · simp only [Array.size_extract]
    omega
  · intro i hi hfull
    simp only [Array.size_extract] at hi hfull
    rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
    congr 1
    omega

/-- Extracting a bounded window from a slice shifts both endpoints by the slice start. -/
theorem extract_after_extract_window {α} (a : Array α) {start stop off len : Nat}
    (hstart : start ≤ stop) (hstop : stop ≤ a.size) (hoff : off + len ≤ stop - start) :
    (a.extract start stop).extract off (off + len) =
      a.extract (start + off) (start + off + len) := by
  apply Array.ext
  · simp only [Array.size_extract]
    omega
  · intro i hi hfull
    simp only [Array.size_extract] at hi hfull
    rw [Array.getElem_extract, Array.getElem_extract, Array.getElem_extract]
    congr 1
    omega

/-- Concatenated `.data` of a list of byte arrays. -/
def concatData : List ByteArray → Array UInt8
  | [] => #[]
  | w :: ws => w.data ++ concatData ws

/-- `concatData` over 32-byte words is exactly `32 * length` bytes. -/
theorem concatData_size (ws : List ByteArray) (hsz : ∀ w ∈ ws, w.size = 32) :
    (concatData ws).size = 32 * ws.length := by
  induction ws with
  | nil => simp [concatData]
  | cons w ws ih =>
      have hw : w.size = 32 := hsz w (List.mem_cons_self ..)
      have hwd : w.data.size = 32 := hw
      have hsz' : ∀ x ∈ ws, x.size = 32 :=
        fun x hx => hsz x (List.mem_cons_of_mem _ hx)
      rw [concatData, Array.size_append, ih hsz', hwd]
      simp only [List.length_cons]
      omega

/-- Write a list of 32-byte words consecutively, each appended at the current end
    of memory — the general `mstore(0,w₀); mstore(0x20,w₁); …` choreography. -/
def writeWords32 : List ByteArray → ByteArray → ByteArray
  | [], mem => mem
  | w :: ws, mem => writeWords32 ws (ByteArray.write w 0 mem mem.size 32)

/-- The bytes after an n-word append are `mem ‖ w₀ ‖ w₁ ‖ …` — the inductive
    generalization of `two_word_writes`, reusable for every multi-word transcript
    (hmsg, leaf, node, roots). -/
theorem writeWords32_data (ws : List ByteArray) (mem : ByteArray)
    (hsz : ∀ w ∈ ws, w.size = 32) :
    (writeWords32 ws mem).data = mem.data ++ concatData ws := by
  induction ws generalizing mem with
  | nil => simp [writeWords32, concatData]
  | cons w ws ih =>
    have hw : w.size = 32 := hsz w (List.mem_cons_self ..)
    have hstep : (ByteArray.write w 0 mem mem.size 32).data = mem.data ++ w.data :=
      byteArray_write_append w mem mem.size 32 rfl hw.symm (by omega)
    have hsz' : ∀ x ∈ ws, x.size = 32 := fun x hx => hsz x (List.mem_cons_of_mem _ hx)
    show (writeWords32 ws (ByteArray.write w 0 mem mem.size 32)).data = _
    rw [ih _ hsz', concatData, hstep, Array.append_assoc]

/-- Write a list of 32-byte words consecutively starting at a fixed offset,
    overwriting an existing memory window. -/
def writeWords32At : Nat → List ByteArray → ByteArray → ByteArray
  | _, [], mem => mem
  | offset, w :: ws, mem =>
      writeWords32At (offset + 32) ws (ByteArray.write w 0 mem offset 32)

/-- The bytes after an n-word overwrite are
    `prefix ‖ w₀ ‖ w₁ ‖ … ‖ suffix`. This is the write-over-existing-memory
    companion to `writeWords32_data`, for the real contract choreography where
    hmsg/leaf/node/roots reuse already-populated memory. -/
theorem writeWords32At_data (ws : List ByteArray) (mem : ByteArray) (offset : Nat)
    (hsz : ∀ w ∈ ws, w.size = 32)
    (hbound : offset + 32 * ws.length ≤ mem.size) :
    (writeWords32At offset ws mem).data =
      mem.data.extract 0 offset ++ concatData ws ++
        mem.data.extract (offset + 32 * ws.length) mem.size := by
  induction ws generalizing mem offset with
  | nil =>
      simp only [writeWords32At, concatData, List.length_nil, Nat.mul_zero]
      exact (array_extract_prefix_suffix mem.data offset (by simpa using hbound)).symm
  | cons w ws ih =>
      have hw : w.size = 32 := hsz w (List.mem_cons_self ..)
      have hsz' : ∀ x ∈ ws, x.size = 32 :=
        fun x hx => hsz x (List.mem_cons_of_mem _ hx)
      have hbound_cons : offset + (32 * ws.length + 32) ≤ mem.size := by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound
      have hwrite_bound : offset + 32 ≤ mem.size := by omega
      have hmd : mem.data.size = mem.size := rfl
      have hprefix_size : (mem.data.extract 0 offset).size = offset := by
        rw [Array.size_extract]
        rw [show min offset mem.data.size = offset by rw [hmd]; omega]
        simp
      have htail0_size :
          (mem.data.extract (offset + 32) mem.size).size = mem.size - (offset + 32) := by
        rw [Array.size_extract]
        rw [show min mem.size mem.data.size = mem.size by rw [hmd]; simp]
      let mem1 := ByteArray.write w 0 mem offset 32
      have hstep : mem1.data = mem.data.extract 0 offset ++ w.data ++
          mem.data.extract (offset + 32) mem.size := by
        dsimp [mem1]
        exact byteArray_write_overwrite w mem offset 32 hw.symm (by omega) hwrite_bound
      have hmem1size : mem1.size = mem.size := by
        show mem1.data.size = mem.size
        rw [hstep]
        have hwd : w.data.size = 32 := hw
        rw [Array.size_append, Array.size_append, hprefix_size, hwd, htail0_size]
        omega
      have hbound' : offset + 32 + 32 * ws.length ≤ mem1.size := by
        rw [hmem1size]
        omega
      show (writeWords32At (offset + 32) ws mem1).data = _
      rw [ih mem1 (offset + 32) hsz' hbound']
      rw [hstep, hmem1size]
      have hwd : w.data.size = 32 := hw
      have hpref :
          Array.extract
            (mem.data.extract 0 offset ++ w.data ++ mem.data.extract (offset + 32) mem.size)
            0 (offset + 32)
            = mem.data.extract 0 offset ++ w.data := by
        exact extract_two_prefix _ _ _ (offset + 32) (by rw [hprefix_size, hwd])
      have htail :
          Array.extract
            (mem.data.extract 0 offset ++ w.data ++ mem.data.extract (offset + 32) mem.size)
            (offset + 32 + 32 * ws.length) mem.size
            = mem.data.extract (offset + 32 + 32 * ws.length) mem.size := by
        let A := mem.data.extract 0 offset
        let B := w.data
        let C := mem.data.extract (offset + 32) mem.size
        change (A ++ B ++ C).extract (offset + 32 + 32 * ws.length) mem.size =
          mem.data.extract (offset + 32 + 32 * ws.length) mem.size
        have hAB : (A ++ B).size = offset + 32 := by
          dsimp [A, B]
          rw [Array.size_append, hprefix_size, hwd]
        have hC : C.size = mem.size - (offset + 32) := by
          dsimp [C]
          exact htail0_size
        have hstart_eq : offset + 32 + 32 * ws.length = (A ++ B).size + 32 * ws.length := by
          rw [hAB]
        have hstop_eq : mem.size = (A ++ B).size + C.size := by
          rw [hAB, hC]
          omega
        rw [hstart_eq, hstop_eq]
        rw [Array.extract_append_right' (a := A ++ B) (b := C)
          (i := (A ++ B).size + 32 * ws.length)
          (j := (A ++ B).size + C.size) (by omega)]
        rw [show (A ++ B).size + 32 * ws.length - (A ++ B).size = 32 * ws.length by omega]
        rw [show (A ++ B).size + C.size - (A ++ B).size = C.size by omega]
        rw [show (A ++ B).size + 32 * ws.length = offset + 32 + 32 * ws.length by rw [hAB]]
        rw [show (A ++ B).size + C.size = mem.size by exact hstop_eq.symm]
        change C.extract (32 * ws.length) C.size =
          mem.data.extract (offset + 32 + 32 * ws.length) mem.size
        rw [hC]
        dsimp [C]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (extract_after_extract_to_end mem.data (start := offset + 32) (stop := mem.size)
            (off := 32 * ws.length) (by omega) (by rw [hmd]) (by omega))
      rw [hpref, htail]
      simp only [concatData, List.length_cons]
      have hoff : offset + 32 * (ws.length + 1) = offset + 32 + 32 * ws.length := by
        omega
      rw [hoff]
      simp only [Array.append_assoc]

/-- In-bounds fixed-offset 32-byte overwrites preserve total memory size. -/
theorem writeWords32At_size (ws : List ByteArray) (mem : ByteArray) (offset : Nat)
    (hsz : ∀ w ∈ ws, w.size = 32)
    (hbound : offset + 32 * ws.length ≤ mem.size) :
    (writeWords32At offset ws mem).size = mem.size := by
  have hdata := writeWords32At_data ws mem offset hsz hbound
  have hconcat : (concatData ws).size = 32 * ws.length := concatData_size ws hsz
  have hprefix : (mem.data.extract 0 offset).size = offset := by
    have hmd : mem.data.size = mem.size := rfl
    rw [Array.size_extract]
    rw [show min offset mem.data.size = offset by rw [hmd]; omega]
    simp
  have htail :
      (mem.data.extract (offset + 32 * ws.length) mem.size).size =
        mem.size - (offset + 32 * ws.length) := by
    have hmd : mem.data.size = mem.size := rfl
    rw [Array.size_extract]
    rw [show min mem.size mem.data.size = mem.size by rw [hmd]; simp]
  show (writeWords32At offset ws mem).data.size = mem.size
  rw [hdata]
  rw [Array.size_append, Array.size_append, hprefix, hconcat, htail]
  omega

/-- Reading back the overwritten window after `writeWords32At` gives exactly the
    concatenated word bytes. This is the reusable Class-M keccak-input lemma for
    fixed-size transcript shapes. -/
theorem writeWords32At_readWithPadding_data
    (ws : List ByteArray) (mem : ByteArray) (offset : Nat)
    (hsz : ∀ w ∈ ws, w.size = 32)
    (hbound : offset + 32 * ws.length ≤ mem.size)
    (hpos : 0 < ws.length) (hlt : 32 * ws.length < 2 ^ 64) :
    ((writeWords32At offset ws mem).readWithPadding offset (32 * ws.length)).data =
      concatData ws := by
  have hdata := writeWords32At_data ws mem offset hsz hbound
  have hconcat : (concatData ws).size = 32 * ws.length := concatData_size ws hsz
  have hprefix : (mem.data.extract 0 offset).size = offset := by
    have hmd : mem.data.size = mem.size := rfl
    rw [Array.size_extract]
    rw [show min offset mem.data.size = offset by rw [hmd]; omega]
    simp
  have htail :
      (mem.data.extract (offset + 32 * ws.length) mem.size).size =
        mem.size - (offset + 32 * ws.length) := by
    have hmd : mem.data.size = mem.size := rfl
    rw [Array.size_extract]
    rw [show min mem.size mem.data.size = mem.size by rw [hmd]; simp]
  have hsize : (writeWords32At offset ws mem).size = mem.size := by
    show (writeWords32At offset ws mem).data.size = mem.size
    rw [hdata]
    rw [Array.size_append, Array.size_append, hprefix, hconcat, htail]
    omega
  rw [readWithPadding_window _ offset (32 * ws.length)
    (by rw [hsize]; exact hbound) (by omega) hlt]
  rw [ByteArray.data_extract, hdata]
  have hm :
      (mem.data.extract 0 offset ++ concatData ws ++
          mem.data.extract (offset + 32 * ws.length) mem.size).extract offset
          (offset + 32 * ws.length) = concatData ws := by
    let A := mem.data.extract 0 offset
    let B := concatData ws
    let C := mem.data.extract (offset + 32 * ws.length) mem.size
    change (A ++ B ++ C).extract offset (offset + 32 * ws.length) = B
    have hA : A.size = offset := by
      dsimp [A]
      exact hprefix
    have hB : B.size = 32 * ws.length := by
      dsimp [B]
      exact hconcat
    rw [show offset = A.size by rw [hA]]
    rw [show A.size + 32 * ws.length = A.size + B.size by rw [hB]]
    exact extract_middle _ _ _
  exact hm

end NiceTry.Fors.Bridge
