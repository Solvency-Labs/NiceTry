import NiceTry.Fors.Bridge.TreePreLoop

/-!
# `fun_recover` pre-loop statement trace (body[18:32])

This file runs the interpreter through `fun_recover`'s pre-loop prefix — the hmsg
construction (statements 18–24), the forced-zero guard skip (25), and the five
loop-variable initializations (26–31) — landing at the `for`-loop entry state and
discharging `LoopInv 0` for `tree_loop_run_from_zero`.

The hmsg window is built by five `mstore`s on a 96-byte entry memory (the recover
entry inherits the dispatcher's `mstore(64, 0x80)` free-memory pointer write — and,
equivalently, the bare `runForsRecover` entry differs only below `0xa0`, all of
which these stores overwrite). Slots 0–2 land in-bounds; slots 3–4 are padding
stores that grow memory to exactly `0xa0`. `hmsg_window_after_5` carries that
threading once.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

/-! ## The five-store hmsg window over a 96-byte entry -/

private theorem o0_toNat : (UInt256.ofNat 0).toNat = 0 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o20_toNat : (UInt256.ofNat 0x20).toNat = 0x20 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o40_toNat : (UInt256.ofNat 0x40).toNat = 0x40 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o60_toNat : (UInt256.ofNat 0x60).toNat = 0x60 :=
  uint256_ofNat_toNat_of_lt _ (by decide)
private theorem o80_toNat : (UInt256.ofNat 128).toNat = 128 :=
  uint256_ofNat_toNat_of_lt _ (by decide)

/-- The state after the five hmsg `mstore`s, abbreviated. -/
def hmsgMem (m : MachineState) (w0 w1 w2 w3 w4 : UInt256) : MachineState :=
  ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
    (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).mstore
    (UInt256.ofNat 128) w4

/-- Sizes through the five-store chain over a 96-byte entry. -/
private theorem hmsg_sizes (m : MachineState) (w0 w1 w2 w3 _w4 : UInt256)
    (hsize : m.memory.size = 96) :
    (m.mstore (UInt256.ofNat 0) w0).memory.size = 96
    ∧ ((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).memory.size = 96
    ∧ (((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
        (UInt256.ofNat 0x40) w2).memory.size = 96
    ∧ ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
        (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).memory.size = 128 := by
  have s1 : (m.mstore (UInt256.ofNat 0) w0).memory.size = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o0_toNat, hsize]; try omega), hsize]
  have s2 : ((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).memory.size
      = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o20_toNat, s1]; try omega), s1]
  have s3 : (((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
      (UInt256.ofNat 0x40) w2).memory.size = 96 := by
    rw [mstore_memory_size _ _ _ (by rw [o40_toNat, s2]; try omega), s2]
  have s4 : ((((m.mstore (UInt256.ofNat 0) w0).mstore (UInt256.ofNat 0x20) w1).mstore
      (UInt256.ofNat 0x40) w2).mstore (UInt256.ofNat 0x60) w3).memory.size = 128 := by
    rw [mstore_pad_size _ _ _ (by rw [o60_toNat, s3]) (by rw [o60_toNat]; decide),
      o60_toNat]
  exact ⟨s1, s2, s3, s4⟩

/-- The five hmsg `mstore`s over a 96-byte entry write the transcript window
    `[0, 0xa0)` as the five words and leave memory at size `0xa0`. -/
theorem hmsg_window_after_5 (m : MachineState) (w0 w1 w2 w3 w4 : UInt256)
    (hsize : m.memory.size = 96) :
    (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x00 0x20 = w0.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x20 0x40 = w1.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x40 0x60 = w2.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x60 0x80 = w3.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x80 0xa0 = w4.toByteArray.data
    ∧ (hmsgMem m w0 w1 w2 w3 w4).memory.size = 0xa0 := by
  obtain ⟨s1, s2, s3, s4⟩ := hmsg_sizes m w0 w1 w2 w3 w4 hsize
  set m1 := m.mstore (UInt256.ofNat 0) w0 with hm1
  set m2 := m1.mstore (UInt256.ofNat 0x20) w1 with hm2
  set m3 := m2.mstore (UInt256.ofNat 0x40) w2 with hm3
  set m4 := m3.mstore (UInt256.ofNat 0x60) w3 with hm4
  have hb0 : (UInt256.ofNat 0).toNat + 32 ≤ m.memory.size := by rw [o0_toNat, hsize]; try omega
  have hb1 : (UInt256.ofNat 0x20).toNat + 32 ≤ m1.memory.size := by rw [o20_toNat, s1]; try omega
  have hb2 : (UInt256.ofNat 0x40).toNat + 32 ≤ m2.memory.size := by rw [o40_toNat, s2]; try omega
  have hpad3 : m3.memory.size ≤ (UInt256.ofNat 0x60).toNat := by rw [o60_toNat, s3]
  have hpad4 : m4.memory.size ≤ (UInt256.ofNat 128).toNat := by rw [o80_toNat, s4]
  have hsmall3 : (UInt256.ofNat 0x60).toNat < 2 ^ 32 := by rw [o60_toNat]; decide
  have hsmall4 : (UInt256.ofNat 128).toNat < 2 ^ 32 := by rw [o80_toNat]; decide
  -- Final state size
  have hszF : (hmsgMem m w0 w1 w2 w3 w4).memory.size = 0xa0 := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.size = 0xa0
    rw [mstore_pad_size _ _ _ hpad4 hsmall4, o80_toNat]
  -- Slot 0: [0, 0x20)
  have e0 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x00 0x20 = w0.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x00 0x20 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (by left; rw [o40_toNat]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb1 (by left; rw [o20_toNat]; try omega)]
    have h := mstore_extract_self m (UInt256.ofNat 0) w0 hb0
    rw [o0_toNat] at h
    exact h
  -- Slot 1: [0x20, 0x40)
  have e1 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x20 0x40 = w1.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x20 0x40 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    rw [mstore_extract_disjoint _ _ _ _ _ hb2 (by left; rw [o40_toNat]; try omega)]
    have h := mstore_extract_self m1 (UInt256.ofNat 0x20) w1 hb1
    rw [o20_toNat] at h
    exact h
  -- Slot 2: [0x40, 0x60)
  have e2 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x40 0x60 = w2.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x40 0x60 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    rw [mstore_pad_extract_below _ _ _ _ _ hpad3 (by rw [s3]; try omega)]
    have h := mstore_extract_self m2 (UInt256.ofNat 0x40) w2 hb2
    rw [o40_toNat] at h
    exact h
  -- Slot 3: [0x60, 0x80)
  have e3 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x60 0x80 = w3.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x60 0x80 = _
    rw [mstore_pad_extract_below _ _ _ _ _ hpad4 (by rw [s4]; try omega)]
    have h := mstore_pad_extract_self m3 (UInt256.ofNat 0x60) w3 hpad3 hsmall3
    rw [o60_toNat] at h
    exact h
  -- Slot 4: [0x80, 0xa0)
  have e4 : (hmsgMem m w0 w1 w2 w3 w4).memory.data.extract 0x80 0xa0 = w4.toByteArray.data := by
    show (m4.mstore (UInt256.ofNat 128) w4).memory.data.extract 0x80 0xa0 = _
    have h := mstore_pad_extract_self m4 (UInt256.ofNat 128) w4 hpad4 hsmall4
    rw [o80_toNat] at h
    exact h
  exact ⟨e0, e1, e2, e3, e4, hszF⟩

end NiceTry.Fors.Bridge
