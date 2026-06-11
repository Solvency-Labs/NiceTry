import NiceTry.Fors.Bridge.TreeIter
import Mathlib.Data.Nat.Bitwise

/-!
# Tree-loop arithmetic layer (M2): selector and ADRS-word identities

Discharges `tree_iter_values`' arithmetic hypotheses from the A4 invariant
values (`usr_t = t`, `usr_tLeafBase = 32t`, `usr_dCursor = dVal >>> 5t`,
`ret = 32`, `ret_2 = 96`):

* `UInt256` `toNat` semantics for `land`/`lor`/`shiftLeft`/`shiftRight`;
* the swap selectors are single bits of `usr_dCursor`
  (`treeSelector<j>Word = 32 * bit j`), matched to the parity of
  `indexAt dVal t / 2^j`;
* the packed ADRS words are disjoint-bit sums equal to
  `shapeLeafAdrsWord`/`shapeNodeAdrsWord`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-! ## `UInt256` bit-op `toNat` semantics -/

private theorem usize_eq : UInt256.size = 2 ^ 256 := by decide

theorem uint256_land_toNat (a b : UInt256) :
    (a.land b).toNat = a.toNat &&& b.toNat := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  show (Fin.land ⟨av, ha⟩ ⟨bv, hb⟩).val = av &&& bv
  rw [Fin.land]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left ha)

theorem uint256_lor_toNat (a b : UInt256) :
    (a.lor b).toNat = a.toNat ||| b.toNat := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  show (Fin.lor ⟨av, ha⟩ ⟨bv, hb⟩).val = av ||| bv
  rw [Fin.lor]
  refine Nat.mod_eq_of_lt ?_
  rw [usize_eq] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb

theorem uint256_shiftRight_toNat (a b : UInt256) (h : b.toNat < 256) :
    (UInt256.shiftRight a b).toNat = a.toNat >>> b.toNat := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  have hb' : bv < 256 := h
  have hcond : ¬ ((⟨bv, hb⟩ : Fin UInt256.size) ≥ (256 : Fin UInt256.size)) := by
    rw [ge_iff_le, Fin.le_def]
    have h256 : (256 : Fin UInt256.size).val = 256 := by decide
    rw [h256]
    exact not_le.mpr hb' 
  unfold UInt256.shiftRight
  rw [if_neg hcond]
  show (Fin.shiftRight ⟨av, ha⟩ ⟨bv, hb⟩).val = av >>> bv
  rw [Fin.shiftRight]
  refine Nat.mod_eq_of_lt (lt_of_le_of_lt ?_ ha)
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

theorem uint256_shiftLeft_toNat (a b : UInt256) (h : b.toNat < 256) :
    (UInt256.shiftLeft a b).toNat = (a.toNat <<< b.toNat) % UInt256.size := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  have hb' : bv < 256 := h
  have hcond : ¬ ((⟨bv, hb⟩ : Fin UInt256.size) ≥ (256 : Fin UInt256.size)) := by
    rw [ge_iff_le, Fin.le_def]
    have h256 : (256 : Fin UInt256.size).val = 256 := by decide
    rw [h256]
    exact not_le.mpr hb' 
  unfold UInt256.shiftLeft
  rw [if_neg hcond]
  show (Fin.shiftLeft ⟨av, ha⟩ ⟨bv, hb⟩).val = (av <<< bv) % UInt256.size
  rw [Fin.shiftLeft]


theorem uint256_eq_of_toNat {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  obtain ⟨⟨av, ha⟩⟩ := a
  obtain ⟨⟨bv, hb⟩⟩ := b
  have hv : av = bv := h
  subst hv
  rfl

/-! ## The swap selectors are single bits of `usr_dCursor` -/

/-- Bit `5 - k` of `x`, extracted by the contract's `and(shl(k, x), 32)`. -/
theorem shl_land_32 (x k : Nat) (hk : k ≤ 5) :
    ((x <<< k) % 2 ^ 256) &&& 32 = 32 * ((x >>> (5 - k)) % 2) := by
  have h32 : (32 : Nat) = 2 ^ 5 := by norm_num
  rw [h32, Nat.and_two_pow]
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  simp only [show ((5 : Nat) < 256) = True by simp, decide_true, Bool.true_and,
    decide_eq_true hk, Nat.toNat_testBit]
  rw [Nat.shiftRight_eq_div_pow]
  ring


theorem treeSelector0Word_cases (s : EvmYul.Yul.State) (x : Nat)
    (hcur : s[dCursorId]!.toNat = x)
    (hret : s[retId]! = UInt256.ofNat 32) :
    (treeSelector0Word s = UInt256.ofNat 0 ∧ x % 2 = 0)
      ∨ (treeSelector0Word s = UInt256.ofNat 32 ∧ x % 2 ≠ 0) := by
  have hval : (treeSelector0Word s).toNat = 32 * (x % 2) := by
    unfold treeSelector0Word
    rw [hret, uint256_land_toNat,
      uint256_shiftLeft_toNat _ _ (by rw [show (UInt256.ofNat 5).toNat = 5 from
        uint256_ofNat_toNat_of_lt _ (by decide)]; omega),
      hcur,
      show (UInt256.ofNat 5).toNat = 5 from uint256_ofNat_toNat_of_lt _ (by decide),
      show (UInt256.ofNat 32).toNat = 32 from uint256_ofNat_toNat_of_lt _ (by decide),
      usize_eq, shl_land_32 x 5 (by omega)]
    rw [show (5 : Nat) - 5 = 0 from rfl, Nat.shiftRight_zero]
  rcases Nat.mod_two_eq_zero_or_one (x) with h | h
  · left
    refine ⟨uint256_eq_of_toNat ?_, h⟩
    rw [hval, h, show (UInt256.ofNat 0).toNat = 0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  · right
    refine ⟨uint256_eq_of_toNat ?_, by omega⟩
    rw [hval, h, show (UInt256.ofNat 32).toNat = 32 from
      uint256_ofNat_toNat_of_lt _ (by decide)]


theorem treeSelector1Word_cases (s : EvmYul.Yul.State) (x : Nat)
    (hcur : s[dCursorId]!.toNat = x)
    (hret : s[retId]! = UInt256.ofNat 32) :
    (treeSelector1Word s = UInt256.ofNat 0 ∧ x / 2 % 2 = 0)
      ∨ (treeSelector1Word s = UInt256.ofNat 32 ∧ x / 2 % 2 ≠ 0) := by
  have hval : (treeSelector1Word s).toNat = 32 * (x / 2 % 2) := by
    unfold treeSelector1Word
    rw [hret]
    rw [uint256_land_toNat, uint256_land_toNat, uint256_land_toNat,
      uint256_shiftLeft_toNat _ _ (by rw [show (UInt256.ofNat 4).toNat = 4 from
        uint256_ofNat_toNat_of_lt _ (by decide)]; omega),
      hcur,
      show (UInt256.ofNat 4).toNat = 4 from uint256_ofNat_toNat_of_lt _ (by decide),
      show ((UInt256.ofNat 31).lnot).toNat = 2 ^ 256 - 32 from by decide,
      show (UInt256.ofNat 480).toNat = 480 from
        uint256_ofNat_toNat_of_lt _ (by decide),
      show (UInt256.ofNat 32).toNat = 32 from uint256_ofNat_toNat_of_lt _ (by decide),
      usize_eq, Nat.and_assoc, Nat.and_assoc,
      show ((2 ^ 256 - 32 : Nat) &&& (480 &&& 32)) = 32 from by decide,
      shl_land_32 x 4 (by omega)]
    rw [show (5 : Nat) - 4 = 1 from rfl, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 2) with h | h
  · left
    refine ⟨uint256_eq_of_toNat ?_, h⟩
    rw [hval, h, show (UInt256.ofNat 0).toNat = 0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  · right
    refine ⟨uint256_eq_of_toNat ?_, by omega⟩
    rw [hval, h, show (UInt256.ofNat 32).toNat = 32 from
      uint256_ofNat_toNat_of_lt _ (by decide)]


theorem treeSelector2Word_cases (s : EvmYul.Yul.State) (x : Nat)
    (hcur : s[dCursorId]!.toNat = x)
    (hret : s[retId]! = UInt256.ofNat 32) :
    (treeSelector2Word s = UInt256.ofNat 0 ∧ x / 4 % 2 = 0)
      ∨ (treeSelector2Word s = UInt256.ofNat 32 ∧ x / 4 % 2 ≠ 0) := by
  have hval : (treeSelector2Word s).toNat = 32 * (x / 4 % 2) := by
    unfold treeSelector2Word
    rw [hret]
    rw [uint256_land_toNat, uint256_land_toNat, uint256_land_toNat,
      uint256_shiftLeft_toNat _ _ (by rw [show (UInt256.ofNat 3).toNat = 3 from
        uint256_ofNat_toNat_of_lt _ (by decide)]; omega),
      hcur,
      show (UInt256.ofNat 3).toNat = 3 from uint256_ofNat_toNat_of_lt _ (by decide),
      show ((UInt256.ofNat 31).lnot).toNat = 2 ^ 256 - 32 from by decide,
      show (UInt256.ofNat 224).toNat = 224 from
        uint256_ofNat_toNat_of_lt _ (by decide),
      show (UInt256.ofNat 32).toNat = 32 from uint256_ofNat_toNat_of_lt _ (by decide),
      usize_eq, Nat.and_assoc, Nat.and_assoc,
      show ((2 ^ 256 - 32 : Nat) &&& (224 &&& 32)) = 32 from by decide,
      shl_land_32 x 3 (by omega)]
    rw [show (5 : Nat) - 3 = 2 from rfl, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 4) with h | h
  · left
    refine ⟨uint256_eq_of_toNat ?_, h⟩
    rw [hval, h, show (UInt256.ofNat 0).toNat = 0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  · right
    refine ⟨uint256_eq_of_toNat ?_, by omega⟩
    rw [hval, h, show (UInt256.ofNat 32).toNat = 32 from
      uint256_ofNat_toNat_of_lt _ (by decide)]


theorem treeSelector3Word_cases (s : EvmYul.Yul.State) (x : Nat)
    (hcur : s[dCursorId]!.toNat = x)
    (hret : s[retId]! = UInt256.ofNat 32)
    (hret2 : s[ret2Id]! = UInt256.ofNat 96) :
    (treeSelector3Word s = UInt256.ofNat 0 ∧ x / 8 % 2 = 0)
      ∨ (treeSelector3Word s = UInt256.ofNat 32 ∧ x / 8 % 2 ≠ 0) := by
  have hval : (treeSelector3Word s).toNat = 32 * (x / 8 % 2) := by
    unfold treeSelector3Word
    rw [hret]
    rw [hret2]
    rw [uint256_land_toNat, uint256_land_toNat, uint256_land_toNat,
      uint256_shiftLeft_toNat _ _ (by rw [show (UInt256.ofNat 2).toNat = 2 from
        uint256_ofNat_toNat_of_lt _ (by decide)]; omega),
      hcur,
      show (UInt256.ofNat 2).toNat = 2 from uint256_ofNat_toNat_of_lt _ (by decide),
      show ((UInt256.ofNat 31).lnot).toNat = 2 ^ 256 - 32 from by decide,
      show (UInt256.ofNat 96).toNat = 96 from
        uint256_ofNat_toNat_of_lt _ (by decide),
      show (UInt256.ofNat 32).toNat = 32 from uint256_ofNat_toNat_of_lt _ (by decide),
      usize_eq, Nat.and_assoc, Nat.and_assoc,
      show ((2 ^ 256 - 32 : Nat) &&& (96 &&& 32)) = 32 from by decide,
      shl_land_32 x 2 (by omega)]
    rw [show (5 : Nat) - 2 = 3 from rfl, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 8) with h | h
  · left
    refine ⟨uint256_eq_of_toNat ?_, h⟩
    rw [hval, h, show (UInt256.ofNat 0).toNat = 0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  · right
    refine ⟨uint256_eq_of_toNat ?_, by omega⟩
    rw [hval, h, show (UInt256.ofNat 32).toNat = 32 from
      uint256_ofNat_toNat_of_lt _ (by decide)]


theorem treeSelector4Word_cases (s : EvmYul.Yul.State) (x : Nat)
    (hcur : s[dCursorId]!.toNat = x)
    (hret : s[retId]! = UInt256.ofNat 32) :
    (treeSelector4Word s = UInt256.ofNat 0 ∧ x / 16 % 2 = 0)
      ∨ (treeSelector4Word s = UInt256.ofNat 32 ∧ x / 16 % 2 ≠ 0) := by
  have hval : (treeSelector4Word s).toNat = 32 * (x / 16 % 2) := by
    unfold treeSelector4Word
    rw [hret]
    rw [uint256_land_toNat, uint256_land_toNat, uint256_land_toNat,
      uint256_shiftLeft_toNat _ _ (by rw [show (UInt256.ofNat 1).toNat = 1 from
        uint256_ofNat_toNat_of_lt _ (by decide)]; omega),
      hcur,
      show (UInt256.ofNat 1).toNat = 1 from uint256_ofNat_toNat_of_lt _ (by decide),
      show ((UInt256.ofNat 31).lnot).toNat = 2 ^ 256 - 32 from by decide,
      show (UInt256.ofNat 32).toNat = 32 from
        uint256_ofNat_toNat_of_lt _ (by decide),
      usize_eq, Nat.and_assoc, Nat.and_assoc,
      show ((2 ^ 256 - 32 : Nat) &&& (32 &&& 32)) = 32 from by decide,
      shl_land_32 x 1 (by omega)]
    rw [show (5 : Nat) - 1 = 4 from rfl, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (x / 16) with h | h
  · left
    refine ⟨uint256_eq_of_toNat ?_, h⟩
    rw [hval, h, show (UInt256.ofNat 0).toNat = 0 from
      uint256_ofNat_toNat_of_lt _ (by decide)]
  · right
    refine ⟨uint256_eq_of_toNat ?_, by omega⟩
    rw [hval, h, show (UInt256.ofNat 32).toNat = 32 from
      uint256_ofNat_toNat_of_lt _ (by decide)]

/-! ## The packed ADRS words are the model shape words -/

/-- The leaf ADRS word: `or(shl(128,3), or(32t, and(dCursor, 31)))`. -/
theorem treeLeafAdrsWord_eq (s : EvmYul.Yul.State) (t x : Nat) (ht : t < 25)
    (hbase : s[tLeafBaseId]! = UInt256.ofNat (32 * t))
    (hcur : s[dCursorId]!.toNat = x) :
    (treeLeafAdrsWord s[tLeafBaseId]! s[dCursorId]!).toNat
      = shapeLeafAdrsWord t (x % 32) := by
  unfold treeLeafAdrsWord shapeLeafAdrsWord ForsBaseWord
  rw [hbase, uint256_lor_toNat, uint256_lor_toNat, uint256_land_toNat,
    uint256_shiftLeft_toNat _ _ (by
      rw [show (UInt256.ofNat 128).toNat = 128 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    hcur,
    show (UInt256.ofNat 3).toNat = 3 from uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 128).toNat = 128 from uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 31).toNat = 31 from uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat (32 * t)).toNat = 32 * t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    usize_eq,
    Nat.mod_eq_of_lt (show (3 <<< 128 : Nat) < 2 ^ 256 by decide),
    show (31 : Nat) = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,
    show (32 * t : Nat) = 2 ^ 5 * t from by ring,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt x (by norm_num)) t,
    show (3 <<< 128 : Nat) = 2 ^ 128 * 3 from by decide,
    ← Nat.two_pow_add_eq_or_of_lt
      (show 2 ^ 5 * t + x % 32 < 2 ^ 128 from by
        have := Nat.mod_lt x (show 0 < 32 by norm_num)
        omega) 3]
  omega


/-- The level-1 node ADRS word. -/
theorem treeNodeAdrsWord1_eq (s : EvmYul.Yul.State) (t x : Nat) (ht : t < 25)
    (husrT : s[usrTId]! = UInt256.ofNat t)
    (hcur : s[dCursorId]!.toNat = x) :
    (treeNodeAdrsWord s 4 1 15 1020847100762815390390123822299599601664).toNat
      = shapeNodeAdrsWord t 1 (x / 2 ^ 1 % 2 ^ 4) := by
  unfold treeNodeAdrsWord shapeNodeAdrsWord ForsBaseWord HeightWord twoPow A
  rw [husrT, uint256_lor_toNat, uint256_lor_toNat, uint256_land_toNat,
    uint256_shiftLeft_toNat _ _ (by
      rw [show (UInt256.ofNat 4).toNat = 4 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    uint256_shiftRight_toNat _ _ (by
      rw [show (UInt256.ofNat 1).toNat = 1 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    hcur,
    show (UInt256.ofNat 4).toNat = 4 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 1).toNat = 1 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 15).toNat = 15 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat t).toNat = t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    show (UInt256.ofNat 1020847100762815390390123822299599601664).toNat = 1020847100762815390390123822299599601664 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    usize_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show t * 2 ^ 4 < 2 ^ 256 by omega),
    show (15 : Nat) = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,
    mul_comm t (2 ^ 4),
    ← Nat.two_pow_add_eq_or_of_lt
      (Nat.mod_lt (x / 2 ^ 1) (by norm_num)) t,
    Nat.lor_comm,
    show (1020847100762815390390123822299599601664 : Nat) = 2 ^ 32 * (3 * 2 ^ 96 + 1) from by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt
      (show 2 ^ 4 * t + x / 2 ^ 1 % 2 ^ 4 < 2 ^ 32 from by
        have := Nat.mod_lt (x / 2 ^ 1) (show 0 < 2 ^ 4 by norm_num)
        omega)
      (3 * 2 ^ 96 + 1)]
  omega


/-- The level-2 node ADRS word. -/
theorem treeNodeAdrsWord2_eq (s : EvmYul.Yul.State) (t x : Nat) (ht : t < 25)
    (husrT : s[usrTId]! = UInt256.ofNat t)
    (hcur : s[dCursorId]!.toNat = x) :
    (treeNodeAdrsWord s 3 2 7 1020847100762815390390123822303894568960).toNat
      = shapeNodeAdrsWord t 2 (x / 2 ^ 2 % 2 ^ 3) := by
  unfold treeNodeAdrsWord shapeNodeAdrsWord ForsBaseWord HeightWord twoPow A
  rw [husrT, uint256_lor_toNat, uint256_lor_toNat, uint256_land_toNat,
    uint256_shiftLeft_toNat _ _ (by
      rw [show (UInt256.ofNat 3).toNat = 3 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    uint256_shiftRight_toNat _ _ (by
      rw [show (UInt256.ofNat 2).toNat = 2 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    hcur,
    show (UInt256.ofNat 3).toNat = 3 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 2).toNat = 2 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 7).toNat = 7 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat t).toNat = t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    show (UInt256.ofNat 1020847100762815390390123822303894568960).toNat = 1020847100762815390390123822303894568960 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    usize_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show t * 2 ^ 3 < 2 ^ 256 by omega),
    show (7 : Nat) = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,
    mul_comm t (2 ^ 3),
    ← Nat.two_pow_add_eq_or_of_lt
      (Nat.mod_lt (x / 2 ^ 2) (by norm_num)) t,
    Nat.lor_comm,
    show (1020847100762815390390123822303894568960 : Nat) = 2 ^ 32 * (3 * 2 ^ 96 + 2) from by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt
      (show 2 ^ 3 * t + x / 2 ^ 2 % 2 ^ 3 < 2 ^ 32 from by
        have := Nat.mod_lt (x / 2 ^ 2) (show 0 < 2 ^ 3 by norm_num)
        omega)
      (3 * 2 ^ 96 + 2)]
  omega


/-- The level-3 node ADRS word. -/
theorem treeNodeAdrsWord3_eq (s : EvmYul.Yul.State) (t x : Nat) (ht : t < 25)
    (husrT : s[usrTId]! = UInt256.ofNat t)
    (hcur : s[dCursorId]!.toNat = x) :
    (treeNodeAdrsWord s 2 3 3 1020847100762815390390123822308189536256).toNat
      = shapeNodeAdrsWord t 3 (x / 2 ^ 3 % 2 ^ 2) := by
  unfold treeNodeAdrsWord shapeNodeAdrsWord ForsBaseWord HeightWord twoPow A
  rw [husrT, uint256_lor_toNat, uint256_lor_toNat, uint256_land_toNat,
    uint256_shiftLeft_toNat _ _ (by
      rw [show (UInt256.ofNat 2).toNat = 2 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    uint256_shiftRight_toNat _ _ (by
      rw [show (UInt256.ofNat 3).toNat = 3 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    hcur,
    show (UInt256.ofNat 2).toNat = 2 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 3).toNat = 3 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat t).toNat = t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    show (UInt256.ofNat 1020847100762815390390123822308189536256).toNat = 1020847100762815390390123822308189536256 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    usize_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show t * 2 ^ 2 < 2 ^ 256 by omega),
    show ∀ y : Nat, y &&& 3 = y % 2 ^ 2 from fun y => by
      rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod],
    mul_comm t (2 ^ 2),
    ← Nat.two_pow_add_eq_or_of_lt
      (Nat.mod_lt (x / 2 ^ 3) (by norm_num)) t,
    Nat.lor_comm,
    show (1020847100762815390390123822308189536256 : Nat) = 2 ^ 32 * (3 * 2 ^ 96 + 3) from by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt
      (show 2 ^ 2 * t + x / 2 ^ 3 % 2 ^ 2 < 2 ^ 32 from by
        have := Nat.mod_lt (x / 2 ^ 3) (show 0 < 2 ^ 2 by norm_num)
        omega)
      (3 * 2 ^ 96 + 3)]
  omega


/-- The level-4 node ADRS word. -/
theorem treeNodeAdrsWord4_eq (s : EvmYul.Yul.State) (t x : Nat) (ht : t < 25)
    (husrT : s[usrTId]! = UInt256.ofNat t)
    (hcur : s[dCursorId]!.toNat = x) :
    (treeNodeAdrsWord s 1 4 1 1020847100762815390390123822312484503552).toNat
      = shapeNodeAdrsWord t 4 (x / 2 ^ 4 % 2 ^ 1) := by
  unfold treeNodeAdrsWord shapeNodeAdrsWord ForsBaseWord HeightWord twoPow A
  rw [husrT, uint256_lor_toNat, uint256_lor_toNat, uint256_land_toNat,
    uint256_shiftLeft_toNat _ _ (by
      rw [show (UInt256.ofNat 1).toNat = 1 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    uint256_shiftRight_toNat _ _ (by
      rw [show (UInt256.ofNat 4).toNat = 4 from
        uint256_ofNat_toNat_of_lt _ (by decide)]
      omega),
    hcur,
    show (UInt256.ofNat 1).toNat = 1 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat 4).toNat = 4 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    show (UInt256.ofNat t).toNat = t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    show (UInt256.ofNat 1020847100762815390390123822312484503552).toNat = 1020847100762815390390123822312484503552 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    usize_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show t * 2 ^ 1 < 2 ^ 256 by omega),
    show ∀ y : Nat, y &&& 1 = y % 2 ^ 1 from fun y => by
      rw [Nat.and_one_is_mod]; norm_num,
    mul_comm t (2 ^ 1),
    ← Nat.two_pow_add_eq_or_of_lt
      (Nat.mod_lt (x / 2 ^ 4) (by norm_num)) t,
    Nat.lor_comm,
    show (1020847100762815390390123822312484503552 : Nat) = 2 ^ 32 * (3 * 2 ^ 96 + 4) from by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt
      (show 2 ^ 1 * t + x / 2 ^ 4 % 2 ^ 1 < 2 ^ 32 from by
        have := Nat.mod_lt (x / 2 ^ 4) (show 0 < 2 ^ 1 by norm_num)
        omega)
      (3 * 2 ^ 96 + 4)]
  omega


/-- The level-5 node ADRS word `or(usr_t, C5)`. -/
theorem treeNode5AdrsWord_eq (s : EvmYul.Yul.State) (t : Nat) (ht : t < 25)
    (husrT : s[usrTId]! = UInt256.ofNat t) :
    (s[usrTId]!.lor
        (UInt256.ofNat 1020847100762815390390123822316779470848)).toNat
      = shapeNodeAdrsWord t 5 0 := by
  unfold shapeNodeAdrsWord ForsBaseWord HeightWord twoPow A
  rw [husrT, uint256_lor_toNat,
    show (UInt256.ofNat t).toNat = t from
      uint256_ofNat_toNat_of_lt _ (by rw [usize_eq]; omega),
    show (UInt256.ofNat 1020847100762815390390123822316779470848).toNat
        = 1020847100762815390390123822316779470848 from
      uint256_ofNat_toNat_of_lt _ (by decide),
    Nat.lor_comm,
    show (1020847100762815390390123822316779470848 : Nat)
        = 2 ^ 32 * (3 * 2 ^ 96 + 5) from by norm_num,
    ← Nat.two_pow_add_eq_or_of_lt (show t < 2 ^ 32 from by omega) (3 * 2 ^ 96 + 5)]
  omega


/-! ## The assembled arithmetic interface for A4 -/

/-- **All six hash values of one iteration, from the loop-invariant values.**
    `t` is the tree counter, `x = usr_dCursor`'s value (`= dVal >>> 5t` in the
    loop), and the leaf index is `x % 32 = indexAt dVal t`. -/
theorem tree_iter_values_of_invariant
    (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore) (pkSeed : UInt256)
    (t x idx : Nat) (ht : t < 25) (hidx : idx = x % 32)
    (hpk : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.data.extract 0x380 0x3a0
            = pkSeed.toByteArray.data)
    (hsize : 0x3a0 ≤ (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size)
    (hcur : (EvmYul.Yul.State.Ok ss vs)[dCursorId]!.toNat = x)
    (husrT : (EvmYul.Yul.State.Ok ss vs)[usrTId]! = UInt256.ofNat t)
    (hbase : (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]! = UInt256.ofNat (32 * t))
    (hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 32)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96) :
    (treeLeafNodeWord (.Ok ss vs)).toNat
        = leafHash pkSeed.toNat (leafAdrs t idx)
            (treeSkWord (.Ok ss vs)).toNat
      ∧ (treeNode1Word (treeAfterLeafHash (.Ok ss vs))).toNat
        = climbLevel pkSeed.toNat t 1 idx
            (treeLeafNodeWord (.Ok ss vs)).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 16))).toNat
      ∧ (treeNode2Word (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))).toNat
        = climbLevel pkSeed.toNat t 2 (idx / 2)
            (treeNode1Word (treeAfterLeafHash (.Ok ss vs))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add
                (EvmYul.Yul.State.Ok ss vs)[retId]!)).toNat
      ∧ (treeNode3Word (treeAfterNode2 (treeAfterNode1
            (treeAfterLeafHash (.Ok ss vs))))).toNat
        = climbLevel pkSeed.toNat t 3 (idx / 2 / 2)
            (treeNode2Word (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 48))).toNat
      ∧ (treeNode4Word (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
            (treeAfterLeafHash (.Ok ss vs)))))).toNat
        = climbLevel pkSeed.toNat t 4 (idx / 2 / 2 / 2)
            (treeNode3Word (treeAfterNode2 (treeAfterNode1
              (treeAfterLeafHash (.Ok ss vs))))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 64))).toNat
      ∧ (treeRootWord (treeAfterSibling5 (treeAfterNode4 (treeAfterNode3
            (treeAfterNode2 (treeAfterNode1 (treeAfterLeafHash (.Ok ss vs)))))))).toNat
        = climbLevel pkSeed.toNat t 5 (idx / 2 / 2 / 2 / 2)
            (treeNode4Word (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
              (treeAfterLeafHash (.Ok ss vs)))))).toNat
            (treeMaskedCalldataWord (.Ok ss vs)
              ((EvmYul.Yul.State.Ok ss vs)[treePtrId]!.add (UInt256.ofNat 80))).toNat := by
  subst hidx
  refine tree_iter_values ss vs pkSeed t (x % 32) hpk hsize hlen ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact treeLeafAdrsWord_eq (.Ok ss vs) t x ht hbase hcur
  · have h := treeSelector0Word_cases (.Ok ss vs) x hcur hret
    rwa [show x % 2 = x % 32 % 2 from by omega] at h
  · have h := treeNodeAdrsWord1_eq (.Ok ss vs) t x ht husrT hcur
    rwa [show x / 2 ^ 1 % 2 ^ 4 = x % 32 / 2 from by omega] at h
  · have h := treeSelector1Word_cases (.Ok ss vs) x hcur hret
    rwa [show x / 2 % 2 = x % 32 / 2 % 2 from by omega] at h
  · have h := treeNodeAdrsWord2_eq (.Ok ss vs) t x ht husrT hcur
    rwa [show x / 2 ^ 2 % 2 ^ 3 = x % 32 / 2 / 2 from by omega] at h
  · have h := treeSelector2Word_cases (.Ok ss vs) x hcur hret
    rwa [show x / 4 % 2 = x % 32 / 2 / 2 % 2 from by omega] at h
  · have h := treeNodeAdrsWord3_eq (.Ok ss vs) t x ht husrT hcur
    rwa [show x / 2 ^ 3 % 2 ^ 2 = x % 32 / 2 / 2 / 2 from by omega] at h
  · have h := treeSelector3Word_cases (.Ok ss vs) x hcur hret hlen
    rwa [show x / 8 % 2 = x % 32 / 2 / 2 / 2 % 2 from by omega] at h
  · have h := treeNodeAdrsWord4_eq (.Ok ss vs) t x ht husrT hcur
    rwa [show x / 2 ^ 4 % 2 ^ 1 = x % 32 / 2 / 2 / 2 / 2 from by omega] at h
  · have h := treeSelector4Word_cases (.Ok ss vs) x hcur hret
    rwa [show x / 16 % 2 = x % 32 / 2 / 2 / 2 / 2 % 2 from by omega] at h
  · have h := treeNode5AdrsWord_eq (.Ok ss vs) t ht husrT
    rwa [show (0 : Nat) = x % 32 / 2 / 2 / 2 / 2 / 2 from by omega] at h

end NiceTry.Fors.Bridge
