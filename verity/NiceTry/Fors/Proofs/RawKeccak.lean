import NiceTry.Fors.RawKeccak

namespace NiceTry.Fors

theorem rawOpeningFields_eq : RawOpeningFields = 6 := by
  rfl

theorem rawOpeningOffset_eq (tree field : Nat) :
    rawOpeningOffset tree field = SectionOffset + tree * TreeLen + field * N := by
  rfl

theorem first_rawOpeningOffset_eq :
    rawOpeningOffset 0 0 = 32 := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, N]

theorem second_tree_rawOpeningOffset_eq :
    rawOpeningOffset 1 0 = 128 := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, A, N]

theorem first_tree_last_auth_rawOpeningOffset_eq :
    rawOpeningOffset 0 5 = 112 := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, N]

theorem last_tree_rawOpeningOffset_eq :
    rawOpeningOffset 24 0 = 2336 := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, A, N]

theorem last_tree_last_auth_rawOpeningOffset_eq :
    rawOpeningOffset 24 5 = 2416 := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, A, N]

theorem raw_opening_region_ends_at_counter :
    rawOpeningOffset 24 5 + N = CounterOffset := by
  simp [rawOpeningOffset, SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen,
    TreeLen, CounterOffset, SectionLen, RealTrees, K, A, N]

theorem rawOpenings_first (raw : RawSig) :
    rawOpenings raw 0 = raw.read16 32 := by
  simp [rawOpenings, rawOpeningAt, rawOpeningOffset, RawOpeningFields,
    SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, N]

theorem rawOpenings_last (raw : RawSig) :
    rawOpenings raw 149 = raw.read16 2416 := by
  simp [rawOpenings, rawOpeningAt, rawOpeningOffset, RawOpeningFields,
    SectionOffset, PkSeedOffset, PkSeedLen, ROffset, RLen, TreeLen, A, N]

theorem rawOpenings_sk_eq_decodeOpening_sk (raw : RawSig) (tree : TreeIndex) :
    openingSk (rawOpenings raw) tree.val = (decodeOpening raw tree).sk := by
  simp [openingSk, openingWord, rawOpenings, rawOpeningAt, rawOpeningOffset,
    decodeOpening, readHash16, treeOffset, RawOpeningFields, SectionOffset,
    TreeLen, N]

theorem rawOpenings_auth_eq_decodeOpening_auth
    (raw : RawSig) (tree : TreeIndex) (level : AuthLevel) :
    openingAuth (rawOpenings raw) tree.val level.val =
      (decodeOpening raw tree).auth level := by
  have hlevel : level.val + 1 < 6 := by
    have hltA : level.val < A := level.isLt
    have hA : A = 5 := rfl
    omega
  have hdiv : (tree.val * 6 + (level.val + 1)) / 6 = tree.val := by
    rw [Nat.mul_comm tree.val 6]
    rw [Nat.mul_add_div (by decide : 0 < 6)]
    rw [Nat.div_eq_of_lt hlevel]
    omega
  have hmod : (tree.val * 6 + (level.val + 1)) % 6 = level.val + 1 := by
    rw [Nat.mul_comm tree.val 6]
    rw [Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt hlevel
  simp [openingAuth, openingWord, rawOpenings, rawOpeningAt, rawOpeningOffset,
    decodeOpening, readHash16, authOffset, treeOffset, RawOpeningFields,
    SectionOffset, TreeLen, N, hdiv, hmod]
  rw [show (level.val + 1) * 16 = 16 + level.val * 16 by omega]
  congr 1
  omega

theorem rawOpenings_treeOpening_eq_decodeTyped_opening
    (raw : RawSig) (tree : TreeIndex) :
    ({ sk := openingSk (rawOpenings raw) tree.val,
       auth := fun level => openingAuth (rawOpenings raw) tree.val level.val } : TreeOpening) =
      (decodeTyped raw).openings tree := by
  simp only [decodeTyped]
  rw [TreeOpening.mk.injEq]
  constructor
  · exact rawOpenings_sk_eq_decodeOpening_sk raw tree
  · funext level
    exact rawOpenings_auth_eq_decodeOpening_auth raw tree level

theorem reconstructTree_rawOpenings_eq_decodeTyped
    (raw : RawSig) (dVal : Word) (tree : TreeIndex) :
    reconstructTree (raw.read16 PkSeedOffset) tree (indexAt dVal tree.val)
        ({ sk := openingSk (rawOpenings raw) tree.val,
           auth := fun level => openingAuth (rawOpenings raw) tree.val level.val } : TreeOpening) =
      reconstructTree (decodeTyped raw).pkSeed tree (indexAt dVal tree.val)
        ((decodeTyped raw).openings tree) := by
  rw [rawOpenings_treeOpening_eq_decodeTyped_opening raw tree]
  rfl

theorem memoryRecoverRaw_bad_length
    (raw : RawSig)
    (digest : Nat)
    (h : Not (raw.len = SigLen)) :
    memoryRecoverRaw? raw digest = none := by
  simp [memoryRecoverRaw?, h]

theorem memoryRecoverRaw_good_length
    (raw : RawSig)
    (digest : Nat)
    (h : raw.len = SigLen) :
    memoryRecoverRaw? raw digest =
      memoryRecoverTyped?
        (raw.read16 ROffset)
        (raw.read16 PkSeedOffset)
        digest
        (raw.read16 CounterOffset)
        (rawOpenings raw) := by
  simp [memoryRecoverRaw?, h]

end NiceTry.Fors
