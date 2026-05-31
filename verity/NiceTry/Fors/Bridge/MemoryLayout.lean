import NiceTry.Fors.FullKeccak

/-!
# Step 3 / obligations #9, #10 — Class-C memory-layout facts

Decidable arithmetic backing the contract's three compile-time `_GUARD` constants
and the choreography claim "25 roots at `0x40 + 32·t`, scratch at `0x380+`,
non-overlap". Proven and **axiom-free** (no `native_decide`), so they count toward
a no-`assumed` bar. They compose into `full_verifier_memory_refinement` once the
Class-M byte-level lemmas land.

Model layout constants live in `Fors/FullKeccak.lean`:
`RootBufferStart = 0x40`, `RootsHashLen = (K+1)·32 = 0x360`, `HMsgHashLen = 0xa0`,
`AddressHashLen = 0x40`; the asm scratch base `0x380` is `ScratchBase` here.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors

/-- Tree-hashing scratch base in `ForsVerifier.sol` (`FORS_SCRATCH_OFFSET = 0x380`). -/
def ScratchBase : Nat := 0x380

/-- `FORS_A_UNROLL_GUARD`: the A=5 unroll precondition. -/
theorem guard_A_unroll : A = 5 := rfl

/-- `FORS_SCRATCH_ALIGN_GUARD`: scratch base is 64-byte aligned. -/
theorem guard_scratch_align : ScratchBase % 64 = 0 := by decide

/-- `FORS_SCRATCH_OVERLAP_GUARD`: scratch starts at/after the roots-hash input region. -/
theorem guard_scratch_no_overlap : RootsHashLen ≤ ScratchBase := by decide

/-- The roots buffer occupies exactly `[0x40, 0x360)` — 25 contiguous 32-byte words. -/
theorem rootsRegion_end_eq : RootBufferStart + RealTrees * 32 = RootsHashLen := by decide

/-- Root `t` is written at `0x40 + 32·t` (matches the asm `rootPtr := 0x40 + 0x20·t`). -/
theorem rootBufferWrite_offset (pkSeed dVal : Nat) (openings : Nat → Nat) (t : Nat) :
    (rootBufferWrite pkSeed dVal openings t).offset = RootBufferStart + t * 32 := rfl

/-- Every real root slot ends at/below the scratch base — roots and scratch never overlap. -/
theorem rootBuffer_below_scratch (t : Nat) (ht : t < RealTrees) :
    RootBufferStart + t * 32 + 32 ≤ ScratchBase := by
  have hr : RealTrees = 25 := rfl
  rw [hr] at ht
  unfold RootBufferStart ScratchBase
  omega

/-- Distinct trees write to distinct root slots — no aliasing in the roots buffer. -/
theorem rootBuffer_offset_injective
    (pkSeed dVal : Nat) (openings : Nat → Nat) (t t' : Nat)
    (h : (rootBufferWrite pkSeed dVal openings t).offset
        = (rootBufferWrite pkSeed dVal openings t').offset) : t = t' := by
  have h1 := rootBufferWrite_offset pkSeed dVal openings t
  have h2 := rootBufferWrite_offset pkSeed dVal openings t'
  rw [h1, h2] at h
  omega

/-- The Hmsg input region `[0, 0xa0)` sits entirely below scratch. -/
theorem hmsg_below_scratch : HMsgHashLen ≤ ScratchBase := by decide

/-- The address-derivation input region `[0, 0x40)` sits entirely below scratch. -/
theorem address_below_scratch : AddressHashLen ≤ ScratchBase := by decide

end NiceTry.Fors.Bridge
