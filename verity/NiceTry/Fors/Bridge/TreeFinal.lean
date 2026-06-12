import NiceTry.Fors.Bridge.TreeLoop

/-!
# M4: post-loop assembly — the roots buffer as one concatenation

`tree_loop_run` leaves the 25 root slots `[0x40 + 32j, 0x40 + 32(j+1))`
individually characterized; the roots-compression keccak reads them as one
window. This file folds the per-slot extracts into the
`concatData (List.ofFn …)` form `roots_derivation_eq_from_buffer` consumes.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

set_option maxHeartbeats 2000000

theorem concatData_append (l₁ l₂ : List ByteArray) :
    concatData (l₁ ++ l₂) = concatData l₁ ++ concatData l₂ := by
  induction l₁ with
  | nil => simp [concatData]
  | cons w ws ih =>
    show w.data ++ concatData (ws ++ l₂) = w.data ++ concatData ws ++ concatData l₂
    rw [ih, Array.append_assoc]

/-- Folding `k` adjacent 32-byte slot extracts into one window extract. -/
theorem extract_slots_concat (M : MachineState) (rootsW : Nat → UInt256)
    (hslots : ∀ j, j < 25 →
      M.memory.data.extract (0x40 + 32 * j) (0x40 + 32 * j + 32)
        = (rootsW j).toByteArray.data)
    (hsize : 0x360 ≤ M.memory.size) :
    ∀ k, k ≤ 25 →
      M.memory.data.extract 0x40 (0x40 + 32 * k)
        = concatData ((List.ofFn (fun i : Fin k => rootsW i.val)).map
            UInt256.toByteArray) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [concatData]
  | succ k ih =>
    intro hk
    have hmd : M.memory.data.size = M.memory.size := rfl
    rw [extract_split M.memory.data 0x40 (0x40 + 32 * k) (0x40 + 32 * (k + 1))
        (by omega) (by omega) (by omega),
      ih (by omega),
      show 0x40 + 32 * (k + 1) = (0x40 + 32 * k) + 32 from by omega,
      hslots k (by omega),
      show (List.ofFn (fun i : Fin (k + 1) => rootsW i.val))
          = (List.ofFn (fun i : Fin k => rootsW i.val)) ++ [rootsW k] from by
        rw [List.ofFn_succ_last]
        rfl,
      List.map_append, concatData_append]
    rfl

/-- The full roots window in the handoff's `concatData (List.ofFn …)` form. -/
theorem roots_buffer_concat (M : MachineState) (rootsW : Nat → UInt256)
    (hslots : ∀ j, j < 25 →
      M.memory.data.extract (0x40 + 32 * j) (0x40 + 32 * j + 32)
        = (rootsW j).toByteArray.data)
    (hsize : 0x360 ≤ M.memory.size) :
    M.memory.data.extract RootBufferStart RootsHashLen
      = concatData ((List.ofFn (fun i : TreeIndex => rootsW i.val)).map
          UInt256.toByteArray) := by
  have h := extract_slots_concat M rootsW hslots hsize 25 (by omega)
  unfold RootBufferStart RootsHashLen K
  show M.memory.data.extract 0x40 864 = _
  rw [show (864 : Nat) = 0x40 + 32 * 25 from by omega]
  exact h

end NiceTry.Fors.Bridge
