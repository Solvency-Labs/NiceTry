import NiceTry.Fors.Bridge.EvmRun
import NiceTry.Fors.Bridge.AddressShape

/-!
# WS-4 — reduction of `ForsRefines` to three interpreter-execution facts

`ForsRefines` (`EvmRun.lean`) is the deployed-contract refinement target:

    ∀ raw digest, evmRun raw digest = (recoverRaw? raw digest).getD 0

This file does **all of the model-side glue** — the case analysis of `recoverRaw?`
(length check → `decodeRaw` → forced-zero grinding guard) and the `none ↔ address(0)`
correspondence (`.getD 0`) — and proves that `ForsRefines` reduces to exactly **three
facts about the interpreter run** (`forsRefines_of_branches`):

* `h_len`    — bad signature length ⇒ the contract returns `address(0)`;
* `h_guard`  — forced-zero guard fails ⇒ the contract returns `address(0)`;
* `h_accept` — otherwise the contract returns `addressFromRoot pkSeed (recoverRoot …)`.

These three are the **open execution obligations**; nothing here is `sorry` or a new
axiom (`#print axioms forsRefines_of_branches` = the AddressShape/FFI trust base only).

## How the three hypotheses get discharged (the remaining workstreams)

* `h_len` / `h_guard`  ⇐ **WS-1** (Class-A ABI parse): run `forsDispatcher` on
  `encodeForsCalldata`, hit the `iszero(eq(var_sig_length, expr))` / forced-zero
  `if and(shr(125,dVal),31)` branches that `RETURN address(0)`. The forced-zero shape
  is the proved model-side `forcedZero_eq_evm_shape`.
* `h_accept` ⇐ **WS-2 + WS-3**: the interpreter run produces a `MachineState` whose
  memory feeds the proved `AddressShape` handoffs —
  `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init` (its
  `hleaf/hnode1..5/hroot` premises are the tree-loop induction, WS-3) composed with
  `address_derivation_eq_overwrite` for the final `keccak256(0,0x40) & low160`.

`h_accept` is therefore the single consolidated target the multi-week loop proof
feeds; once the three hold, `ForsRefines` is closed by this theorem.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors
open NiceTry.Fors.Spec

/-- The grinding value the contract derives (`keccak256(0,0xa0)` in `fun_recover`),
    expressed on the decoded typed signature. Abbreviation to keep the obligation
    statements readable. -/
def dValOf (raw : RawSig) (digest : Digest) : Word :=
  hMsg (decodeTyped raw).pkSeed (decodeTyped raw).r digest (decodeTyped raw).counter

/-- Normal form of the model recovery as a nested `if` over the two guards, in
    `dValOf` vocabulary (so the main reduction is pure `if_pos`/`if_neg`). -/
theorem recoverRaw_eq (raw : RawSig) (digest : Digest) :
    recoverRaw? raw digest =
      (if raw.len = SigLen then
        (if forcedZero (dValOf raw digest) then
          some (addressFromRoot (decodeTyped raw).pkSeed
                  (recoverRoot (decodeTyped raw) (dValOf raw digest)))
         else none)
       else none) := by
  unfold recoverRaw? decodeRaw recoverTyped? dValOf
  by_cases h : raw.len = SigLen <;> simp [h]

/--
**WS-4 reduction.** `ForsRefines` follows from the three interpreter-execution facts.
The proof is the complete model-side decomposition: via `recoverRaw_eq` it case-
splits on the length and forced-zero guards and discharges the `none ↔ address(0)`
gap, leaving only the three execution obligations. No `sorry`, no new axiom.
-/
theorem forsRefines_of_branches
    (h_len : ∀ raw digest, raw.len ≠ SigLen → evmRun raw digest = 0)
    (h_guard : ∀ raw digest, raw.len = SigLen →
        forcedZero (dValOf raw digest) = false → evmRun raw digest = 0)
    (h_accept : ∀ raw digest, raw.len = SigLen →
        forcedZero (dValOf raw digest) = true →
        evmRun raw digest =
          addressFromRoot (decodeTyped raw).pkSeed
            (recoverRoot (decodeTyped raw) (dValOf raw digest))) :
    ForsRefines := by
  intro raw digest
  rw [recoverRaw_eq raw digest]
  by_cases hlen : raw.len = SigLen
  · rw [if_pos hlen]
    by_cases hfz : forcedZero (dValOf raw digest) = true
    · -- accept branch
      rw [if_pos hfz]
      simpa using h_accept raw digest hlen hfz
    · -- forced-zero reject branch
      have hfz' : forcedZero (dValOf raw digest) = false := by simpa using hfz
      rw [if_neg hfz]
      simpa using h_guard raw digest hlen hfz'
  · -- bad length: model rejects, contract returns address(0)
    rw [if_neg hlen]
    simpa using h_len raw digest hlen

end NiceTry.Fors.Bridge
