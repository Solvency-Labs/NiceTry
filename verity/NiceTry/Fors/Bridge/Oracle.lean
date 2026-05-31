import NiceTry.Fors.Proofs.Basic

/-!
# Step 4 — SoLean verifier-oracle composition

SoLean (`SoLean/Examples/PQVerifierWrapper.lean`) models the PQ verifier as an
abstract boolean oracle on its `Env`:

    Env.verifier : UInt256 → UInt256 → UInt256 → UInt256 → Bool   -- pk msg domain sig

and the wrapper, after checking lengths + domain, `require`s `verifier … = true`.
This file gives the FORS+C side of that interface: a concrete boolean acceptance
predicate backed by the proved recovery model, and the lemma that discharges it.

What is proved here (compiles against the existing closed proofs):
* `forsOracle_discharge` — a legit raw signature recovers the expected address.
* `forsAccept_of_legit`  — the boolean oracle accepts exactly that case.

What is *documented, not proved* (the interface contract SoLean still owes):
the representation refinement `UInt256 → {Address, RawSig, Digest}`. SoLean's
`signature : UInt256` is a placeholder; a faithful link needs SoLean to carry the
2448-byte `RawSig` and an `Address`/`Digest` decoding. See `INTERFACE` below.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors
open NiceTry.Fors.Spec
open NiceTry.Fors.Proofs.Basic

/-- The recovery result is the FORS verifier's observable output. -/
theorem forsOracle_discharge
    (raw : RawSig) (digest : Digest) (pkRoot : Hash16)
    (h : RawLegitSignatureFor raw digest pkRoot) :
    ∃ sig : TypedSig, decodeRaw raw = some sig ∧
      recoverRaw? raw digest = some (addressFromRoot sig.pkSeed pkRoot) := by
  obtain ⟨sig, hlen, hdecode, hlegit⟩ := h
  exact ⟨sig, hdecode,
    legit_raw_signature_recovers_expected_address raw digest sig pkRoot hlen hdecode hlegit⟩

/--
Boolean acceptance predicate matching the *shape* of SoLean's `Env.verifier`:
the verifier accepts iff recovery yields the expected signer. In the AA wallet
model the "public key" is the rotated owner address, so the FORS public key is
exactly `expectedSigner` (no separate pk channel; domain is pinned to `FORS_DOM`).
-/
def forsAccept (expectedSigner : Address) (raw : RawSig) (digest : Digest) : Bool :=
  recoverRaw? raw digest == some expectedSigner

/-- The boolean oracle accepts the legit case — this is what discharges
    `require (verify …)` in `PQVerifierWrapper.verifyProgram`. -/
theorem forsAccept_of_legit
    (raw : RawSig) (digest : Digest) (sig : TypedSig) (pkRoot : Hash16)
    (hlen : raw.len = SigLen)
    (hdecode : decodeRaw raw = some sig)
    (hlegit : LegitSignatureFor sig digest pkRoot) :
    forsAccept (addressFromRoot sig.pkSeed pkRoot) raw digest = true := by
  unfold forsAccept
  rw [legit_raw_signature_recovers_expected_address raw digest sig pkRoot hlen hdecode hlegit]
  simp

/-!
## INTERFACE — what SoLean instantiates, and the refinement it owes

SoLean instantiates its abstract oracle as

    env.verifier pk msg domain sig  :=  forsAccept (toAddress pk) (toRawSig sig) (toDigest msg)

pinning `domain = FORS_DOM`. Then `PQVerifierWrapper.verify_success_properties`
(which concludes `env.verifier … = true`) composes with `forsAccept_of_legit` to
give: a successful wrapper run implies a legit FORS+C signature recovered the
owner address.

Refinement SoLean still owes (representation gap, not a FORS-side gap):
* `toRawSig : UInt256 → RawSig` — SoLean's `signature : UInt256` must become the
  real 2448-byte `RawSig` (its `read16` offset discipline). Until then the link is
  at the *modeled* level, not byte-level.
* `toAddress`, `toDigest` — `UInt256 → Address`/`Digest` (truncation/identity).

These belong to SoLean's model upgrade; the FORS theorems above are stated so the
discharge is immediate once that refinement lands.
-/

end NiceTry.Fors.Bridge
