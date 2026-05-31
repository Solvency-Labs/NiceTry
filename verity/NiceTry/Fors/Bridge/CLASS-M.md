# Class-M architecture & findings (the EVM↔model memory bridge)

Result of spiking the Class-M layer against real EVMYulLean. Two findings reshape
the plan; both are honest TCB facts Antonio should see.

## Finding 1 — three layers, two gaps (the model isn't end-to-end)

The FORS model has **two opaque keccak families that are never related**:

```
EVM execution            model memory layer            model transcript layer
ffi.KEC(readWithPadding  →  keccakWordFromMemory     →  keccakWord
        memory)             (KeccakMemoryCall)           (List TranscriptField)
                                                         ↑ all proved theorems here
```

* **Gap A (EVM ↔ memory-call):** the `mstore` sequence in `ForsVerifier.sol`
  produces a memory whose region equals a given `KeccakMemoryCall`'s writes. This
  is what the 10 `keccak_memory_refinement` `local_obligations` assert.
* **Gap B (memory-call ↔ transcript):** `keccakWordFromMemory (hMsgMemoryCall …)`
  = `keccakWord (hMsgTranscript …)`, etc. This encodes the 16-byte top-half
  masking (`FORS_TOP_N_MASK`) and is **currently unproved in the model** — neither
  layer references the other. The proved main theorem lives entirely in the
  transcript layer, so without Gap B the EVM result never reaches it.

Plan must close **both** A and B, then compose with the proved
`legit_raw_signature_recovers_expected_address`.

## Finding 2 — the EVM memory model is not kernel-reducible

`mstore` → `writeWord` → `ByteArray.write`, and `UInt256.toByteArray`, both call
`ffi.ByteArray.zeroes : USize → ByteArray`, which is `@[extern] opaque` (no body).
`ffi.KEC` likewise. EVMYulLean ships **zero** lemmas about memory/`ByteArray.write`/
`readWithPadding` and has no Proofs dir. So Gap-A byte reasoning is from scratch on
top of a trusted spec for the opaque primitives.

Minimal trusted layer (`EvmFfiSpec.lean`, built): `ffi_zeroes_size`,
`ffi_zeroes_get!`, `ffi_zeroes_zero`. Total-correctness specs of memory padding,
not crypto. Plus the existing trusted `ffi.KEC` (keccak).

## The decision: how to close Gap A

* **(i) Prove byte-level (max rigor).** From `EvmFfiSpec` + core `ByteArray`
  (`extract`/`++`/`copySlice`/`.data` Array ops, all reducible) prove
  `readWithPadding (after the mstores) off len = encode(writes)`. Largest effort —
  needs a from-scratch `ByteArray.write`/`readWithPadding` lemma library (word
  round-trip, adjacent-write composition, non-overlap from `MemoryLayout.lean`).
  TCB = keccak + 3 zeroes axioms.
* **(ii) Axiomatize the per-keccak binding (pragmatic).** One auditable axiom per
  keccak shape: "running the kernel's `mstore` choreography then `keccak256 off len`
  yields `keccakWordFromMemory call`." Sidesteps `ByteArray` entirely; larger but
  mechanical TCB. Gap B still proved.

Recommendation: **(i)** — it's the reason route B is worth doing over route A, and
the byte library is reusable across all 5 transcript shapes. Fall back to (ii) per
shape if a specific proof proves intractable.

## Concrete next steps (route i)

1. `ByteArray` lemma library: `size_append`, `writeWord` size/`get`, single-word
   round-trip `read (writeWord m a v) a = v.toByteArray`, adjacent composition.
2. Gap-A per shape: address (2 writes) → leaf (3) → node (4) → hmsg (5) → roots (27).
   Start with address as the template.
3. Gap-B per shape: memory-call value list ↔ transcript field list, via the
   top-16 masking facts.
4. Compose A∘B with the proved transcript theorem into `RefinesModel evmRun`;
   flip the 12 `local_obligations` to `.proved`.

Layout side-conditions for step 2 non-overlap are already proved in
`MemoryLayout.lean`.
