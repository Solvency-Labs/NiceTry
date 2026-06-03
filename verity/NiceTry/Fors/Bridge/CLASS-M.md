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
`ffi_zeroes_get!`, `ffi_zeroes_eq_empty`. Total-correctness specs of memory
padding, not crypto. Plus trusted `ffi.KEC` (keccak).

Current Bridge shape status: Gap-A byte equality is proved for address, hmsg,
leaf, node, and the roots-compression buffer (with abstract per-tree root
values). Gap-B is still explicit trust, localized as labeled `evm_keccak_*`
axioms in `AddressShape.lean` (`address`, `hmsg`, `leaf`, `node`, `roots`).
These axioms bundle keccak correctness plus byte/value transcript encoding and
masking until the planned Gap-B split replaces the encoding parts with proof.
The FORS tree-climb loop still has to prove that the 25 abstract roots written
into the roots buffer are exactly the model roots. The post-loop handoff is now
named: establish `pkSeed` at `0x00` and the 25-root buffer at `0x40..0x35f`, then
`roots_derivation_eq_from_buffer` connects the real `compressRoots` call to the
model. The helper `roots_derivation_eq_after_loop_buffer_init` composes the
abstract root-buffer initialization, the memory-size preservation facts, and the
final `mstore(0x20, ADRS_roots); keccak256(0,0x360)` call; the remaining hard
work is proving that the root values supplied to that helper are produced by the
real FORS tree-climb loop. The sharper target is
`roots_derivation_eq_recoverRoot_after_loop_buffer_init`: prove the pointwise
premise `(roots t).toNat = reconstructTree ...` for each tree, and the bridge
rewrites the final roots compression all the way to `recoverRoot`.
`roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init` further
breaks that pointwise premise into the six per-tree hash results: leaf plus five
node levels. The per-node bridge lemmas
`node_derivation_eq_climbLevel_even_overwrite` and
`node_derivation_eq_climbLevel_odd_overwrite` package the sibling ordering needed
by those five node facts. The typed wrappers
`leaf_derivation_eq_model_leaf_overwrite` and
`node_derivation_eq_model_climbLevel_{even,odd}_overwrite` further rewrite the
EVM hash result directly into the `TypedSig`/`reconstructTree` vocabulary.
The root-buffer loop invariant now also has a prefix form,
`roots_loop_buffer_prefix_after_init`, for proving the 25-iteration roots write
loop incrementally.

## The decision: how to close Gap A

* **(i) Prove byte-level (max rigor).** From `EvmFfiSpec` + core `ByteArray`
  (`extract`/`++`/`copySlice`/`.data` Array ops, all reducible) prove
  `readWithPadding (after the mstores) off len = encode(writes)`. Largest effort —
  needs a from-scratch `ByteArray.write`/`readWithPadding` lemma library (word
  round-trip, adjacent-write composition, non-overlap from `MemoryLayout.lean`).
  TCB = keccak/transcript bridge axioms + 3 zeroes axioms.
* **(ii) Axiomatize the per-keccak binding (pragmatic).** One auditable axiom per
  keccak shape: "running the kernel's `mstore` choreography then `keccak256 off len`
  yields `keccakWordFromMemory call`." Sidesteps `ByteArray` entirely; larger but
  mechanical TCB. Gap B still proved.

Recommendation: **(i)** — it's the reason route B is worth doing over route A, and
the byte library is reusable across all 5 transcript shapes. Fall back to (ii) per
shape if a specific proof proves intractable.

## Concrete next steps (route i)

> **Status update:** steps 1–3 below are now **done** (the `ByteArray` library,
> Gap-A per shape for address/hmsg/leaf/node/roots, and Gap-B as the labeled
> `evm_keccak_*` axioms all landed on `evmrun-runtime`). The live remaining work is
> step 4 — assembling `RefinesModel evmRun`, gated on the FORS tree-loop execution
> proof. See [`PICKUP.md`](./PICKUP.md) §3 (WS-3, WS-4) for the current frontier.
> The list below is kept as the original route-i plan of record.

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
