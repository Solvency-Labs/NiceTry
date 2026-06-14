# Class-M architecture & findings (the EVM↔model memory bridge)

Result of spiking the Class-M layer against real EVMYulLean. Two findings reshape
the plan; both are honest TCB facts Antonio should see.

## Finding 1 — three layers, two gaps (the model isn't end-to-end)

The FORS model originally had **two opaque keccak families that were never
related**:

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

## Finding 2 — the extern boundary is smaller than first believed

`mstore` → `writeWord` → `ByteArray.write`, and `UInt256.toByteArray`, both call
`ffi.ByteArray.zeroes : USize → ByteArray`. It is `@[extern]`, but unlike
`ffi.KEC` it also has a reducible Lean body (`Array.replicate`), so its size,
contents, and empty-array behavior are kernel-provable. The same is true of the
word codec once EVMYulLean's private encoder-length theorem is applied by its
generated declaration name. `EvmFfiSpec.lean` now proves all five former
padding/codec axioms.

The remaining extern boundary is `ffi.KEC`: `InterpKeccak.lean` assumes only
that it returns 32 bytes (`ffi_kec_size`) and proves the decoded `< 2²⁵⁶` bound
from EVMYulLean's public decoder theorem.

Current Bridge shape status: Gap-A byte equality is proved for address, hmsg,
leaf, node, and the roots-compression buffer (with abstract per-tree root
values). The Phase 5 Gap-B split is complete:

* `TranscriptEncoding.lean` defines `encodeTranscript` and proves all five
  concrete EVM word sequences equal their abstract transcript encodings.
* `Hash.lean` has one opaque `keccakWord`; `keccakHash16` and `keccakAddress` are
  definitions that apply the proved high-128/low-160 masks.
* `AddressShape.lean` has one generic trust item,
  `evm_keccak_transcript`, replacing the five bundled shape axioms.
The FORS tree-climb loop now proves that the 25 roots written into the roots
buffer are exactly the model chain values. The post-loop handoff is
named: establish `pkSeed` at `0x00` and the 25-root buffer at `0x40..0x35f`, then
`roots_derivation_eq_from_buffer` connects the real `compressRoots` call to the
model. The helper `roots_derivation_eq_after_loop_buffer_init` composes the
abstract root-buffer initialization, the memory-size preservation facts, and the
final `mstore(0x20, ADRS_roots); keccak256(0,0x360)` call. `TreeLoop.lean`,
`TreeCalldata.lean`, and `TreeEntryFront.lean` now supply the real loop values and
complete pre-loop entry invariant; the remaining work is the raw-header/model glue
and composition with the loop and post-loop trace. The sharper target is
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
  TCB = the generic keccak/transcript bridge + the 32-byte `ffi.KEC` shape fact.
* **(ii) Axiomatize the per-keccak binding (pragmatic).** One auditable axiom per
  keccak shape: "running the kernel's `mstore` choreography then `keccak256 off len`
  yields `keccakWordFromMemory call`." Sidesteps `ByteArray` entirely; larger but
  mechanical TCB. Gap B still proved.

Recommendation: **(i)** — it's the reason route B is worth doing over route A, and
the byte library is reusable across all 5 transcript shapes. Fall back to (ii) per
shape if a specific proof proves intractable.

## Concrete next steps (route i)

> **Status update:** steps 1–4 below are now **done** for the deployed contract.
> Phase 5 then narrowed Gap B from five bundled shape axioms to the single
> `evm_keccak_transcript` assumption over a proved canonical encoder. See
> [`PICKUP.md`](./PICKUP.md) for the current trust-reduction frontier.
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
