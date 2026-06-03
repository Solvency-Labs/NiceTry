# FORS+C verifier bridge — START HERE (pick-up guide)

This is the entry point for anyone picking up the `ForsVerifier.sol` ⊑ Lean-model
proof. It says **where the work lives, what's already done, and exactly what to
grab next**. Deep technical detail is in [`OBLIGATIONS.md`](./OBLIGATIONS.md) (the
discharge plan) and [`CLASS-M.md`](./CLASS-M.md) (the EVM↔model memory findings).

---

## 0. Where the work actually is (read this first — it bites)

- **Remote:** the live work is on **`Solvency-Labs/NiceTry`**, *not* the
  `RivaLabs-Core/NiceTry` upstream. If you cloned from RivaLabs-Core you will get
  the FORS model **without** the `Bridge/` directory and waste an afternoon
  looking for it.
  ```bash
  git remote add solvency https://github.com/Solvency-Labs/NiceTry.git   # if missing
  git fetch solvency
  git checkout -B evmrun-runtime --track solvency/evmrun-runtime
  ```
- **Branch:** `evmrun-runtime` — has `evmRun` + the runtime transcription on top of
  the merged Codex shape work. (`fors-verity-model` is the model+shape base;
  `codex/fors-overwrite-shapes` is the shape-only Codex workstream.)
- **Path:** all Lean is under `verity/NiceTry/Fors/`; the EVM bridge is in
  `verity/NiceTry/Fors/Bridge/`.

## 1. How to build (also bites)

The lakefile has **no `@[default_target]`**, so a bare `lake build` compiles
**nothing** and still exits 0 — a false green. Always name the library:

```bash
cd verity
lake exe cache get      # pull Mathlib oleans; skips ~1h of from-source Mathlib build
lake build NiceTry      # the real build — compiles EVMYulLean + verity + the Bridge
```

Dependencies are pinned in `lakefile.lean` (`verity@bd211c5`, which pulls
`EVMYulLean@b353c75` + Mathlib). First build is a cold clone of all of them.

---

## 2. What is DONE — do not redo this

All of the following is committed on `evmrun-runtime`, **`sorry`/`admit`-free**,
with trust localized to **9 labeled axioms** (verify with `#print axioms`):

| Area | File | Status |
|---|---|---|
| FORS recovery model + structural proofs | `Fors/Model.lean`, `Fors/Proofs/*` | ✅ closed (`legit_raw_signature_recovers_expected_address`) |
| Deployed contract transcribed to EVMYulLean DSL | `Bridge/ForsRuntime.lean` | ✅ `forsVerifierRuntime` (dispatcher + `fun_recover`, incl. the 25-tree `for` loop) — verbatim from solc `irOptimized` |
| `evmRun` (calldata encode → interpreter run → decode addr) | `Bridge/EvmRun.lean` | ✅ `runForsCalldata`, `encodeForsCalldata`, `evmRun` |
| ByteArray / memory lemma library | `Bridge/ByteArrayLemmas.lean`, `Bridge/EvmMemory.lean` | ✅ Gap-A byte reasoning for every shape |
| Per-keccak shape equivalences (Class M) | `Bridge/AddressShape.lean` | ✅ address / hmsg / leaf / node (`climbLevel` even+odd) / roots |
| Roots → `recoverRoot` handoff skeleton | `Bridge/AddressShape.lean` | ✅ `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init` |
| Memory layout / non-overlap (Class C side-conditions) | `Bridge/MemoryLayout.lean` | ✅ the three `_GUARD`s |
| Trusted FFI specs (memory padding + keccak) | `Bridge/EvmFfiSpec.lean` | ✅ 4 axioms (3 `ffi_zeroes_*` + `uint256_toByteArray_size`) |
| SoLean oracle discharge + sufficiency | `Bridge/Oracle.lean`, `Bridge/Equivalence.lean` | ✅ `refinement_discharges_oracle`, `refinement_matches_forsAccept` |

**The 9 trust-base axioms:** `evm_keccak_{address,hmsg,leaf,node,roots}`
(`AddressShape.lean`) + `ffi_zeroes_{size,get!,eq_empty}` + `uint256_toByteArray_size`
(`EvmFfiSpec.lean`). See `TRUST_SURFACE` for why each is acceptable.

> Net: the per-shape "every hash step is the right one" guarantee is **proved**.
> The contract-execution spine connecting those steps is **not yet assembled**.

## 3. What is OPEN — the remaining frontier

Everything reduces to: **connect the interpreter actually running
`forsVerifierRuntime` to the premises the proved handoff lemmas already consume.**
`ForsRefines` / `RefinesModel evmRun` is currently only a `def : Prop` with a prose
decomposition (`EvmRun.lean` lines 64-87, `Equivalence.lean` lines 55-96). Four
independently-claimable workstreams:

### WS-1 · Class-A: ABI calldata parse  — *smallest, good first task*
Prove `runForsCalldata (encodeForsCalldata raw digest)` routes the dispatcher to
`fun_recover` with the right `offset/length/digest`, and that `fun_recover`'s
`calldataload` field reads equal `raw.read16` / `decodeRaw`; bad length →
`address(0)`.
- Entry targets (named, not yet proved): `decodeTyped_reads_raw_header`,
  `decodeOpening_reads_raw_fields`, `rawOpenings_treeOpening_eq_decodeTyped_opening`.
- Obligations #6, #11 in `OBLIGATIONS.md`.

### WS-2 · Class-M execution wiring  — *mechanical, template exists*
The `*_derivation_eq_overwrite` lemmas in `AddressShape.lean` assume a
`MachineState` whose memory already satisfies the shape hypotheses (e.g.
`m.memory.data.extract 0 32 = pkSeed.toByteArray.data`). Open work: show the **real
interpreter execution up to each keccak** produces such a state. address is the
done template; hmsg / leaf / node follow it.

### WS-3 · The FORS tree loop  — *the multi-week long pole*
Induct over the interpreter executing `for { } lt(usr_t,25) { … }` in
`fun_recover`, threading `MachineState`, to produce the per-tree
`leaf / node1..5 / root` values and **discharge the `hleaf / hnode1..5 / hroot`
premises** of
`roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`. Use the
prefix invariant `roots_loop_buffer_prefix_after_init` and the
`node_derivation_eq_climbLevel_{even,odd}_overwrite` sibling-ordering lemmas. This
is the genuine core; the *destination* lemmas exist, the *execution → premises*
bridge does not.

### WS-4 · Assemble `RefinesModel evmRun`  — *integration; statement can be written now*
Chain WS-1 + WS-2 + WS-3 + the proved address/roots handoffs + the forced-zero and
length-rejection branches into a term of `RefinesModel evmRun`. Then
`refinement_discharges_oracle evmRun` closes the whole chain to the SoLean oracle.
Planned home: a new `Bridge/Refinement.lean` stating the reduction with the open
WS-1/WS-3 lemmas as its only named goals (so the long pole has a typed skeleton).

### Finishing step (after WS-1..4)
Flip the 12 Verity `local_obligations` `.assumed → .proved` and rebuild with
`lake exe verity-compiler … --deny-local-obligations` to enforce none remain
(`OBLIGATIONS.md` §"Discharge order" step 5).

---

## 4. Suggested grab order by time available
- **An hour:** WS-1 (ABI parse) or one shape of WS-2 (hmsg/leaf/node) — bounded.
- **A focused week+:** WS-3 (the loop). One owner — it overlaps WS-2/WS-4; diverging
  copies of the loop induction will hurt.
- **Glue:** WS-4 statement first (unblocks parallel work), proof last.

## 5. Build status of this branch
- **`lake build NiceTry` — verified green (2026-06-04):** 1134/1134 modules built,
  all 9 Bridge oleans produced, no errors/warnings, and the three
  `#check_contract ok` for the Verity kernels.
- **Axiom audit (`#print axioms`) — clean:** no `sorryAx` anywhere. The bridge
  theorems depend only on Lean's `propext / Classical.choice / Quot.sound` plus the
  labeled trust axioms (`evm_keccak_*`, `ffi_zeroes_*`, `uint256_toByteArray_size`).
  The sufficiency theorem `refinement_discharges_oracle` is pure logic (`[propext]`).
- Reminder: a bare `lake build` (no target) compiles nothing and still exits 0 — see
  §1. Always build `NiceTry` and re-run the axiom audit after touching the Bridge.
