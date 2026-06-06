# FORS+C verifier bridge — START HERE (pick-up guide)

## Agent progress (2026-06-07)

- Added `ClassA.eval_dispatcher_offset_bound_guard_after_offset` and
  `exec_dispatcher_offset_bound_if_after_offset`, proving the selected recover
  case skips `if gt(offset, 0xffffffffffffffff) { revert(...) }` after
  `offset := calldataload(4)`.
- Verified `lake build NiceTry` green. Axiom audit for the new offset-bound
  guard step is only Lean's standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`).
- Next: bind `value := calldataload(36)` and continue the selected recover
  dispatcher trace toward the dynamic-bytes length check.

## Agent progress (2026-06-06)

- Added `Bridge/CalldataBytes.lean` and registered it in `lakefile.lean`.
  Current facts proved: `word32` size/round-trip wrappers, selector size,
  `forsPayload` size (`2448`), and `encodeForsCalldata` size (`2548`).
- Extended `Bridge/CalldataBytes.lean` with `readBytes_window_32` and concrete
  ABI word reads for `calldataload(4) = 0x40`, `calldataload(36) = digest`, and
  `calldataload(0x44) = raw.len`.
- Switched `forsSelector` to the literal ABI bytes and proved
  `shr 224 (calldataload(0)) = 0x1aad75c5` for encoded FORS calldata.
- While starting `h_len`, found a boundary issue: the spine's `h_len` quantifies
  all `raw : RawSig`, but `RawSig.len : Nat` is unbounded while the ABI length
  field is a `UInt256`. Formally,
  `rawLen_uint256_collision :
    UInt256.ofNat (SigLen + UInt256.size) = UInt256.ofNat SigLen`
  and `rawLen_collision_bad_length : SigLen + UInt256.size ≠ SigLen`.
  Therefore the unbounded bad-length implication cannot be discharged from the
  EVM length word alone.
- Fixed the domain mismatch by adding shared `Bridge/RawDomain.lean` and changing
  `ForsRefines` / `RefinesModel` to quantify over `RawSigLenFitsEvmWord raw`
  (`raw.len < 2^256`). This is the ABI-representable domain for
  `recover(bytes,bytes32)`.
- Added the bounded bridge lemma the dispatcher trace can use:
  `rawLen_word_eq_sigLen_iff_of_lt :
    raw.len < UInt256.size →
    (UInt256.ofNat raw.len = UInt256.ofNat SigLen ↔ raw.len = SigLen)`.
- Added the missing stateful opcode reducer
  `InterpState.primCall_mload`, needed for the dispatcher return path after
  `fun_recover` returns a zero word on bad length.
- Added `InterpEval.eval_unop1_thread` and `eval_binop2_thread`, the expression
  composition lemmas for state-threading builtins (`mload` and `keccak256`).
- Added `InterpEval.eval_nullop0`, the expression composition lemma for
  zero-argument builtins (`calldatasize`, `callvalue`).
- Added `InterpCall.exec_let_prim`, `exec_exprstmt_prim`, and `execPrimCall_ok`,
  the statement reducers needed for `mstore(...)` and
  `let x := calldataload(...)` dispatcher steps.
- Added `Bridge/ClassA.lean` and registered it in `lakefile.lean`. Current
  Class-A facts: encoded-call initial state, `runForsCalldata` unfolding,
  dispatcher selector / calldata-size / callvalue / offset / digest / length-word
  expression evaluations, the first dispatcher guard
  `iszero(lt(calldatasize(),4)) = 1`, and the bounded
  `length word = SigLen ↔ raw.len = SigLen` handoff.
- Added `ClassA.exec_dispatcher_free_mem_ptr`, the first concrete dispatcher
  statement step for `mstore(64,0x80)` with its named post-state.
- Added `ClassA.dispatcherAfterFreeMemPtr_*` preservation lemmas and
  `eval_dispatcher_has_selector_guard_after_free_mem_ptr`, so the first `if`
  guard is available after the initial `mstore` step.
- Added `ClassA.exec_dispatcher_has_selector_if_after_free_mem_ptr`, which steps
  the first dispatcher `if` into its body after the initial memory-pointer write.
- Generalized `eval_dispatcher_selector` to `eval_dispatcher_selector_of_calldata`
  and added `eval_dispatcher_selector_after_free_mem_ptr`, so the selector switch
  scrutinee is available after the initial `mstore`.
- Generalized dispatcher offset/digest/length word evaluations to `_of_calldata`
  forms and added their post-`mstore` specializations for the selected recover
  case trace.
- Added `eval_dispatcher_callvalue_after_free_mem_ptr`, the selected recover
  case's first guard input after memory initialization.
- Added `exec_dispatcher_callvalue_if_after_free_mem_ptr`, which proves the
  selected recover case skips `if callvalue() { ... }` after memory initialization.
- Added `eval_dispatcher_min_calldata_guard_of_size` and
  `exec_dispatcher_min_calldata_if_after_free_mem_ptr`, proving the selected
  recover case skips the ABI minimum-size guard on encoded calldata.
- Added `exec_dispatcher_let_offset_after_free_mem_ptr`, the selected recover
  case step for `let offset := calldataload(4)`.
- Added one labeled codec axiom in `Bridge/EvmFfiSpec.lean`:
  `uint256_toByteArray_roundtrip`, the planned Class-A word round-trip for
  `uInt256OfByteArray v.toByteArray = v`.
- Verified `lake build NiceTry` green. Axiom audit for the new `calldataload`
  facts: only `ffi_zeroes_eq_empty`, `uint256_toByteArray_size`, and
  `uint256_toByteArray_roundtrip` beyond Lean's standard axioms. Axiom audit for
  `primCall_mload`, `eval_nullop0`, `eval_unop1_thread`, and
  `eval_binop2_thread`, plus the primitive statement reducers: only Lean's
  standard axioms. `ClassA.exec_dispatcher_free_mem_ptr` and the post-`mstore`
  preservation lemmas also use only Lean's standard axioms. Axiom audit for the
  new `ClassA` dispatcher word facts stays inside the same calldata trust surface.
- Next: prove the dispatcher length trace under `RawSigLenFitsEvmWord raw` using
  `rawLen_word_eq_sigLen_iff_of_lt`; independent raw-field payload reads can
  proceed meanwhile.

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
with trust localized to **10 labeled axioms** on this branch (verify with
`#print axioms`):

| Area | File | Status |
|---|---|---|
| FORS recovery model + structural proofs | `Fors/Model.lean`, `Fors/Proofs/*` | ✅ closed (`legit_raw_signature_recovers_expected_address`) |
| Deployed contract transcribed to EVMYulLean DSL | `Bridge/ForsRuntime.lean` | ✅ `forsVerifierRuntime` (dispatcher + `fun_recover`, incl. the 25-tree `for` loop) — verbatim from solc `irOptimized` |
| `evmRun` (calldata encode → interpreter run → decode addr) | `Bridge/EvmRun.lean` | ✅ `runForsCalldata`, `encodeForsCalldata`, `evmRun` |
| ByteArray / memory lemma library | `Bridge/ByteArrayLemmas.lean`, `Bridge/EvmMemory.lean` | ✅ Gap-A byte reasoning for every shape |
| Per-keccak shape equivalences (Class M) | `Bridge/AddressShape.lean` | ✅ address / hmsg / leaf / node (`climbLevel` even+odd) / roots |
| Roots → `recoverRoot` handoff skeleton | `Bridge/AddressShape.lean` | ✅ `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init` |
| Memory layout / non-overlap (Class C side-conditions) | `Bridge/MemoryLayout.lean` | ✅ the three `_GUARD`s |
| Trusted FFI specs (memory padding + keccak) | `Bridge/EvmFfiSpec.lean` | ✅ 5 axioms (3 `ffi_zeroes_*` + `uint256_toByteArray_size` + `uint256_toByteArray_roundtrip`) |
| SoLean oracle discharge + sufficiency | `Bridge/Oracle.lean`, `Bridge/Equivalence.lean` | ✅ `refinement_discharges_oracle`, `refinement_matches_forsAccept` |

**The 10 trust-base axioms on this branch:** `evm_keccak_{address,hmsg,leaf,node,roots}`
(`AddressShape.lean`) + `ffi_zeroes_{size,get!,eq_empty}` + `uint256_toByteArray_size`
and `uint256_toByteArray_roundtrip` (`EvmFfiSpec.lean`). The round-trip axiom is
the Class-A codec fact planned in WS-1; it mirrors EVMYulLean's private
`fromBytes'_toBytes'` proof.

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
`address(0)` (discharges `Refinement.lean`'s `h_len` + `h_guard`).
- Entry targets (named, not yet proved): `decodeTyped_reads_raw_header`,
  `decodeOpening_reads_raw_fields`, `rawOpenings_treeOpening_eq_decodeTyped_opening`.
- Obligations #6, #11 in `OBLIGATIONS.md`.
- **Foundation in place (interpreter-reasoning layer):**
  - `Bridge/Interp.lean` — one-step `exec` reductions (Block/If/Leave/Break/Continue/
    out-of-fuel) + `eval` base cases (Lit/Var/evalArgs-nil). Recipe:
    `conv_lhs => rw [exec]` then `rw [h]`.
  - `Bridge/InterpOps.lean` — `primCall` lemmas for the pure stack ops
    (`add sub lt gt slt and or xor shl shr byte eq iszero not`). Recipe:
    `unfold primCall; simp [<step OP> = … from by unfold step; rfl]`.
  - `Bridge/InterpEval.lean` — argument plumbing (`evalArgs_cons_ok`,
    `evalTail_cons_ok`, `eval_call_prim`) + composition lemmas `eval_unop1` /
    `eval_binop2`, so nested pure expressions (`and(calldataload(x), not(C))`)
    evaluate compositionally (regression example included). Fuel: `+2` per arg depth.
  - `Bridge/InterpState.lean` — `primCall` for the stateful ops: `calldataload`,
    `callvalue`, `calldatasize`, `mstore`, `keccak256`, `return` (⇒ `YulHalt`),
    `revert` (⇒ `.Revert`). State-rebuilding ops use `unfold step; cases s <;> rfl`.
  - **⚠ evmRun was broken — now fixed (commit `bcc3867`).** `runForsCalldata` ran the
    dispatcher on a state with an *empty* account map; the `recover` path calls
    `fun_recover` via the interpreter's `call`, which does `accountMap.find? codeOwner`
    and errors `MissingContract` **before** `codeOverride` is consulted. So `evmRun`
    returned `0` for *every* input (h_accept/ForsRefines were false; h_len/h_guard
    vacuous). Fix installs an account at `codeOwner` (code superseded by the override).
    Verified: `find? codeOwner |>.isSome = true` by `rfl` post-fix. **Anyone stepping
    the contract must use the fixed `evmRun`.**
  - `Bridge/InterpCall.lean` — the last control-flow primitives: `exec_let_call` /
    `exec_exprstmt_call` / `execCall_ok` / `execCall_err` / `call_ok` (entering
    `fun_recover`; `call_ok` fires now that the contract is installed), and the
    `switch` family `exec_switch_ok` + `execSwitchCases_nil/_cons_ok/_cons_halt` +
    `foldr_switch_cons_match/_nomatch` (EVMYulLean's `switch` eagerly runs all case
    bodies then `foldr`-selects by the scrutinee).
  - **The interpreter-stepping foundation is now COMPLETE** — every construct in
    `forsDispatcher` + `fun_recover` (control flow, all 14 pure builtins, all 7
    stateful ops, user-calls, switch, expression composition) has a reduction lemma.
  - **The one remaining brick for `h_len` — a `calldataload` byte-reasoning library
    (sizeable, ~`EvmMemory.lean` scale):**
    1. `ByteArray.readBytes` reduction — it routes through `copySlice` + the opaque
       `ffi.ByteArray.zeroes` (use the `EvmFfiSpec` `ffi_zeroes_*` specs).
    2. word round-trip `uInt256OfByteArray (UInt256.ofNat n).toByteArray = n` (for
       `n < 2^256`) — EVMYulLean's `fromBytes'_toBytes'` is `private`, so this likely
       becomes a trust axiom mirroring `uint256_toByteArray_size`, or a from-scratch
       proof.
    3. `readBytes` over `encodeForsCalldata`'s nested `++` (`selector ‖ 0x40 ‖ digest
       ‖ len ‖ payload`) with offset/size arithmetic ⇒ `calldataload 4 = 0x40`,
       `calldataload 0x44 = raw.len`, `calldataload 36 = digest`, `shr 224 (calldataload 0)
       = selector`, `calldatasize = 2548`; connects to the proved model-side `decodeTyped_*`.
    4. Assemble the dispatcher trace + `fun_recover` length check into `h_len`
       (mechanical once 1–3 exist, using the now-complete stepping foundation).
    `h_guard` additionally needs the **hmsg keccak bridge** (Class-M): the contract's
    `dVal = keccak256(0,0xa0)` and `forcedZero` check (`forcedZero_eq_evm_shape`).

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

### WS-4 · Assemble `RefinesModel evmRun`  — ✅ **DONE** (`Bridge/Refinement.lean`)
`forsRefines_of_branches` reduces `ForsRefines` to exactly three interpreter-run
obligations — `h_len` (bad length → `address(0)`), `h_guard` (forced-zero reject →
`address(0)`), `h_accept` (otherwise `= addressFromRoot pkSeed (recoverRoot …)`).
All model-side glue (the `recoverRaw?` case-split + `none ↔ address(0)`) is proved;
adds **zero trust** (`#print axioms` = `propext/Classical.choice/Quot.sound`).
`h_len`/`h_guard` ⇐ WS-1; `h_accept` ⇐ WS-2 + WS-3 via the AddressShape handoffs.
Remaining glue: adapt to the `Option` `RefinesModel` form for
`refinement_discharges_oracle` → SoLean oracle.

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
