# FORS+C verifier bridge — START HERE (pick-up guide)

## Current checkpoint (2026-06-14) — Phase 4 complete through the reviewed dispatcher transcription

- **Final theorem:** `Phase4.phase4_forsRefines : ForsRefines` proves that the
  reviewed optimized-IR runtime transcription agrees with `recoverRaw?` on
  `ForsAbiInput`.
- **ABI domain fixed honestly:** `RawDomain.lean` now defines `ForsAbiInput` as
  representable length + packed 16-byte fields + a bytes32-sized digest. The old
  length-only statement was false for unbounded model `Nat` values because ABI
  encoding truncates them.
- **Accept path closed:** `Phase4Accept.lean` executes the real scoped call through
  the complete prefix, hmsg transcript, 25-tree loop, roots compression, low-160
  address derivation, and final `RETURN`.
- **Reject paths closed:** `Phase4Reject.lean` proves the exact malformed-length
  word guard/body and the forced-zero `YulHalt` zero return. The scoped observable
  normalizes malformed lengths to zero before running the checked good-length call.
- **Dispatcher route closed:** `DispatcherRoute.lean` executes the real selector
  switch, ABI decode and bounds guards, then proves the call into
  `fun_recover(100, raw.len, digest)`. Malformed representable lengths are covered
  by the dispatcher's revert paths or the aligned direct call's out-of-fuel result.
  `dispatcher_routes_to_recover` is now a theorem, not an axiom.
- **Fuel is exact:** `recoverFuel = 99983`, exactly the fuel received by
  `fun_recover` inside `runForsCalldata ... 100000`; no fuel-monotonicity axiom
  was added.
- **Build/audit:** `lake build NiceTry` passes all 1172 modules.
  `#print axioms phase4_forsRefines` reports Lean core plus exactly 2 project
  axioms: `evm_keccak_transcript` and `ffi_kec_size`. There is no dispatcher,
  padding, codec, or numeric keccak-bound axiom and no `sorryAx`.
- **Obligation accounting (2026-06-13): 9 of 11 discharged; last 2 held as a
  documented boundary.** All keccak-transcript memory obligations (#1–#5, #7, #8)
  and both Class-A calldata obligations (#6, #11) are now `proved`, each backed by
  a real Lean theorem (see the sprint logs below). The 2 remaining —
  `full_verifier_memory_refinement` (#9) / `full_raw_verifier_memory_refinement`
  (#10), Class-C loop choreography on the auxiliary Verity kernel — are
  **deliberately held `.assumed`**: the equivalent choreography is already proven
  for the *deployed* contract (`tree_loop_run` + `Phase4Accept`, inside
  `phase4_forsRefines`), so discharging the kernel copies would duplicate that
  whole induction for a reference artifact (full rationale + cross-refs in
  `OBLIGATIONS.md`).
- **Phase 5 trust reduction:** the bundled keccak/encoding assumptions are split,
  all zero-padding and word-codec facts are now theorems, and the generic
  keccak numeric bound is derived from the sole FFI shape fact
  `(ffi.KEC b).size = 32`.
- **Next:** upstream a public word-codec theorem to remove the private-name
  maintenance hook, and decide whether to retain `ffi_kec_size` as the honest
  extern-C contract or connect the FFI to a modeled Keccak implementation. The
  last 2 kernel obligations are out
  of scope by decision; revisiting them means building a kernel loop-execution
  model (the kernel analogue of `TreeLoop.lean`). Do NOT flip them without real
  lemmas: the Verity `proved` flag is an unchecked label, so honesty rests
  entirely on a cited Lean theorem.
- **GOTCHA (GetElem on string literals):** `state[("foo":Identifier)]!` FAILS GetElem
  synthesis (`GetElem? Yul.State String ?m ?m`). Use a `def fooId : Identifier := "foo"`
  index (like `retId`) OR phrase via `EvmYul.Yul.State.lookup! "foo" s` (a plain arg).
  Reads coming OUT of `exec` (from `.Var` AST nodes) synth fine. To peel an `mstore`/`insert`
  chain after `ok_set_eq`, note State.insert is NOT reducibly unfolded by `rw`, so
  `state_getElem_finsert_ne` (Finmap form) won't match a `State.insert` chain — use a `show`
  to the collapsed `Ok a (vs.insert ...)` form (defeq by rfl) first. `exec_let_lit` produces
  `vars.head!` keys; clean with `simp only [List.head!_cons]`.
- **Build:** `lake build NiceTry` passes all 1172 modules on
  `agent/phase4-integration`.

## Trust surface (2 labeled axioms declared; Phase 4 uses both)

None are hardness assumptions. Verify with `#print axioms <thm>`.
- **keccak (1)** — `evm_keccak_transcript` (`AddressShape.lean`): EVM Keccak over
  the canonical `encodeTranscript fields` equals the model's opaque
  `keccakWord fields`. `TranscriptEncoding.lean` proves the five concrete
  transcript encodings; `keccakHash16` and `keccakAddress` are proved masks.
- **keccak FFI shape (1)** — `ffi_kec_size` (`InterpKeccak.lean`): the
  C-backed `ffi.KEC` returns 32 bytes. The numeric `< 2²⁵⁶` bound is a theorem.

`ffi_zeroes_{size,get!,eq_empty}` and
`uint256_toByteArray_{size,roundtrip}` are now kernel-checked theorems in
`EvmFfiSpec.lean`. The codec size proof currently applies an upstream private
lemma by its generated declaration name; that is a maintenance risk, not trust.

## Sprint log (2026-06-13d) — Class-A calldata obligations discharged (9/11)

- **`raw_abi_parse` (#11) + `raw_calldata` (#6) flipped to `proved`.**
  - **#11:** new `kernel_recover_abi_parse` (in `KernelRefinement.lean`) — on
    `recover(bytes,bytes32)` ABI calldata (`encodeForsCalldata raw digest`),
    `calldataload(4) = 0x40` (offset), `calldataload(4+offset) = raw.len`
    (length), `calldataload(4+offset+32)` = first `sig.data` word. Built by
    composing `calldataload_encode_offset` / `_length` / `_payload_pair_0`.
  - **#6:** cited `masked_calldataload_read16` (+ `_counter_`) from
    `TreeCalldata.lean` — with sigData = 100 and any FORS field offset (a multiple
    of 16, or the 2432 counter), `rawWord = bitAnd(calldataload(sigData+off), NMask)`
    recovers `raw.read16(off)` under `RawSigWellFormed` (part of `ForsAbiInput`).
  - Honesty model identical to the `mstore` obligations: the residual is that the
    compiler maps the kernel's `calldataload` to EVMYulLean's verbatim. Axiom
    audit on `kernel_recover_abi_parse`: only `uint256_toByteArray_{size,roundtrip}`
    + `ffi_zeroes_eq_empty` + Lean core; no `sorry`. `lake build NiceTry` green
    (1170 modules, all `#check_contract ok`).
- **Remaining 2 = the Class-C choreography capstone** (`full_*_verifier_memory_refinement`,
  #9/#10): need the kernel `forEach` loop's *executed* memory behaviour
  (pkSeed preserved, 25 roots at `0x40+32t`, scratch non-overlap, roots =
  recovered values via `reconstructTree`). No kernel loop-execution model exists,
  so these stay `.assumed` — not flipped.

## Sprint log (2026-06-13c) — all keccak-transcript obligations discharged (7/11)

- **hmsg / roots / address discharged + flipped.** Building on the leaf/node work
  below, the remaining three keccak-transcript obligations are now `proved`:
  - **hmsg (#3):** cited `hmsg_derivation_eq_overwrite` — the existing 5-store
    chain (`0x00 pkSeed, 0x20 r, 0x40 digest, 0x60 dom_FORS, 0x80 counter`) is
    byte-for-byte the kernel's `hMsg` body (`dom_FORS` = the literal `0xFF..FD` =
    `ForsDomainWord`). Concludes `= hMsg` (no masking, matching the kernel).
  - **roots (#7):** cited `roots_derivation_eq_from_buffer` — matches the kernel's
    `compressRoots` exactly: a pre-populated buffer (pkSeed@0x00, roots@`[0x40,0x360)`)
    plus the single `mstore(0x20, ADRS_roots)` then `keccak256(0,0x360)`, masked,
    `= compressRoots`. The buffer-population precondition is the loop's job (the
    Class-C obligations #9/#10).
  - **address (#8):** new `kernel_address_keccak_memory_refinement` — the kernel
    emits *both* stores (`0x00 pkSeed; 0x20 pkRoot`) onto arbitrary populated
    memory; neither existing address lemma covered that, so it extracts pkSeed@0x00
    from the first store and reuses `address_derivation_eq_overwrite`. Masked with
    `Lower160Mask`, `= addressFromRoot`.
  - Axiom audit: `kernel_address_*` uses only `evm_keccak_address` + codec/FFI +
    Lean core. All `#check_contract ok`; `lake build NiceTry` green (1170 modules).
- **Remaining 4 (honest stop):** `raw_calldata_refinement`,
  `raw_abi_parse_refinement` (Class-A calldata) and the two
  `full_*_verifier_memory_refinement` (Class-C loop choreography) are *not*
  closed `mstore`-chain facts — they need a kernel calldata model and a kernel
  loop-execution model respectively. Left `.assumed`; not flipped (flipping
  without a real lemma would be a false `proved`).

## Sprint log (2026-06-13b) — obligation discharge begins: leaf/node kernel keccak refinement

- **`Bridge/KernelRefinement.lean` (new) — Class-M, kernel-facing.** Two real,
  fully-proved theorems discharge the leaf/node `keccak_memory_refinement`
  obligations of *both* Verity kernels:
  - `kernel_leaf_keccak_memory_refinement`: over the kernel's exact 3-store leaf
    chain (`mstore 0x380 pkSeed; 0x3a0 adrs; 0x3c0 sk`) on any scratch-sized
    machine state, the masked `keccak256(0x380,0x60)` = model `leafHash`.
  - `kernel_node_keccak_memory_refinement`: over the exact 4-store node chain
    (`+ mstore 0x3e0 right`), the masked `keccak256(0x380,0x80)` = model
    `nodeHash`.
  - Proof = the artifact-agnostic extract calculus from `TreeMemory.lean`
    (`mstore_extract_self`/`mstore_extract_disjoint`/`mstore_memory_size` peel each
    slot back through the chain) feeding `leaf_/node_derivation_of_extracts`.
  - **Why a new theorem and not the deployed-contract one:** the deployed
    contract pre-stores `pkSeed@0x380` once (`TreeLeaf.lean` leaf body = 2 stores);
    the kernels emit all 3/4 stores per call. Different programs, same transcript
    — flipping the kernel flags "against the deployed lemmas" would have been an
    overclaim, so the kernel-specific chain is proved directly.
  - **Flags flipped (4):** `TreeKeccakKernel` leaf/node + `FullVerifierKernel`
    leaf/node `:= proved`, each justification citing its theorem. The Verity
    `proved` flag is a free-text label the macro never checks (parser:
    `Verity/Macro/Translate.lean` `parseLocalObligation`); honesty here rests on
    the cited Lean theorem, not the label.
  - **Residual on these 4:** (a) the Verity compiler emits exactly the `unsafe do`
    `mstore` sequence (true by inspection), and (b) keccak itself stays the
    intended abstract boundary (`evm_keccak_{leaf,node}`) — the obligation text
    only asks about the *memory writes + masking*, which is fully proved.
  - **Axiom audit:** both theorems depend only on `evm_keccak_{leaf,node}`,
    `uint256_toByteArray_size`, `ffi_zeroes_eq_empty`, and Lean core. No `sorry`.
  - **Build:** `lake build NiceTry` green — 1170 modules, all three
    `#check_contract ok` (incl. both kernels with flipped flags).

## Sprint log (2026-06-12b) — M3 DONE: the tree loop is PROVED

- **`Bridge/TreeLoop.lean` — the A4 induction, closed end to end:**
  - Loop plumbing (`mkOk`/`reviveJump`/`overwrite?` are identity on `.Ok`;
    `UInt256` `lt`/`add`/`shiftRight` value lemmas; cursor bits = `indexAt`).
  - `treePostState` fully resolved (Ok exposures + per-variable lookups).
  - `LoopInv` (the loop invariant: control vars, `dCursor = dVal >>> 5t`,
    pkSeed slot extract, `0x3a0 ≤ size`, pointer bound) + closed-form
    per-tree values (`loopSk`/`loopSib`/`loopRootV` — the 5-level climb over
    the masked calldata reads at `ptr0 + 96j + {0,16,32,48,64,80}`).
  - `tree_iter_body_facts` (the mega-lemma): one body iteration from the
    invariant — exit `.Ok`, vars/calldata view kept, memory to `0x400`,
    below-slot + pkSeed preservation, the closed-form root written.
  - `tree_iter_step_full`: + the post block → `LoopInv (t+1)`.
  - **`tree_loop_run` / `tree_loop_run_from_zero`**: the 25-iteration
    `loop_step` induction (fuel `n + 3k + 46`; from zero: `n + 121`),
    exiting via `loop_exit` at `t = 25` — final `.Ok` state with
    `LoopInv 25`, memory below `0x40` untouched, and **all 25 root slots
    populated with `loopRootV` chain values**.
  - Axiom audit: the four documented axioms only
    (`evm_keccak_{leaf,node}`, `ffi_kec_lt`, `ffi_zeroes_eq_empty`,
    `uint256_toByteArray_size`). No sorry.
- **M4 (next) — `h_accept` assembly:**
  1. **Pre-loop trace** (statements 0–31 of `fun_recover`, generic fuel):
     establishes `LoopInv … 0` — incl. `mstore(0x380, pkSeed)` giving the
     pkSeed extract (memory ends at exactly `0x3a0` there — the calculus
     already covers it), the hmsg keccak + forced-zero skip, and the loop
     var inits (`ptr0 = var_sig_offset + 0x20`, `dVal = hmsg word`).
  2. **Calldata glue**: `loopSk/loopSib T ptr0 j` ↔ `(sig.openings j).sk/auth`
     (CalldataBytes `read16` machinery) and `idx = indexAt dVal j` per tree ⇒
     instantiate `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`
     with the `rootsW` family from `tree_loop_run_from_zero` (its `hleaf/...`
     hypotheses are exactly `loopRootV`'s layers — split `loopRootV` into the
     seven families pointwise).
  3. **Post-loop trace**: `mstore(0x20, shl(130,1))`, the roots keccak
     `keccak256(0, 0x360)` (consumes the populated buffer + pk@0 from the
     hmsg phase — NOTE: needs `pkSeed@0x00` preserved through the loop ✓
     `tree_loop_run`'s below-`0x40` preservation), the address keccak, and
     `return(0, 0x20)` through `evmRunRecover`.

## Sprint log (2026-06-12) — M1 + M2 DONE: ready for the A4 induction (M3)

- **M1 (`TreeValue.lean` completed + `TreeIter.lean`):**
  - **Iteration-0 fix**: the first iteration *extends* memory (loop entry has
    `size = 0x3a0`); generalized the extract calculus to boundary-tolerant
    forms (`byteArray_write_overwrite'` under `destAddr ≤ size`,
    `mstore_{memory_size,extract_below,extract_self}'`) and re-keyed all
    discharges on the weak size hypotheses — valid for all 25 iterations.
  - **All six per-level value discharges** (leaf, nodes 1–4, root) as thin
    wrappers over generic chain-value lemmas
    (`masked_keccak_{leaf,node}_chain_value{,_even,_odd}`).
  - **`TreeIter.lean`**: chain memory facts under the selector disjunction,
    `IterFacts` invariant (control vars/calldata view/pkSeed slot/size) with
    leaf base + node steps, level-exit transparency (laddered one-layer Ok
    algebra — **gotcha**: deep whnf of the nested state defs causes
    unification blowup; the ladder style checks in ~1.5s where naive defeq
    hit 8M-heartbeat timeouts), existential per-level step lemmas, and
    **`tree_iter_values`** — all six hash values of one iteration, chained
    and entry-keyed.
- **M2 (`TreeArith.lean`):** UInt256 bit-op `toNat` semantics; `shl_land_32`
  (bit extraction); the five selector parity cases; the six ADRS-word
  identities (`Nat.two_pow_add_eq_or_of_lt` + omega); and
  **`tree_iter_values_of_invariant`** — the six values directly from the
  invariant values (`t < 25`, `x = usr_dCursor`, `idx = x % 32`,
  `usr_t`/`tLeafBase`/`ret`/`ret_2` lookups).
- **M3 (next, the A4 induction) — all inputs now exist:**
  1. Invariant def: `usr_t = t`, `usr_treePtr = sigOff+0x20+96t`,
     `usr_rootPtr = 0x40+32t`, `usr_tLeafBase = 32t`,
     `usr_dCursor.toNat = dVal >>> 5t`, `ret = 32`, `ret_2 = 96`,
     pkSeed extract @0x380, `0x3a0 ≤ size`, roots `j < t` written
     (`mem[0x40+32j]` extracts), calldata view fixed.
  2. Step: `loop_step` + `exec_tree_body_iter` (hbody) + `exec_tree_post`
     (hpost) + `eval_tree_cond` (hcond) + `treeIterState_ok`;
     values via `tree_iter_values_of_invariant` (idx = indexAt dVal t glue:
     `x % 32` with `x = dVal >>> 5t` — omega/`Nat.shiftRight_eq_div_pow`);
     invariant restoration via the `IterFacts` lemmas + `treePostState`'s
     insert chain (`state_getElem_insert_{self,ne}`) +
     `treeAfterNode5_memory`/`root_store_memory_facts` (root slot written,
     `rootPtr+32 ≤ 0x360` from `t < 25`).
  3. Exit at `t = 25` via `loop_exit`; collect roots ⇒
     `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`.
  4. Remaining non-loop glue for `h_accept`: sibling reads ↔
     `(sig.openings t).auth` and sk ↔ model (calldata layer), the pre-loop
     trace, and the post-loop roots/address keccaks.

## Sprint log (2026-06-11b) — value layer: extract calculus + leaf & node-1 values

- **`Bridge/TreeMemory.lean` — the extract-based scratch-window calculus.** No
  chain re-factoring (collapse/commute) needed anywhere:
  `mstore_extract_{self,disjoint}` + `mstore_memory_size` chase per-slot
  contents through any store sequence; `scratch_{leaf,node}_read_of_extracts`
  rebuild the keccak input; `{leaf,node}_derivation_of_extracts` +
  `node_derivation_climbLevel_{even,odd}_of_extracts` are the extract-based
  twins of the `AddressShape` chain lemmas. `uint256_ofNat_toNat_of_lt` made
  public for the value files.
- **`Bridge/TreeValue.lean` — the per-hash discharges, both templates worked:**
  - `tree_leaf_node_value_of_extract`: leaf value from the **extract-based
    invariant** (pkSeed bytes at `[0x380,0x3a0)` of the *entry* memory +
    `0x400 ≤ size` — this is what A4 maintains; nothing in the body writes
    `0x380`, so `mstore_extract_disjoint` preserves it).
  - `tree_node1_value_of_extract_{even,odd}`: the level-1 node value =
    `climbLevel` with node = entry `usr_node`, sibling = masked read at
    `usr_treePtr+16`, keyed on the selector value `usr_s ∈ {0,32}`
    (`xor_3c0/3e0_{zero,32}`) — the full swap case split, worked end to end.
  - Lookup-resolution kit (`state_setMachineState_getElem`,
    `treeAfterSel0_getElem_{self,ne}`, per-state `_getElem`/`_toState` rfl
    transfers) — the pattern for resolving any loop-body lookup.
- **Remaining for `h_accept`:**
  1. Levels 2–5 value discharges — parameter copies of the node-1 template
     (selector var `usr_s_k`, ADRS params, sibling offset `+ret/+48/+64/+80`,
     node var; level 5 stores to `usr_rootPtr` — also needs a rootPtr-write
     extract lemma for the roots buffer at `0x40+32t`).
  2. Chain the six values through `treeIterState` (the hashes feed forward:
     level k+1's `usr_node_k` lookup = level k's value — via the read-back
     lemmas) ⇒ per-iteration `hleaf/hnode1..5/hroot`.
  3. A4 `loop_step` induction (exec side is DONE: `exec_tree_body_iter`,
     `exec_tree_post`, `eval_tree_cond`, `treeIterState_ok`): invariant =
     extract facts (pkSeed@0x380, roots prefix at 0x40) + var values
     (`usr_t=k`, pointers, `dCursor=dVal>>5k`, `ret=32`, `ret_2=96`) + the
     ADRS/selector arithmetic (`hadrs`/`hsel`/parity per level).
  4. Feed `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`
     → `address_derivation_eq_overwrite` → `h_accept`.

## Sprint log (2026-06-11) — A3 exec DONE: the full loop body runs symbolically

- **`Bridge/TreeNode.lean`** (on top of the A2 template; generic fuel, generic
  state, **zero added axioms** — all Lean-core-only):
  - **All five node levels executed** (`exec_tree_body_node{1..5}`), each from
    any state at fuel `n+20` → `n+15`, via parameterized statement lemmas
    (`exec_tree_selector_let` incl. the triple-`and` form,
    `exec_tree_node_adrs_mstore` over `(shl,shr,mask,C)`,
    `exec_tree_node_store`/`exec_tree_sibling_store` over the selector var and
    sibling-offset eval, `exec_tree_node_hash_let`, `exec_tree_root_store` via
    the new state-threading `exec_mstore_thread`).
  - **`exec_tree_body_iter`** — ONE COMPLETE body iteration: `exec (n+43)
    (.Block forsTreeBody) co (.Ok ss vs) = .ok (treeIterState (.Ok ss vs))`.
    This is `loop_step`'s `hbody`, with `treeIterState_ok` giving the `.Ok`
    shape it pattern-matches on.
  - **`eval_tree_cond`** (`lt(usr_t,25)` word) + **`exec_tree_post`** (the
    5-statement post block → `treePostState`) — `loop_step`'s `hcond`/`hpost`.
- **What remains for `h_accept`** (the value layer; all execution is done):
  1. **Per-level value bridges**: relate each `treeNode<k>Word` to the model
     `climbLevel` via `node_derivation_eq_climbLevel_{even,odd}_overwrite`.
     Crux: the `usr_s_k ∈ {0, 32}` case split (`xor(0x3c0/0x3e0, usr_s)` swap)
     plus **mstore bookkeeping not yet built**: same-offset overwrite collapse
     (`(m.mstore a v).mstore a w = m.mstore a w`) and disjoint-offset commute,
     to re-factor each level's chain into the 4-store `AddressShape` form with
     `pkSeed@0x380` in front (the A2 leaf value theorem
     `tree_leaf_node_value_eq_leafHash` shows the wiring pattern).
  2. **A4 induction**: `loop_step` (InterpLoop) + `exec_tree_body_iter` +
     `exec_tree_post`, invariant: `usr_t=k`, `usr_treePtr/rootPtr/tLeafBase`
     advanced, `usr_dCursor = dVal>>5k`, `mem[0x40+32j]=root_j (j<k)`,
     `pkSeed@0x380`, `ret=32`, `ret_2=96`. The varstore reads go through
     `state_getElem_insert_{self,ne}` / `treePostState`'s insert chain.
  3. Feed `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`
     → `address_derivation_eq_overwrite` → `h_accept`.

## Sprint log (2026-06-10c) — tree loop A2 landed: the leaf-hash template

- **A2 DONE — `Bridge/TreeLeaf.lean`** (generic-fuel throughout; adds **zero**
  axioms — every theorem is Lean-core-only except the end-to-end value theorem,
  which uses exactly the existing `evm_keccak_leaf` + `ffi_kec_lt` +
  `ffi_zeroes_eq_empty` + `uint256_toByteArray_size`):
  - **Loop AST pinned**: `forsTreeCond`/`forsTreePost`/`forsTreeBody` (all 28 body
    statements) with `forsFunRecover_tree_for : forsFunRecover.body[32]? = some
    forsTreeFor := rfl` — proofs about `forsTreeBody` are about the real
    transcription.
  - **Leaf prefix executed**: `exec_tree_body_leaf_prefix` runs body statements
    0–2 (ADRS mstore @0x3a0, masked-sk mstore @0x3c0, leaf keccak `let`) on any
    `.Ok ss vs` at fuel `n+13` → `treeAfterLeafHash`. Reusable statement
    reducers: `exec_mstore_lit` (any `mstore(<lit>, <pure e>)`),
    `exec_let_masked_keccak_var_len`, `eval_keccak_lit_var`, plus the
    `multifill` normal forms (`multifill_nil_vars`/`multifill_single`).
  - **The bookkeeping bridge**: `treeAfterLeafSk_toMachineState` — the
    interpreter machine state after the two stores IS the `AddressShape` mstore
    chain (`rfl`!), plus varstore/`toState` preservation lemmas.
  - **The value**: `tree_leaf_node_value_eq_leafHash` — with the entry machine
    state factored as `m.mstore 0x380 pkSeed` (`hm`) and `ret_2 = 96` (`hlen`),
    the bound `usr_node` value `.toNat` = model `leafHash` (wiring:
    `masked_keccak_toNat` → `leaf_derivation_eq_overwrite`); the ADRS-word
    arithmetic stays a hypothesis (`hadrs`) for the A4 invariant to supply.
  - **A3 handoff**: `state_getElem!_eq_lookup!`,
    `state_getElem_insert_{self,ne}` (Finmap insert-lookup through `Yul.State`),
    `treeAfterLeafHash_getElem_usr_node` (reading `usr_node` back).
- **Gotchas found (real, will bite A3):**
  - `Identifier` is a **non-reducible `def`** of `String` → a raw string literal
    in `s["x"]!` does NOT trigger the `Yul.State` `GetElem` instance
    (`GetElem? Yul.State String` synthesis fails). Use the pre-typed constants
    (`tLeafBaseId`/`dCursorId`/`treePtrId`/`ret2Id`/`usrNodeId`) — they stay
    defeq to the literals the AST carries (verified: `eval_var` instances).
  - `default` is a **reserved token** in files importing `YulNotation` (the
    `switch`-default syntax) — write `Inhabited.default` in terms.
  - `decide` on `UInt256` `.toNat` facts blows the heartbeat budget — use the
    `uint256_ofNat_toNat` bridge (mirrors `EvmMemory`'s private lemma) with a
    cheap `Nat` bound `decide`.
  - `InterpOps` `primCall_*` take `s` **implicitly**; `InterpState`'s take it
    explicitly.
- **Next (A3)**: the five node hashes mirror the template. Per level: evaluate the
  selector `usr_s_k` (pure ops over `usr_dCursor`/`ret`), the ADRS store @0x3a0
  (`exec_mstore_lit` + a `treeNodeAdrsStmt` eval), the two swap stores at
  `xor(0x3c0, s)`/`xor(0x3e0, s)` (needs an `exec_mstore_expr` variant for
  non-literal offsets), the node keccak (`keccak256(0x380, 128)` — add a
  lit-lit masked-keccak `let` reducer), then
  `node_derivation_eq_climbLevel_{even,odd}_overwrite` keyed on the `usr_s`
  swap value (`usr_s ∈ {0, 32}` ↔ even/odd `pathIdx`). Then A4: thread
  `treeAfterLeafHash` through one full body → `loop_step` induction with the
  invariant (pkSeed factoring across iterations needs an mstore-commute or an
  extract-based re-factoring lemma — not yet built).

## Sprint log (2026-06-10b) — scoped to `fun_recover`; tree loop started

- **Strategic pivot — scope to `fun_recover`** (`EvmRunRecover.lean`). The dispatcher's
  eager `switch` + fuel-monotonicity (incl. the `execSwitchCases` non-mono crux) are
  *off the critical path*. `evmRunRecover` runs `fun_recover` directly; the dispatcher
  routing is **one explicit, dischargeable axiom** `dispatcher_routes_to_recover`
  (historical note: discharged on 2026-06-14 by `DispatcherRoute.lean`). The target
  is now `fun_recover`'s recovery logic, where the value is.
- **Tree-loop foundation** (`InterpLoop.lean`): the `for`-loop step lemmas
  (`exec_for`/`loop_exit`/`loop_step`/`loop_cond_err`) — the induction scaffolding.
- **THE tree loop (next, the multi-week core).** `fun_recover`'s `for { } lt(usr_t,25)
  {post} {body}`:
  1. **Per-iteration body**: each iteration computes leaf + 5 `climbLevel` node hashes
     (6 `keccak256`s) → connect each to the model via the **already-proved**
     `leaf_derivation_eq_model_leaf_overwrite` /
     `node_derivation_eq_model_climbLevel_{even,odd}_overwrite` (`AddressShape.lean`),
     storing the root at `usr_rootPtr = 0x40 + 32·t`.
  2. **Invariant** after `k` iters: `usr_t=k`, pointers advanced, `usr_dCursor=dVal>>5k`,
     `mem[0x40+32·j]=root_j` for `j<k`, `pkSeed@0x380`.
  3. **Induct** over `25−k` via `loop_step` ⇒ all 25 roots in the buffer.
  4. Feed `roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init`
     (proved) ⇒ `compressRoots = recoverRoot`, then `address_derivation_eq_overwrite`
     ⇒ **`h_accept`**.
  Fuel threads generically per `loop_step` — **no monotonicity needed** (no switch).
- Reject branches (`h_len`/`h_guard`) against `evmRunRecover` are the easy warm-up.

## Sprint log (2026-06-10) — `h_len` sprint + a gap finding

- **T1 done** (`ClassALen.lean`): terminal-state → `evmRun=0` plumbing —
  `evmRun_zero_of_exec_revert` (revert ⇒ `none` ⇒ 0) and
  `evmRun_zero_of_exec_yulhalt_zero` (RETURN with zero `H_return` ⇒ 0), on top of
  the agent's `runForsCalldata_encode_unfold`. Green, axiom-free.
- **⚠ GAP FOUND — the `switch` is uncomposed.** The Class-A trace proves the recover
  *case-body* internals (offset/length/guards/recover-call) on named states
  (`dispatcherAfterFreeMemPtr`/`AfterOffset`/`AfterLength`), but **nothing connects
  `exec … forsDispatcher (forsInitialState)` through the `switch` into those states.**
  The furthest-up lemma (`exec_dispatcher_has_selector_if_after_free_mem_ptr`) stops
  at `exec (.Block body)` for an arbitrary `body`; the real `body = [switch …]` is
  never run. **So Class-A does not yet reach `evmRun`** — the eager-all-5-branches
  `switch` dispatch (run every case body, then `foldr`-select 0x1aad75c5) is the
  uncomposed blocker, and it sits upstream of `h_len`, `h_guard`, AND `h_accept`.
- **⚠ SECOND, DEEPER GAP — fixed-fuel fragments don't reach `evmRun`.** Every
  dispatcher/recover fragment is proved at a *fixed small fuel* (`exec 7/9/13`,
  `eval 2/4/…`), but `evmRun` runs `runForsCalldata … 100000`. There is **no
  fuel-monotonicity lemma**, so `exec 7 (mstore…)` cannot be used inside
  `exec 99999 (mstore…)` in the real run — the fragments do not compose up to fuel
  100000. *So no amount of additional case-body tracing reaches `evmRun` on its own.*
- **STRATEGIC FIX (do this FIRST — one lemma unlocks both gaps):** prove
  **fuel-monotonicity** of the interpreter:
  `exec n stmt co s ≠ .error .OutOfFuel → exec (n+1) stmt co s = exec n stmt co s`
  (+ analogues). Then every existing fixed-fuel fragment lifts to fuel 100000, and
  the switch composes without re-threading exact fuels.
  - **Progress (`FuelMono.lean`, 2026-06-10):** 9 conjuncts proven + committed (base
    case + the 5 wrappers + `eval`/`evalArgs`/`callDispatcher`/`call`) + the recursive
    template `exec_block_cons_mono`. Remaining core: `exec` (~13 cases), `loop`,
    `primCall` (CALL family).
  - **⚠ FINDING — `execSwitchCases` is NOT fuel-monotone (the eager-`switch` crux).**
    It *records* a case body's `OutOfFuel` as a branch and continues (doesn't
    propagate), so a body that OOFs at `n` but terminates at `n+1` breaks
    `execSwitchCases (n+1) = (n+2)` despite `≠OOF`. `MonoAt.switch` is false as stated.
    `exec` on `Switch` is still monotone (the `foldr` selects by static case value and
    ignores non-selected branches → only the selected body's `exec` matters), but it
    needs a **refined `foldr`-selection argument**, not `execSwitchCases`-mono. This is
    the genuine hard core of the eager dispatch.
  - **Mechanic VALIDATED** (2026-06-10): induction on `n`, `conv => rw [exec]`
    unfolds both fuel layers, the IH at `n` lifts the head, the `≠ OutOfFuel`
    precondition propagates through the `match`. The recursive `Block` case goes
    through. So this is *feasible*, not blocked.
  - **BUT it's a large all-or-nothing proof over the WHOLE mutual block** — not just
    `exec`/`eval`, but `primCall` (50+ opcodes) and, via `primCall`'s `CALL` case,
    `callDispatcher`. A single combined induction; no partial commit.
  - **Two paths:**
    (a) **Restricted pure-fragment monotonicity** (FORS-local): the contract is pure
        (no `CALL`/`SSTORE`/…), so a version scoped to the non-`CALL` opcodes avoids
        `callDispatcher` and the `CALL` family — medium-size, still all-or-nothing.
    (b) **Upstream the general lemma to `lfglabs-dev/EVMYulLean`** — it's a general
        interpreter property (belongs there, like the `toBytes'_le` de-privatization),
        benefits everyone, and strengthens our trust-surface story. **Recommended.**
- **Then the switch composition:** `forsDispatcher = Block[ mstore(64,128),
  If(iszero(lt(calldatasize,4)))[Switch(shr(224,calldataload 0)) [(0x1aad75c5=447575493,
  recoverBody), 4 getters] []], revert(0,0) ]`. Compose via `exec_switch_ok` +
  `execSwitchCases_*` + `foldr_switch_*` + `primCall_mload`: trace the 4 getter
  bodies to `YulHalt` (discarded by `foldr`, just must not `OutOfFuel`), reuse the
  recover trace, select 0x1aad75c5. Then `h_len`'s two reject branches assemble on top.

## Agent progress (2026-06-07)

- Added `ClassA.eval_dispatcher_offset_bound_guard_after_offset` and
  `exec_dispatcher_offset_bound_if_after_offset`, proving the selected recover
  case skips `if gt(offset, 0xffffffffffffffff) { revert(...) }` after
  `offset := calldataload(4)`.
- Added `ClassA.eval_dispatcher_offset_min_calldata_guard_after_offset` and
  `exec_dispatcher_offset_min_calldata_if_after_offset`, proving encoded calldata
  skips `if iszero(slt(add(offset, 35), calldatasize())) { revert(...) }`.
- Added `ClassA.exec_dispatcher_let_length_after_offset`, binding
  `length := calldataload(add(4, offset))` to `UInt256.ofNat raw.len` in the
  selected recover case.
- Added `ClassA.exec_dispatcher_length_bound_if_after_length`, a reusable
  conditional skip for `if gt(length, 0xffffffffffffffff) { revert(...) }`, plus
  the `raw.len = SigLen` specialization
  `exec_dispatcher_length_bound_if_after_length_of_sigLen`.
- Added `ClassA.exec_dispatcher_payload_bound_if_after_length_of_sigLen`, proving
  the `raw.len = SigLen` path skips
  `if gt(add(add(offset, length), 36), calldatasize()) { revert(...) }`.
- Added `ClassA.evalArgs_dispatcher_recover_call_after_length_of_sigLen`, reducing
  the selected recover call arguments to
  `[UInt256.ofNat 100, UInt256.ofNat SigLen, UInt256.ofNat digest]` after reversal.
- Added `ClassA.exec_dispatcher_let_recover_call_args_after_length_of_sigLen`,
  reducing the selected recover `let ret := fun_recover(...)` statement to
  `execCall` with the concrete arguments above.
- Added compact names for the good `fun_recover` handoff state:
  `dispatcherBeforeRecoverState`, `recoverGoodArgs`, and `recoverEntryState`, plus
  the `call_ok` side conditions `dispatcherBeforeRecoverState_account_find` and
  `forsVerifierRuntime_lookup_fun_recover`.
- Added `Interp.exec_let_lit` and `Interp.exec_let_var`, the simple statement
  reducers needed to start stepping `fun_recover`'s literal and variable
  assignments.
- Added `ClassA.recoverEntryState_lookup_sig_offset`,
  `recoverEntryState_lookup_sig_length`, `recoverEntryState_lookup_digest`, and
  `exec_recover_var_init`, establishing the good `fun_recover` entry parameters
  and stepping its first body statement `var := 0`.
- Added `ClassA.recoverAfterVarInit_account_find` and
  `forsVerifierRuntime_lookup_const_sig_len`, the `call_ok` side conditions for
  the next `let expr := constant_FORS_SIG_LEN()` step in `fun_recover`.
- Added `InterpCall.exec_let_call_noargs` and
  `ClassA.exec_recover_let_expr_const_call_args`, reducing
  `let expr := constant_FORS_SIG_LEN()` to an `execCall` with an empty argument
  vector after `fun_recover`'s first statement.
- Added `Bridge/ClassAConst.lean` and registered it in `lakefile.lean`.
  `exec_const_sig_len_prefix_to_ret1_product` steps the first eight statements of
  `constant_FORS_SIG_LEN()` through `ret_1 := product`, leaving execution at
  `forsConstSigLen.body.drop 8`.
- Extended `ClassAConst` with `exec_const_sig_len_through_first_guard`, which
  computes `sum := add(32, product)` as `2432` and skips the first
  `constant_FORS_SIG_LEN()` overflow guard.
- Completed `constant_FORS_SIG_LEN()` execution in `ClassAConst`:
  `exec_const_sig_len_body` runs the helper body from the good `fun_recover`
  call entry and ends in `constAfterRet` with `ret = SigLen`.
- Added `exec_recover_const_sig_len_call` and `exec_recover_let_expr_const`,
  proving the `fun_recover` statement `let expr := constant_FORS_SIG_LEN()`
  returns to the recover frame with `expr = SigLen`.
- Added `Bridge/ClassARecover.lean` and registered it in `lakefile.lean`.
  `exec_recover_ret_init_after_expr` steps the good `fun_recover` path through
  `ret := 0; ret := 0x20` after `expr = SigLen`.
- Extended `ClassARecover` with `exec_recover_prefix_to_ret1_product`, stepping
  the following straight-line `fun_recover` setup through `ret_1 := product` and
  leaving execution at `forsFunRecover.body.drop 12`.
- Added `ClassARecover.exec_recover_through_length_guard`, computing
  `sum := add(ret, product)`, skipping the setup overflow guard, binding
  `ret_3 := ret_2`, and proving the good path skips
  `if iszero(eq(var_sig_length, expr)) { var := 0; leave }`.
- Added `ClassARecover.eval_recover_pkSeed_calldata_offset`, the pure offset
  arithmetic for the next calldata read:
  `add(var_sig_offset, 0x10) = 116` after the good length guard.
- Added `ClassARecover.eval_recover_high16_mask`,
  `eval_recover_hmsg_domain_word`,
  `eval_recover_counter_calldata_base`, and
  `eval_recover_counter_calldata_offset`, proving the reusable hmsg setup
  constants and the trailer/counter read offset
  `add(add(var_sig_offset, product), ret) = 2532`.
- Added `CalldataBytes.forsPayloadChunk` plus
  `encodeForsCalldata_readBytes_payload_pair_1` and
  `calldataload_encode_payload_pair_1`, proving that calldata offset `116`
  reads the exact payload chunk pair `(raw.read16 16, raw.read16 32)` at the byte
  level. Connected this to `fun_recover` with
  `ClassARecover.eval_recover_pkSeed_calldataload_pair`.
- Added the out-of-bounds calldata tail-read lemma `readBytes_tail_16`, the
  counter chunk extraction `forsPayload_extract_counter`, and
  `calldataload_encode_counter`, proving the hmsg counter read at calldata offset
  `2532` is the final payload chunk plus 16 zero padding bytes. Connected it to
  `fun_recover` with `ClassARecover.eval_recover_counter_calldataload`.
- Added `forsPayload_extract_chunk_pair_0`,
  `encodeForsCalldata_readBytes_payload_pair_0`, and
  `calldataload_encode_payload_pair_0`, proving calldata offset `100` reads the
  exact payload chunk pair `(raw.read16 0, raw.read16 16)` at the byte level.
  Connected this to `fun_recover` with
  `ClassARecover.eval_recover_r_calldataload_pair`.
- Added `ClassARecover.recoverPkSeedWord` and
  `eval_recover_pkSeed_masked`, proving the full
  `and(calldataload(add(var_sig_offset, 0x10)), not(low16mask))` expression
  evaluates to the concrete contract-side masked pkSeed word.
- Added `ClassARecover.recoverRWord`, `recoverCounterWord`,
  `eval_recover_r_masked`, and `eval_recover_counter_masked`, completing the
  same contract-side masked-word evaluation for the hmsg R and counter inputs.
- Verified `lake build NiceTry` green. Axiom audit for the offset-bound guard step
  is only Lean's standard axioms; the calldata-size guard step additionally uses
  the existing `uint256_toByteArray_size` codec axiom through
  `encodeForsCalldata_size`. The length binding stays inside the existing
  calldata-read trust surface (`ffi_zeroes_eq_empty`,
  `uint256_toByteArray_roundtrip`, `uint256_toByteArray_size`). The good-length
  length-bound guard specialization uses only Lean's standard axioms. The
  good-length payload-bound guard uses `uint256_toByteArray_size` through
  calldata size. The recover-call argument reduction stays inside the existing
  calldata-read trust surface; so does the statement-level `execCall` handoff.
  The new `call_ok` side conditions use only Lean's standard axioms.
  `exec_let_lit` and `exec_let_var` also use only Lean's standard axioms.
  The new `recoverEntryState_*` facts and `exec_recover_var_init` use only Lean's
  standard axioms. The constant-call side conditions use only Lean's standard
  axioms. The no-argument call reducer and concrete constant-call handoff also
  use only Lean's standard axioms. The constant-getter prefix theorem uses only
  Lean's standard axioms, as does the first-guard theorem. The full constant
  getter body theorem also uses only Lean's standard axioms. The constant call
  return to the recover frame also uses only Lean's standard axioms. The first
  recover-body theorem and the recover setup-prefix theorem use only Lean's
  standard axioms. The recover internal length-guard theorem and pkSeed offset
  theorem also use only Lean's standard axioms.
- Next: continue the good `fun_recover` path into the calldata reads and memory
  writes for `usr_pkSeed`, `r`, `digest`, and the hmsg/forced-zero prelude.

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
  git checkout -B agent/phase4-integration --track solvency/agent/phase4-integration
  ```
- **Branch:** current development is on `agent/phase4-integration`, which contains
  the completed `phase4_forsRefines` theorem.
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

All of the following is committed on `agent/phase4-integration`,
**`sorry`/`admit`-free**,
with **2 labeled project axioms declared** on this branch (verify with
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
| Padding + word codec | `Bridge/EvmFfiSpec.lean` | ✅ all five former axioms discharged as theorems |
| Keccak FFI shape | `Bridge/InterpKeccak.lean` | ✅ one explicit `ffi_kec_size` axiom; numeric bound proved |
| SoLean oracle discharge + sufficiency | `Bridge/Oracle.lean`, `Bridge/Equivalence.lean` | ✅ `refinement_discharges_oracle`, `refinement_matches_forsAccept` |
| Deployed dispatcher route | `Bridge/DispatcherRoute.lean` | ✅ selector, ABI guards, eager switch, recover call, and malformed-length outcomes proved |

**The 2 trust-base axioms declared on this branch:** `evm_keccak_transcript`
(`AddressShape.lean`) + `ffi_kec_size` (`InterpKeccak.lean`).
`phase4_forsRefines` uses both.

> Net: the per-shape "every hash step is the right one" guarantee is **proved**.
> The complete reviewed runtime-execution spine connecting those steps is also
> **proved**. Source-to-transcription correspondence remains a review boundary.

## 3. What is OPEN — the remaining frontier

The deployed refinement is assembled. Remaining work reduces the explicit trust
surface or expands certification to the auxiliary Verity kernel; it is no longer
needed to establish `phase4_forsRefines`.

### WS-1 · Class-A / reject paths and dispatcher — ✅ **DONE**
The ABI byte library, reject branches, direct recover call, and full deployed
dispatcher trace are proved. `DispatcherRoute.lean` composes the eager switch,
ABI guards, and `fun_recover` call for both valid and malformed lengths.
- **Foundation in place:**
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
  - `CalldataBytes.lean`, `ClassA*.lean`, and `TreeCalldata.lean` now cover the
    calldata layout, dispatcher words, masked header/payload reads, and model-opening
    values. Do not rebuild this layer.

### WS-2 · M4 execution assembly — ✅ **DONE**
`Phase4Accept.lean` and `Phase4Reject.lean` close the three observable branches
through `call`/`runForsRecover`/`evmRunRecover`.

### WS-3 · The FORS tree loop  — ✅ **DONE**
`TreeLeaf.lean` through `TreeLoop.lean` prove the real loop end to end: execution
of all six hashes per iteration, the invariant and arithmetic, 25-step induction,
and all root-buffer writes. `TreeCalldata.lean` supplies the model-opening values,
and `Phase4Accept.lean` now connects those values to `recoverRoot`. Do not
reimplement the induction.

### WS-4 · Assemble deployed refinement — ✅ **DONE**
`forsRefines_of_branches` reduces `ForsRefines` to exactly three interpreter-run
obligations — `h_len` (bad length → `address(0)`), `h_guard` (forced-zero reject →
`address(0)`), `h_accept` (otherwise `= addressFromRoot pkSeed (recoverRoot …)`).
All model-side glue (the `recoverRaw?` case-split + `none ↔ address(0)`) is proved;
adds **zero trust** (`#print axioms` = `propext/Classical.choice/Quot.sound`).
`Phase4.lean` instantiates all three obligations and exports
`phase4_forsRefines : ForsRefines`. `ForsRefines` and `RefinesModel` now use the
truthful `ForsAbiInput` domain.

### Verity accounting boundary
Nine of the eleven Verity `local_obligations` are backed by real Lean theorems.
The remaining two kernel-loop choreography labels are deliberately held because
the equivalent deployed-contract induction is already proved in `TreeLoop.lean`.

---

## 4. Suggested grab order
- **First:** upstream a public EVMYulLean word-codec theorem so
  `EvmFfiSpec.lean` no longer reaches a private declaration by generated name.
- **Second:** decide whether `ffi_kec_size` remains the explicit extern-C
  contract or is replaced by a proved link from `ffi.KEC` to a modeled Keccak.
- **Then:** revisit the two held kernel obligations only if certifying the
  auxiliary generated kernel becomes a project requirement.

## 5. Build status of this branch
- **`lake build NiceTry` — verified green (2026-06-14):** 1172 modules built,
  no errors, and the three
  `#check_contract ok` for the Verity kernels.
- **Axiom audit (`#print axioms`) — clean:** no `sorryAx` anywhere. The bridge
  `phase4_forsRefines` depends only on Lean's
  `propext / Classical.choice / Quot.sound` plus
  `evm_keccak_transcript / ffi_kec_size`.
  The dispatcher route is proved and adds no trust.
  The sufficiency theorem `refinement_discharges_oracle` is pure logic (`[propext]`).
- Reminder: a bare `lake build` (no target) compiles nothing and still exits 0 — see
  §1. Always build `NiceTry` and re-run the axiom audit after touching the Bridge.
