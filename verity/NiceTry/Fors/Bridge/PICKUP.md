# FORS+C verifier bridge — START HERE (pick-up guide)

## Trust surface (12 labeled axioms — `#print axioms` shows only these + Lean core)

None are hardness assumptions. Verify with `#print axioms <thm>`.
- **keccak (5)** — `evm_keccak_{address,hmsg,leaf,node,roots}` (`AddressShape.lean`): the
  kickoff "keccak is trusted" decision; each currently also folds the 16-byte masking
  (Gap-B, to be split into a keccak-only axiom + a proved masking lemma).
- **FFI memory padding (3)** — `ffi_zeroes_{size,get!,eq_empty}` (`EvmFfiSpec.lean`):
  total-correctness specs of the opaque `ffi.ByteArray.zeroes`; not crypto.
- **word-codec (2)** — `uint256_toByteArray_{size,roundtrip}` (`EvmFfiSpec.lean`):
  true, provable-but-upstream-`private`; discharge via an EVMYulLean PR.
- **keccak output size (1)** — `ffi_kec_lt` (`InterpKeccak.lean`): `ffi.KEC` value `< 2²⁵⁶`;
  total-correctness spec, same upstream PR.
- **dispatcher routing (1)** — `dispatcher_routes_to_recover` (`EvmRunRecover.lean`): the
  `fun_recover`-scoping assumption; dischargeable via the switch composition + the
  remaining fuel-monotonicity.

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
  (boilerplate, not crypto — discharge later via the switch composition). The target
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
