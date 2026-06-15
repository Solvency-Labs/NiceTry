# FORS+C verifier — open obligations & discharge plan

> **New here? Read [`PICKUP.md`](./PICKUP.md) first** — it has the remote/branch
> gotcha, build instructions, what's already proved, and the remaining work split
> into claimable workstreams. This file is the detailed obligation/discharge plan.

Status snapshot (`agent/phase4-integration`, 2026-06-14):

- **Structural Lean proofs: fully closed.** `grep -rn 'sorry\|admit' NiceTry/Fors` → 0 hits.
- **Hand-written runtime loop: fully closed.** The real 25-iteration
  `fun_recover` tree loop, per-tree calldata/model values, and all 25 root-buffer
  writes are proved in `Tree*.lean`.
- **Pre-loop trace: fully closed.** `TreeEntryFront.lean` executes the hmsg front
  half, proves its transcript value, and composes through `LoopInv 0`.
- **Deployed dispatcher route: fully closed.** `DispatcherRoute.lean` proves the
  selector switch, ABI guards, exact-fuel `fun_recover` call, and malformed-length
  outcomes. `dispatcher_routes_to_recover` is a theorem, not an axiom.
- **9 of 11 obligations discharged (2026-06-13).** All keccak-transcript memory
  obligations (#1–#5, #7, #8) and both Class-A calldata obligations (#6, #11) are
  now `proved`, each backed by a real Lean theorem: leaf/node/address by
  `kernel_*_keccak_memory_refinement` and the ABI parse by
  `kernel_recover_abi_parse` (new, in `Bridge/KernelRefinement.lean`); hmsg/roots
  by `hmsg_derivation_eq_overwrite` / `roots_derivation_eq_from_buffer` and the
  `rawWord` reads by `masked_calldataload_read16` (+ `_counter_`) (existing
  `AddressShape.lean` / `TreeCalldata.lean` lemmas that already match the kernel
  verbatim). Current axiom audit: only `evm_keccak_transcript`,
  `ffi_kec_size`, and Lean core; the padding and word-codec facts are proved
  theorems. No `sorry`.
- **Held boundary: 2 remaining `local_obligations`** (`proofStatus := .assumed`):
  `full_verifier_memory_refinement` (#9) and `full_raw_verifier_memory_refinement`
  (#10) — Class-C loop choreography on the auxiliary Verity kernel. The equivalent
  choreography is **already proven for the parser-certified runtime** (`tree_loop_run` +
  `Phase4Accept`, inside `phase4_forsRefines`); discharging the kernel copies would
  duplicate that whole induction for a reference artifact. **Decision: held as a
  documented boundary** (see the table notes below for the full rationale and
  cross-references). A Verity `LocalObligation` is `{name, obligation: String,
  proofStatus}` (`Compiler/CompilationModel/Types.lean:247`) — an **accounting
  flag, not a checked proof term**: the macro never inspects a proof. Discharging
  one honestly = write a real Lean refinement lemma and cite it in the
  justification, then flip `.assumed → .proved`.

## The 12 obligations

| # | Site | Name | Claim | Status |
|---|------|------|-------|--------|
| 1 | `Verity/TreeKeccakKernel.lean:46` | `keccak_memory_refinement` | leaf: `mem[0x380..0x3df] = pkSeed‖ADRS‖sk`, top-16 masking | ✅ `proved` — `kernel_leaf_keccak_memory_refinement` |
| 2 | `Verity/TreeKeccakKernel.lean:59` | `keccak_memory_refinement` | node: `mem[0x380..0x3ff] = pkSeed‖ADRS‖left‖right` | ✅ `proved` — `kernel_node_keccak_memory_refinement` |
| 3 | `Verity/FullVerifierKernel.lean:50` | `hmsg_keccak_memory_refinement` | `mem[0x00..0x9f] = pkSeed‖R‖digest‖dom_FORS‖counter` | ✅ `proved` — `hmsg_derivation_eq_overwrite` |
| 4 | `Verity/FullVerifierKernel.lean:78` | `keccak_memory_refinement` | leaf transcript (= #1) | ✅ `proved` — `kernel_leaf_keccak_memory_refinement` |
| 5 | `Verity/FullVerifierKernel.lean:91` | `keccak_memory_refinement` | node transcript (= #2) | ✅ `proved` — `kernel_node_keccak_memory_refinement` |
| 6 | `Verity/FullVerifierKernel.lean:135` | `raw_calldata_refinement` | `sigData` → first payload byte; `byteOffset` ∈ FORS layout offsets | ✅ `proved` — `masked_calldataload_read16` (+ `_counter_`) |
| 7 | `Verity/FullVerifierKernel.lean:141` | `roots_keccak_memory_refinement` | `mem[0x00..0x35f] = pkSeed‖ADRS_roots‖root_0..root_24` | ✅ `proved` — `roots_derivation_eq_from_buffer` |
| 8 | `Verity/FullVerifierKernel.lean:149` | `address_keccak_memory_refinement` | `mem[0x00..0x3f] = pkSeed‖pkRoot` | ✅ `proved` — `kernel_address_keccak_memory_refinement` |
| 9 | `Verity/FullVerifierKernel.lean:160` | `full_verifier_memory_refinement` | typed choreography: preserves pkSeed, writes 25 roots at `0x40+32·t`, scratch ≥ `0x380` | ⬜ assumed — Class-C (loop exec) |
| 10 | `Verity/FullVerifierKernel.lean:199` | `full_raw_verifier_memory_refinement` | raw choreography (= #9 from decoded raw) | ⬜ assumed — Class-C (loop exec) |
| 11 | `Verity/FullVerifierKernel.lean:230` | `raw_abi_parse_refinement` | ABI reads = `recover(bytes,bytes32)`: `cd[4]`=offset, `cd[4+off]`=len, `cd[4+off+32]`=data | ✅ `proved` — `kernel_recover_abi_parse` |

**9 of 11 discharged** (#1–#8, #11): all keccak-transcript memory obligations
(#1–#5, #7, #8) plus both Class-A calldata obligations (#6 via
`masked_calldataload_read16`/`_counter_`, #11 via `kernel_recover_abi_parse`).

**The remaining 2 (#9, #10) are held as a documented boundary — deliberately,
not for lack of a proof of the algorithm.** They assert the kernel `forEach`
loop's *executed* memory behaviour — pkSeed preserved, 25 roots written at
`0x40+32·t`, scratch non-overlap, and roots = the recovered values (composing the
per-tree leaf/node facts 25× over 6 levels). These are not closed
`mstore`/`calldataload` facts, so the MachineState memory-region template does not
apply.

The equivalent proof **already exists, complete, for the parser-certified
runtime** (`forsVerifierRuntime`) — the artifact `phase4_forsRefines` actually
certifies:

- `TreeLoop.lean:572` `tree_loop_run` / `:667` `tree_loop_run_from_zero` — the
  25-iteration loop induction: all 25 root slots hold the `loopRootV` hash-chain
  values, memory below `0x40` (pkSeed) untouched.
- `Phase4Accept.lean:178,217` — feeds that into
  `compressRoots_eq_recoverRoot` → `recoverRoot` → `addressFromRoot`.

The Verity kernels are a **separate, auxiliary artifact** (generated reference
Yul, exercised by Foundry replay/diff tests — see `README.md` "Branch Recap"
layer 3 and "What Is Not Covered"). Discharging #9/#10 would mean **re-deriving
the entire `TreeLoop` induction for the kernel's differently-generated Yul** — a
multi-week duplication of an already-complete proof, on an artifact that is not
the deployed bytecode. `tree_loop_run` is not reusable here: it runs the deployed
contract's specific Yul body through the EVMYulLean interpreter. The one shortcut
(prove kernel-Yul ≡ `forsVerifierRuntime`) is itself an explicitly-uncovered
boundary (`README.md`: "No proof that the optimized inline-assembly Solidity
verifier is equivalent … to the generated Verity Yul artifact").

**Decision (2026-06-13):** hold #9/#10 as `.assumed`. The cost (weeks of
duplicate proof) is not justified for a reference artifact when the choreography
is already proven for the parser-certified runtime. To revisit, the real task is a
kernel loop-execution model (the kernel analogue of `TreeLoop.lean`).

(11 named sites; #4/#5 duplicate #1/#2's transcript shape, so the table reads as the
12 `local_obligations` grep count with one shape shared.)

## Three proof classes

**Class M — per-keccak transcript memory (#1,2,3,4,5,7,8).** The atomic facts. Each
says: after the kernel's `mstore` sequence, the EVMYulLean memory region feeding a
`keccak256(off,len)` equals the abstract `List TranscriptField` from `Fors/Hash.lean`
(`leafTranscript`, `nodeTranscript`, `hMsgTranscript`, `rootsTranscript`,
`addressTranscript`), under the 16-byte top-half masking (`FORS_TOP_N_MASK`).

**Class C — choreography composition (#9,10).** Compose the Class-M facts across the
full run: pkSeed at `0x00`/`0x380` is never clobbered, the 25 roots land at `0x40+32·t`,
scratch (`0x380+`) never overlaps the roots buffer (`0x40..0x360`). The contract's three
`_GUARD` constants (A==5, scratch 64-aligned, `scratch ≥ ROOTS_HASH_LEN`) are the
side-conditions here.

**Class A — ABI calldata parsing (#6,11).** `recover(bytes,bytes32)` ABI decode:
selector + head/tail bytes encoding, `RawSig.read16 off = mem-word(payload+off) & mask`.

## EVMYulLean primitives to build against

- Execution: `EvmYul.Yul.exec` / `execTopLevel` (`EvmYul/Yul/Interpreter.lean:556,652`).
- Memory: `EvmYul.MachineState` (`MachineState.lean`) — `mstore`/`mload` via
  `MachineStateOps.lean`; reason about the byte map after a `mstore` sequence.
- Keccak: `EvmYul/SpongeHash/*` is the trusted primitive. **We do not prove keccak** —
  we prove its *input region* equals the transcript, then treat the digest as opaque,
  matching the shared opaque `keccakWord` and its defined hash/address masks in
  `Fors/Hash.lean`.

The bridging axiom to state explicitly (and keep auditable): EVMYulLean
`keccak256(off,len)` over a region equal to `encodeTranscript fields` = the
model's `keccakWord fields`. The current Bridge uses the single
`evm_keccak_transcript` axiom in `AddressShape.lean`; all five concrete
encodings, byte-region facts, and output masks are proved. The roots bridge
covers the 27-word compression
input, and `TreeLoop.lean` now proves that the real loop computes and writes the
required 25 root values. The current assembly target is
`roots_derivation_eq_after_loop_buffer_init`: composing those values with the
bridge proves the local memory layout, size preservation,
final roots ADRS overwrite, and `compressRoots` equivalence. The follow-on helper
`roots_derivation_eq_recoverRoot_after_loop_buffer_init` states the exact
pointwise loop obligation needed to rewrite that result to the typed model's
`recoverRoot`.

Pure model-side targets now named for the remaining raw/guard work:
`forcedZero_eq_evm_shape` pins the omitted-tree guard to `(dVal / 2^125) % 32`,
`decodeTyped_reads_raw_header` pins the raw header reads, and
`decodeOpening_reads_raw_fields` pins the per-tree `sk/auth0..auth4` offsets used
by the raw verifier loop. `rawOpenings_treeOpening_eq_decodeTyped_opening` links
the memory-boundary raw opening array back to the typed decoder, so the tree-loop
proof can move between raw calldata fields and `sig.openings`;
`reconstructTree_rawOpenings_eq_decodeTyped` carries that bridge through the
typed Merkle reconstruction call.

## Discharge order (each builds on the previous)

1. **Memory-region lemma library** — `mstore` sequence ⇒ byte-map equality, + the
   keccak-input bridging axiom. Reusable across all of Class M.
2. **Class M** (#1,2,3,4,5,7,8) — instantiate the library per transcript shape.
   Closing these is *exactly* the whole-contract memory-refinement content (see
   `Equivalence.lean`), so do them as named lemmas, not inline.
3. **Class C** (#9,10) — compose; non-overlap from the `_GUARD` constants.
4. **Class A** (#6,11) — ABI decoding; smallest, do last.
5. Flip each obligation `.assumed → .proved`; rebuild with
   `lake exe verity-compiler … --deny-local-obligations` (`CompileDriver.lean:33`)
   to enforce none remain.

## Key efficiency: don't do step 2 and step 3 separately

Class-M + Class-C lemmas *are* the per-keccak and choreography pieces of the
hand-written-contract equivalence (`Equivalence.lean`). Build them once as a shared
EVMYulLean memory-refinement library; the obligations consume them scoped to the Verity
kernel, the equivalence theorem consumes them scoped to `ForsVerifier.sol`'s asm.
