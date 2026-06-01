# FORS+C verifier — open obligations & discharge plan

Status snapshot (cloned `fors-verity-model`, this session):

- **Structural Lean proofs: fully closed.** `grep -rn 'sorry\|admit' NiceTry/Fors` → 0 hits.
- **Open work: 12 `local_obligations`**, all `proofStatus := .assumed`, all at the
  Verity→Yul boundary. A Verity `LocalObligation` is `{name, obligation: String,
  proofStatus}` (`Compiler/CompilationModel/Types.lean:338`) — an **accounting flag,
  not a checked proof term**. Discharging one = write a real Lean refinement lemma
  against the EVMYulLean memory model, then flip `.assumed → .proved`.

## The 12 obligations

| # | Site | Name | Claim |
|---|------|------|-------|
| 1 | `Verity/TreeKeccakKernel.lean:46` | `keccak_memory_refinement` | leaf: `mem[0x380..0x3df] = pkSeed‖ADRS‖sk`, top-16 masking |
| 2 | `Verity/TreeKeccakKernel.lean:59` | `keccak_memory_refinement` | node: `mem[0x380..0x3ff] = pkSeed‖ADRS‖left‖right` |
| 3 | `Verity/FullVerifierKernel.lean:50` | `hmsg_keccak_memory_refinement` | `mem[0x00..0x9f] = pkSeed‖R‖digest‖dom_FORS‖counter` |
| 4 | `Verity/FullVerifierKernel.lean:78` | `keccak_memory_refinement` | leaf transcript (= #1) |
| 5 | `Verity/FullVerifierKernel.lean:91` | `keccak_memory_refinement` | node transcript (= #2) |
| 6 | `Verity/FullVerifierKernel.lean:135` | `raw_calldata_refinement` | `sigData` → first payload byte; `byteOffset` ∈ FORS layout offsets |
| 7 | `Verity/FullVerifierKernel.lean:141` | `roots_keccak_memory_refinement` | `mem[0x00..0x35f] = pkSeed‖ADRS_roots‖root_0..root_24` |
| 8 | `Verity/FullVerifierKernel.lean:149` | `address_keccak_memory_refinement` | `mem[0x00..0x3f] = pkSeed‖pkRoot` |
| 9 | `Verity/FullVerifierKernel.lean:160` | `full_verifier_memory_refinement` | typed choreography: preserves pkSeed, writes 25 roots at `0x40+32·t`, scratch ≥ `0x380` |
| 10 | `Verity/FullVerifierKernel.lean:199` | `full_raw_verifier_memory_refinement` | raw choreography (= #9 from decoded raw) |
| 11 | `Verity/FullVerifierKernel.lean:230` | `raw_abi_parse_refinement` | ABI reads = `recover(bytes,bytes32)`: `cd[4]`=offset, `cd[4+off]`=len, `cd[4+off+32]`=data |

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
  matching `opaque keccakWord/keccakHash16/keccakAddress` in `Fors/Hash.lean`.

The bridging axioms to state explicitly (and keep auditable): EVMYulLean
`keccak256(off,len)` over a region equal to `encode(fields)` = the model's
`keccakWord/Hash16/Address fields`. In the current Bridge these are the labeled
`evm_keccak_*` axioms in `AddressShape.lean`; all byte-region facts feeding them
are mechanical memory reasoning. The roots bridge currently covers the 27-word
compression input for abstract root values; the loop proof that computes those
values remains Class-C work. The current handoff target is
`roots_derivation_eq_after_loop_buffer_init`: the loop must supply the 25 root
values, after which the bridge proves the local memory layout, size preservation,
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
