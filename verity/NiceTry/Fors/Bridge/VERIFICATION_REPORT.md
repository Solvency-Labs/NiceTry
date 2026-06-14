# FORS+C Verifier Verification Report

**Review target:** Antonio Sanso
**Date:** 2026-06-14
**Proof branch:** `agent/phase4-integration`
**Proof checkpoint:** `dad41cf89770d2c46672a849fd40fc51e0d31c57`

## Executive conclusion

The Lean development proves functional correctness of the complete
`recover(bytes,bytes32)` execution represented by `forsVerifierRuntime`,
including dispatcher and ABI guards, malformed-length rejection, the grinding
guard, all 25 FORS tree reconstructions, roots compression, address derivation,
and the final return.

The exported result is:

```lean
theorem phase4_forsRefines : ForsRefines
```

where:

```lean
def ForsRefines : Prop :=
  ∀ (raw : RawSig) (digest : Digest), ForsAbiInput raw digest →
    evmRun raw digest = (recoverRaw? raw digest).getD 0
```

The appropriate short claim is:

> The EVMYulLean execution of the reviewed optimized-Yul transcription of
> `ForsVerifier.recover` refines the Lean FORS+C recovery model on every
> ABI-representable input, conditional on two explicit Keccak boundary
> assumptions.

It is not yet a kernel-checked proof that arbitrary production bytecode was
generated from the reviewed Solidity source. The Solidity-to-Lean runtime
transcription remains an explicit review boundary.

## What is proved

For every `raw` and `digest` satisfying `ForsAbiInput`:

1. The full dispatcher recognizes selector `0x1aad75c5`, checks the ABI bounds,
   decodes the dynamic byte offset, length, and digest, and calls
   `fun_recover(100, raw.len, digest)`.
2. A signature length other than 2448 returns `address(0)`.
3. The five-word Hmsg input is assembled correctly.
4. Failure of the FORS+C forced-zero grinding condition returns `address(0)`.
5. On acceptance, each of the 25 real FORS trees performs one leaf hash and
   five correctly ordered authentication-path node hashes.
6. The 25 roots are written to the intended root buffer and compressed.
7. The returned low-160-bit address equals the model's
   `addressFromRoot pkSeed (recoverRoot ...)`.

The proof executes the actual EVMYulLean dispatcher and function bodies. It does
not replace the loop with a high-level oracle.

## Exact input domain

`ForsAbiInput raw digest` is the conjunction of:

- `raw.len < 2^256`, because ABI `bytes.length` is one EVM word;
- every modeled 16-byte signature chunk is encoded in the high half of a
  256-bit word without truncation;
- `digest < 2^256`, matching ABI `bytes32`.

This domain is necessary because the Lean model uses unbounded `Nat` values,
while EVM calldata words truncate modulo `2^256`.

## Assumption audit

`#print axioms NiceTry.Fors.Bridge.phase4_forsRefines` reports Lean core
principles plus exactly two project axioms:

1. `evm_keccak_transcript`: Keccak over the proved canonical EVM transcript
   bytes equals the model's opaque `keccakWord` on those fields.
2. `ffi_kec_size`: the C-backed EVMYulLean Keccak FFI returns exactly 32 bytes.

The following former assumptions are now proved theorems:

- `ffi_zeroes_size`
- `ffi_zeroes_get!`
- `ffi_zeroes_eq_empty`
- `uint256_toByteArray_size`
- `uint256_toByteArray_roundtrip`
- `ffi_kec_lt`
- `dispatcher_routes_to_recover`

There is no `sorryAx` in the final theorem's dependency closure.

## Runtime provenance

The proof executes `forsVerifierRuntime` from `Bridge/ForsRuntime.lean`. That
runtime was transcribed from:

```bash
forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier irOptimized
```

using the repository's pinned configuration:

- Solidity `0.8.30`
- optimizer enabled
- optimizer runs `200`
- `via_ir = true`

Pinned fingerprints:

| Artifact | SHA-256 |
|---|---|
| `src/Verifiers/ForsVerifier.sol` | `f7dc82ec7019e4f2648c278f121d24713c709d805bcdc7cba892a871e04c903d` |
| generated optimized IR | `a5468ffa1ff600b5e0aca9e08f260e55ca8f3807503f365e2cf32eeac066bb8e` |
| `Bridge/ForsRuntime.lean` | `ae3412b2f7fb063938456db4b328a407e0061f9f447f56177442f71d0d91507e` |

The audit script rejects source, IR, or runtime drift. These hashes establish
review reproducibility, not semantic equality. A reviewer must still accept the
transcription or require a future parser/certificate that derives the
EVMYulLean AST directly from compiler output.

## Auxiliary Verity kernels

Nine of eleven `local_obligations` on the separate generated Verity kernels are
backed by real Lean theorems. The remaining two describe full-loop memory
choreography for those auxiliary generated kernels.

They are not assumptions of `phase4_forsRefines`: the equivalent 25-iteration
choreography is proved directly for `forsVerifierRuntime` in `TreeLoop.lean` and
`Phase4Accept.lean`. Re-proving it for the generated reference kernel would
certify a second artifact, not strengthen the dependency closure of the runtime
refinement theorem.

## Reproduce

From the repository root:

```bash
./scripts/audit-fors-verifier.sh
```

The script:

1. checks the Solidity source, generated optimized IR, and Lean runtime hashes;
2. confirms exactly two declared Bridge axioms;
3. runs `lake build NiceTry`;
4. prints the assumptions of the final theorem and supporting boundary lemmas.

Expected final theorem audit:

```text
NiceTry.Fors.Bridge.phase4_forsRefines depends on:
propext
Classical.choice
Quot.sound
NiceTry.Fors.Bridge.evm_keccak_transcript
NiceTry.Fors.Bridge.ffi_kec_size
```

## Requested sign-off

Please confirm whether the following is an acceptable verification boundary:

1. Functional/spec correctness, not a new proof of FORS unforgeability.
2. Keccak treated as an opaque primitive through `evm_keccak_transcript`.
3. The FFI's 32-byte result shape accepted through `ffi_kec_size`.
4. The pinned Solidity optimized-IR to EVMYulLean transcription accepted after
   review, rather than claimed as kernel-proved.
5. The two auxiliary-kernel loop obligations retained as documented,
   non-dependent boundaries.

If item 4 is not acceptable, the next milestone is narrowly defined: generate
or verify `forsVerifierRuntime` directly from pinned compiler output. The FORS
algorithm, ABI execution, reject paths, and complete accepting trace do not need
to be reproved.
