# FORS+C Verifier Formal Verification

This directory contains the Lean proof that the complete EVMYulLean execution
of the reviewed optimized-Yul transcription of `ForsVerifier.recover` refines
the FORS+C recovery model.

Start with:

- [`NiceTry/Fors/Bridge/VERIFICATION_REPORT.md`](NiceTry/Fors/Bridge/VERIFICATION_REPORT.md)
  for the reviewer-facing claim, assumptions, provenance, and sign-off request;
- [`NiceTry/Fors/Bridge/PICKUP.md`](NiceTry/Fors/Bridge/PICKUP.md) for the
  engineering handoff;
- [`NiceTry/Fors/Bridge/OBLIGATIONS.md`](NiceTry/Fors/Bridge/OBLIGATIONS.md) for
  the separate auxiliary-kernel obligation accounting.

## Final theorem

```lean
NiceTry.Fors.Bridge.phase4_forsRefines :
  NiceTry.Fors.Bridge.ForsRefines
```

Expanded:

```lean
∀ raw digest, ForsAbiInput raw digest →
  evmRun raw digest = (recoverRaw? raw digest).getD 0
```

`evmRun` ABI-encodes the input, executes the full dispatcher and
`fun_recover`, and decodes the returned address. The proof covers:

- selector dispatch and ABI bounds checks;
- bad-length rejection;
- Hmsg construction and forced-zero rejection;
- all 25 FORS tree openings, including sibling ordering and ADRS arithmetic;
- roots compression;
- final low-160-bit address derivation and return.

## Trust boundary

The final theorem depends on Lean core plus exactly two project axioms:

- `evm_keccak_transcript`
- `ffi_kec_size`

Padding, word encoding/decoding, the Keccak numeric bound, dispatcher routing,
and the complete interpreter traces are proved.

The source-to-runtime link is a review boundary: `forsVerifierRuntime` is a
pinned transcription of `forge inspect ... irOptimized`, not an AST generated
by a kernel-checked Solidity compiler bridge. The audit script detects drift
but does not claim semantic equality from hashes alone.

## Reproduce

Prerequisites:

- Foundry with `forge`
- Lean toolchain from `lean-toolchain`
- dependencies fetched by Lake
- `rg` and OpenSSL

From the repository root:

```bash
chmod +x scripts/audit-fors-verifier.sh
./scripts/audit-fors-verifier.sh
```

Or run the proof checks directly:

```bash
cd verity
lake build NiceTry
lake env lean NiceTry/Fors/Bridge/Audit.lean
```

Always build the named `NiceTry` target. A bare `lake build` has no default
target in this package and can exit successfully without compiling the proof.

## Auxiliary Verity artifacts

The repository also contains generated Verity kernels and Foundry replay
artifacts. Nine of their eleven accounting obligations are backed by Lean
theorems. Two full-loop choreography obligations remain documented for those
auxiliary artifacts.

Those two labels are not dependencies of `phase4_forsRefines`; the complete
loop is proved separately for the reviewed `forsVerifierRuntime` that the final
theorem executes.

## Non-claims

This work does not prove:

- Keccak cryptographic security or implementation correctness;
- FORS unforgeability or q-signature security bounds;
- correctness of the off-chain signer;
- semantic equivalence of arbitrary deployed bytecode to the pinned Solidity
  source;
- semantic correctness of the manual optimized-IR transcription beyond the
  explicit review and drift-check boundary.
