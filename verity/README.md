# FORS+C Verifier Formal Verification

This directory contains the Lean proof that the complete EVMYulLean execution
of the runtime parsed from pinned `ForsVerifier` optimized Yul refines the
FORS+C recovery model.

Start with:

- [`../docs/antonio-briefing.md`](../docs/antonio-briefing.md) for the
  plain-English production verdict and go/no-go checklist;
- [`NiceTry/Fors/Bridge/REVIEW_PATH.md`](NiceTry/Fors/Bridge/REVIEW_PATH.md)
  for the step-by-step path from FORS model to EVMYulLean execution to pinned
  artifact;
- [`NiceTry/Fors/Bridge/ReviewSurface.lean`](NiceTry/Fors/Bridge/ReviewSurface.lean)
  for the small set of theorem statements reviewers should read first;
- [`NiceTry/Fors/Bridge/VERIFICATION_REPORT.md`](NiceTry/Fors/Bridge/VERIFICATION_REPORT.md)
  for the reviewer-facing claim, assumptions, provenance, and sign-off request;
- [`NiceTry/Fors/Bridge/PICKUP.md`](NiceTry/Fors/Bridge/PICKUP.md) for the
  engineering handoff;
- [`NiceTry/Fors/Bridge/OBLIGATIONS.md`](NiceTry/Fors/Bridge/OBLIGATIONS.md) for
  the separate auxiliary-kernel obligation accounting.

## Review theorem

The reviewer-facing theorem avoids hiding the checked runtime behind an
existential:

```lean
NiceTry.Fors.Bridge.pinned_yul_runtime_matches_recover_model :
  parseDeployedRuntime pinnedForsOptimizedYul = .ok forsVerifierRuntime ∧
    ∀ raw digest, ForsAbiInput raw digest →
      evmRunWithRuntime forsVerifierRuntime raw digest =
        recoverOrZero raw digest
```

In plain English: the tracked optimized-Yul artifact parses to the runtime Lean
executes, and that runtime returns the same address as the clean FORS+C recovery
model, with model failure represented as `address(0)`.

The underlying execution theorem is:

```lean
NiceTry.Fors.Bridge.phase4_forsRefines :
  NiceTry.Fors.Bridge.ForsRefines
```

The compiler-artifact theorem is:

```lean
NiceTry.Fors.Bridge.pinned_optimized_yul_refines :
  ∃ runtime,
    parseDeployedRuntime pinnedForsOptimizedYul = .ok runtime ∧
    ForsRuntimeRefines runtime
```

Expanded internally:

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

The optimized-Yul-to-runtime link is kernel checked. A total Lean parser imports
the tracked raw `forge inspect ... irOptimized` artifact and proves that the
result is exactly `forsVerifierRuntime`, the stable scaffold used by the
execution proof.

The remaining provenance boundaries are pinned `solc 0.8.30` and the requirement
to compare deployed bytecode with the pinned compiler output.

The theorem covers the verifier component. A production deployment must also
prove bytecode identity, compare the recovered address to the expected owner,
and enforce the FORS few-time-key lifecycle.

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
- correctness of the Solidity compiler.
