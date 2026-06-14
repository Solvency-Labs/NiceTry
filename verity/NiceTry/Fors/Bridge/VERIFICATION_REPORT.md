# FORS+C Verifier Production Safety Report

**Review target:** Antonio Sanso
**Date:** 2026-06-14
**Proof branch:** `agent/phase4-integration`
**Proof checkpoint:** `88f6798`

## Decision summary

| Question | Answer |
|---|---|
| Is the pinned verifier's FORS+C recovery computation correct? | **Yes, formally proved**, subject to the stated Keccak and transcription boundaries. |
| Does the proof cover the dispatcher, reject paths, and complete 25-tree loop? | **Yes.** |
| Does the proof establish that an arbitrary address contains the verified bytecode? | **No. Check each deployment.** |
| Does the proof establish the security of the signer, wallet, or key rotation? | **No. Those are separate production conditions.** |
| Is it reasonable to deploy and rely on this verifier? | **Yes, after every item in the production checklist is green.** |

## The exact statement we can present

> If the deployed `ForsVerifier` bytecode exactly matches the pinned artifact,
> the wallet accepts only when `recover(signature, digest)` equals its current
> nonzero owner, and the signer follows the required key-rotation policy, then
> we can rely on the verifier to enforce the modeled FORS+C recovery algorithm
> correctly, assuming Ethereum Keccak behaves correctly.

Do not broaden this into:

> The whole wallet is unconditionally formally verified and cannot be hacked.

The proof is strong, but it has a precise scope.

## What `recover` means

`ForsVerifier.recover` computes the signer address implied by a signature. It
does not return a boolean saying whether the signature belongs to a particular
account.

Malformed signatures of the correct length often recover a different nonzero
address. Therefore a caller must not accept merely because the result is
nonzero.

Unsafe:

```solidity
require(verifier.recover(signature, digest) != address(0));
```

Safe:

```solidity
address recovered = verifier.recover(signature, digest);
require(recovered != address(0) && recovered == currentOwner);
```

The repository's `SimpleAccount` uses the safe comparison.

## What is formally proved

The exported Lean result is:

```lean
theorem phase4_forsRefines : ForsRefines
```

Expanded:

```lean
def ForsRefines : Prop :=
  forall (raw : RawSig) (digest : Digest), ForsAbiInput raw digest ->
    evmRun raw digest = (recoverRaw? raw digest).getD 0
```

In plain language: for every ABI-representable signature and digest, executing
the complete reviewed verifier runtime returns exactly the address returned by
the Lean FORS+C recovery model.

The proof establishes all of the following:

1. Selector `0x1aad75c5` routes to `recover(bytes,bytes32)`.
2. The ABI dynamic offset, signature length, digest, and payload are decoded
   from the correct calldata positions.
3. A signature length other than 2,448 bytes returns `address(0)`.
4. `pkSeed`, `R`, `digest`, the FORS domain, and the counter are assembled into
   the correct 160-byte Hmsg input.
5. A failed FORS+C forced-zero grinding condition returns `address(0)`.
6. The accepting path executes 25 tree openings.
7. Every tree computes one leaf hash and five authentication-path node hashes.
8. Every left/right sibling decision follows the correct message-index bit.
9. Every ADRS tree number, height, and parent index matches the model.
10. The 25 roots are written to the correct memory slots and compressed over
    the correct 864-byte transcript.
11. The final address is the low 160 bits of the correct
    `keccak256(pkSeed || pkRoot)` input.
12. The returned EVM word equals the model's recovered signer address.

The loop is not replaced by a high-level assumption. The EVMYulLean
interpreter trace executes and proves all 25 iterations.

## Bugs this proof is designed to exclude

For the pinned artifact, the result excludes low-level implementation errors
such as:

- incorrect calldata offsets or masks;
- incorrect tree-opening offsets;
- wrong message-index extraction;
- wrong sibling ordering at any level;
- wrong ADRS fields;
- skipped, repeated, or miscounted loop iterations;
- memory overlap between roots and tree scratch space;
- wrong roots-compression input;
- wrong address mask;
- incorrect dispatcher or rejection behavior.

Ordinary tests sample inputs. This theorem quantifies over every input in the
represented ABI domain.

## Exact input domain

`ForsAbiInput raw digest` requires:

- `raw.len < 2^256`, because ABI `bytes.length` is one EVM word;
- every modeled 16-byte signature chunk is encoded in the high half of a
  256-bit word without truncation;
- `digest < 2^256`, matching ABI `bytes32`.

These are representation conditions, not restrictions on real Solidity calls.
Actual calldata already consists of finite bytes and 256-bit words. They are
needed because the Lean model uses unbounded natural numbers.

## What is not proved

### 1. Cryptographic unforgeability

The theorem proves that the implementation computes the specified FORS+C
recovery function. It does not independently prove the claimed security level
of FORS+C, Keccak collision resistance, or resistance to quantum attacks.

### 2. Safe key reuse

FORS is a few-time signature. The normal production path must use one signer
for one fresh UserOperation and rotate to a new owner. Replacement signatures
must be handled as explicit bounded reuse. Unlimited reuse is not safe merely
because the verifier implementation is correct.

### 3. The signer

The theorem does not prove that an off-chain signer generates correct secrets,
grinds the counter correctly, protects seed material, persists burn state, or
computes the wallet's exact digest.

### 4. The whole wallet

The theorem covers `ForsVerifier.recover`. It does not prove all behavior of
`SimpleAccount`, EntryPoint, bundlers, factories, recovery mechanisms, upgrade
logic, or deployment scripts.

### 5. Arbitrary deployed code

A theorem about the pinned artifact does not automatically apply to any
contract called `ForsVerifier`. The deployed bytecode must be checked.

## Explicit trust boundary

`#print axioms NiceTry.Fors.Bridge.phase4_forsRefines` reports Lean core
principles plus exactly two project assumptions:

1. `evm_keccak_transcript`: Keccak over the proved canonical EVM transcript
   bytes agrees with the model's opaque Keccak value.
2. `ffi_kec_size`: EVMYulLean's external Keccak implementation returns exactly
   32 bytes.

Padding, word encoding and decoding, the Keccak numeric bound, dispatcher
routing, rejection, memory layout, every tree iteration, roots compression,
and address derivation are proved.

There is no `sorryAx` in the final theorem's dependency closure.

## Compiler and transcription boundary

The proof executes `forsVerifierRuntime` from `Bridge/ForsRuntime.lean`. It was
reviewed against:

```bash
forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier irOptimized
```

using:

- Solidity `0.8.30`;
- optimizer enabled;
- optimizer runs `200`;
- `via_ir = true`.

The Solidity source, optimized IR, Lean runtime, and compiled deployed runtime
are fingerprinted. This makes drift visible and the review reproducible.

The optimized-Yul to EVMYulLean transcription is still a review boundary. It
is not yet produced by a kernel-checked parser or compiler certificate. If
Antonio requires that stronger provenance, the next milestone is to automate
or certify this link. The FORS execution proof itself does not need to be
repeated.

## Pinned artifact fingerprints

| Artifact | Fingerprint |
|---|---|
| `src/Verifiers/ForsVerifier.sol` SHA-256 | `aa6d44b994bdb5877863dd0400252649b03b48116f3da432bf4d932031436faf` |
| generated optimized IR SHA-256 | `531d8dd32a84ec56961bd4f220fce1466c533e40019e0729b97c6b328de21691` |
| `Bridge/ForsRuntime.lean` SHA-256 | `ae3412b2f7fb063938456db4b328a407e0061f9f447f56177442f71d0d91507e` |
| compiled deployed runtime length | `1,064 bytes` |
| compiled deployed runtime EVM code hash | `0x41345cf3e55d977f792efdfee943698c695c544d01d28dc0a9412eb7e3fca113` |
| runtime without 53-byte CBOR metadata EVM code hash | `0x1d49e8f4aa74b30f636d13659f46f59392cc5d6f2da2a2edbba8d66713d857b4` |

The June 14, 2026 upstream merge changed the inherited interface name and
source formatting. After source annotations and compiler metadata are removed,
the optimized Yul is byte-for-byte identical to the previously reviewed
artifact. The executable runtime before metadata is also identical.

## Production go/no-go checklist

All items must be green before presenting a deployment as verified:

1. `./scripts/audit-fors-verifier.sh` passes on the release commit.
2. `./scripts/check-deployed-fors-verifier.sh RPC_URL VERIFIER_ADDRESS`
   confirms an exact byte-for-byte match.
3. The wallet's immutable `VERIFIER` points to that checked address.
4. Every caller requires both a nonzero result and equality to the expected
   current owner.
5. The signer computes the exact digest consumed by the wallet.
6. The signer burns or retires a FORS key before releasing a fresh signature.
7. `nextOwner` is derived from the next prepared FORS public key and is included
   in the signed digest.
8. Replacement signatures follow a documented bounded-reuse policy.
9. The wallet integration and signer receive their own review and tests.

If any item fails, the formal verifier theorem remains true, but the production
system has not satisfied the conditions needed to rely on it safely.

## Reproduce the proof

From the repository root:

```bash
./scripts/audit-fors-verifier.sh
```

The script:

1. checks the source, optimized IR, Lean runtime, and compiled runtime code
   fingerprints;
2. confirms exactly two declared Bridge axioms;
3. runs `lake build NiceTry`;
4. prints the assumptions of the final theorem and supporting lemmas.

Expected final theorem audit:

```text
NiceTry.Fors.Bridge.phase4_forsRefines depends on:
propext
Classical.choice
Quot.sound
NiceTry.Fors.Bridge.evm_keccak_transcript
NiceTry.Fors.Bridge.ffi_kec_size
```

## Final recommendation

The verifier implementation is ready to be used as a production component
after the deployment identity check passes.

The complete wallet should be described as production-safe only after the
recover-and-compare integration, digest construction, and few-time-key
lifecycle are separately confirmed.
