import NiceTry.Fors.Bridge.Oracle
import NiceTry.Fors.Bridge.RawDomain

/-!
# Step 3 — `ForsVerifier.sol` ⊑ Lean model (EVMYulLean equivalence)

Goal: prove the deployed hand-written inline-assembly `recover(bytes,bytes32)`
refines the proved recovery model `recoverRaw?`. This file states the refinement
target and proves that hitting it *suffices* to discharge everything downstream
(the SoLean oracle). The EVMYulLean binding itself is the multi-week deliverable,
decomposed below; it is intentionally NOT stubbed with `sorry` — instead the open
content is named precisely so it can be filled against real EVMYulLean signatures.

This file compiles against the closed FORS proofs (it only imports `Bridge.Oracle`).
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors
open NiceTry.Fors.Spec
open NiceTry.Fors.Proofs.Basic

/-- The observable input/output behavior of a verifier contract:
    raw calldata signature + digest ↦ recovered signer (or `none`). The
    EVMYulLean instantiation (below) produces a term of this type by running
    `ForsVerifier.sol`'s runtime on ABI-encoded `recover(bytes,bytes32)` input
    and reading the returned word. -/
abbrev ContractRun := RawSig → Digest → Option Address

/-- The refinement target: the contract agrees with the model over the
    ABI-representable raw-signature domain. -/
def RefinesModel (run : ContractRun) : Prop :=
  ∀ raw digest, RawSigLenFitsEvmWord raw → run raw digest = recoverRaw? raw digest

/--
**Sufficiency (proved).** If the contract refines the model, then a legit FORS+C
signature makes the *contract* recover the expected address — i.e. the refinement
target is exactly strong enough to discharge SoLean's verifier oracle
(`forsAccept` / `PQVerifierWrapper`). So all proof effort can target `RefinesModel`.
-/
theorem refinement_discharges_oracle
    (run : ContractRun) (href : RefinesModel run)
    (raw : RawSig) (digest : Digest) (pkRoot : Hash16)
    (h : RawLegitSignatureFor raw digest pkRoot) :
    ∃ sig : TypedSig, decodeRaw raw = some sig ∧
      run raw digest = some (addressFromRoot sig.pkSeed pkRoot) := by
  obtain ⟨sig, hlen, hdecode, hlegit⟩ := h
  have hbound : RawSigLenFitsEvmWord raw := by
    unfold RawSigLenFitsEvmWord
    rw [hlen]
    norm_num [EvmYul.UInt256.size, SigLen, RLen, PkSeedLen, SectionLen, RealTrees,
      K, TreeLen, A, CounterLen]
  have hrec :
      recoverRaw? raw digest = some (addressFromRoot sig.pkSeed pkRoot) :=
    legit_raw_signature_recovers_expected_address raw digest sig pkRoot hlen hdecode hlegit
  exact ⟨sig, hdecode, by rw [href raw digest hbound]; exact hrec⟩

/-- Same, in boolean-oracle form: contract acceptance matches `forsAccept`. -/
theorem refinement_matches_forsAccept
    (run : ContractRun) (href : RefinesModel run)
    (expectedSigner : Address) (raw : RawSig) (digest : Digest)
    (hbound : RawSigLenFitsEvmWord raw) :
    (run raw digest == some expectedSigner) = forsAccept expectedSigner raw digest := by
  unfold forsAccept
  rw [href raw digest hbound]

/-!
## The open deliverable: build `evmRun` and prove `RefinesModel evmRun`

`evmRun` is obtained from EVMYulLean:

    evmRun raw digest :=
      decodeReturnAddress
        (EvmYul.Yul.execTopLevel fuel forsVerifierRuntime
           (calldataOf (abiEncode «recover(bytes,bytes32)» raw digest)))

(`EvmYul/Yul/Interpreter.lean:652`). `forsVerifierRuntime` is `ForsVerifier.sol`'s
deployed object — either lifted from solc Yul or modeled directly from the
inline-assembly block.

`RefinesModel evmRun` decomposes into exactly the obligation classes in
`OBLIGATIONS.md` (so step 2 and step 3 share these lemmas — build them once):

* **Class A — calldata** (obligations #6, #11): `abiDecode` of the EVM calldata
  yields `RawSig.read16 off = mem-word(payload+off) & FORS_TOP_N_MASK`, and bad
  lengths return `address(0)`. ⇒ matches `decodeRaw` + length rejection.

* **Class M — per-keccak transcript** (#1–#5, #7, #8): for each `keccak256(off,len)`
  in the asm, the preceding `mstore` sequence makes `mem[off..off+len)` equal the
  abstract `List TranscriptField` (`hMsgTranscript`, `leafTranscript`,
  `nodeTranscript`, `rootsTranscript`, `addressTranscript`). Combined with the one
  auditable bridging axiom `evmKeccak (encode fields) = keccak{Word,Hash16,Address} fields`,
  each EVM hash equals the model hash.

* **Class C — choreography** (#9, #10): pkSeed at `0x00`/`0x380` is preserved, the 25
  roots land at `0x40 + 32·t`, scratch (`0x380+`) never overlaps the roots buffer
  (`0x40..0x360`). The contract's compile-time `_GUARD` constants
  (`A == 5`, `0x380 % 64 == 0`, `0x380 ≥ ROOTS_HASH_LEN`) are these side-conditions.

Specific asm spots the Class-M/C proofs must pin (highest bug-density):
* forced-zero field at bit offset `(K-1)·A = 125` of `dVal`;
* per-level ADRS layer constants `1<<32 … 5<<32` and `globalY := (4-i)<<t | pathIdx`;
* branchless sibling swap `s := 32·(pathIdx & 1)`, `mstore(xor(0x3c0,s), node)`;
* leaf index `(t<<A) | mdT = 32·t | mdT` (needs `mdT < 2^A`, given by `indexAt_bound`).

Once `RefinesModel evmRun` is proved, `refinement_discharges_oracle evmRun` closes
the whole chain: deployed bytecode → model → SoLean oracle.
-/

end NiceTry.Fors.Bridge
