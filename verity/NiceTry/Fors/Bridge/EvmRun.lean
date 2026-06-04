import NiceTry.Fors.Bridge.ForsRuntime
import NiceTry.Fors.Spec

/-!
# `evmRun`: run `forsVerifierRuntime` on calldata via the EVMYulLean interpreter

Runs the deployed `ForsVerifier` dispatcher on given calldata (codeOverride supplies
the helper functions; `execTopLevel` can't be used since it hardcodes `.none`),
and reads the 32-byte word returned by the contract's `RETURN` (in `H_return`).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

/-- Run the contract on raw calldata; the returned 32-byte word (the recovered
    address word) if it `RETURN`s, else `none`.

    NOTE: `fun_recover` is invoked via the interpreter's `call`, which first does
    `accountMap.find? codeOwner` and errors with `MissingContract` if no account is
    installed there — *before* `codeOverride` is ever consulted. So besides passing
    `forsVerifierRuntime` as the code override (which supplies the function bodies),
    we must also install an account at `codeOwner`, or the `recover` path always
    errors out (→ `none` → `evmRun ≡ 0`). The installed account's `code` is
    superseded by the override; it only needs to exist. -/
def runForsCalldata (cd : ByteArray) (fuel : Nat) : Option UInt256 :=
  let ee : EvmYul.ExecutionEnv .Yul :=
    { (Inhabited.default : EvmYul.ExecutionEnv .Yul) with calldata := cd }
  let ss : EvmYul.SharedState .Yul :=
    { (Inhabited.default : EvmYul.SharedState .Yul) with
        executionEnv := ee,
        accountMap :=
          (Inhabited.default : EvmYul.SharedState .Yul).accountMap.insert ee.codeOwner
            { (Inhabited.default : EvmYul.Account .Yul) with code := forsVerifierRuntime } }
  match exec fuel forsDispatcher (some forsVerifierRuntime) (.Ok ss Inhabited.default) with
  | .error (.YulHalt s _) => some (.ofNat (fromByteArrayBigEndian s.sharedState.H_return))
  | _ => none

/-! ## ABI calldata encoding + the full `evmRun` -/

open NiceTry.Fors

/-- 32-byte big-endian word. -/
def word32 (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

/-- The `recover(bytes,bytes32)` selector as its 4 leading bytes. -/
def forsSelector : ByteArray := (word32 0x1aad75c5).extract 28 32

/-- The 2448-byte signature payload, reconstructed from `read16` at each 16-byte
    chunk (153 chunks × 16 = 2448). -/
def forsPayload (raw : RawSig) : ByteArray :=
  (List.range 153).foldl
    (fun acc i => acc ++ ((UInt256.ofNat (raw.read16 (16 * i))).toByteArray).extract 16 32)
    ByteArray.empty

/-- ABI calldata for `recover(bytes sig, bytes32 digest)`:
    `selector ‖ offset(0x40) ‖ digest ‖ length ‖ payload`. -/
def encodeForsCalldata (raw : RawSig) (digest : Digest) : ByteArray :=
  forsSelector ++ word32 0x40 ++ word32 digest ++ word32 raw.len ++ forsPayload raw

/-- **`evmRun`** — the deployed contract's observable behavior as a function:
    encode calldata, run it, decode the low-160 of the returned word. The contract
    signals failure with `address(0)`, so the codomain is `Address` (not `Option`). -/
def evmRun (raw : RawSig) (digest : Digest) : Address :=
  ((runForsCalldata (encodeForsCalldata raw digest) 100000).map
    (fun w => w.toNat % 2 ^ 160)).getD 0

/-- **The refinement target for the deployed contract.** Note `none ↔ address(0)`:
    the model returns `none` on bad/not-grinded sigs, the contract returns
    `address(0)`, so this is `.getD 0`, not exact equality. This is the goal the
    whole Bridge feeds; it is **the open multi-week proof** (the FORS tree-loop
    induction + ABI-parse), decomposed below. NOT proved here. -/
def ForsRefines : Prop :=
  ∀ (raw : RawSig) (digest : Digest), evmRun raw digest = (recoverRaw? raw digest).getD 0

/-!
## Decomposition (how `ForsRefines` is discharged — open goals)

Proving `ForsRefines` reduces, via `runForsCalldata` unfolding the interpreter, to:

1. **ABI parse** — `calldataload` over `encodeForsCalldata raw digest` yields the
   dispatcher's `offset/length/digest` and `fun_recover`'s per-field reads match
   `raw.read16` / `decodeRaw` (Codex's `decodeTyped_reads_raw_header`,
   `decodeOpening_reads_raw_fields`, `rawOpenings_*`).
2. **Hmsg** — the 5 `mstore`s + `keccak256(0,0xa0)` = `hMsg` (`evm_keccak_hmsg` +
   `hmsg_keccak_input_overwrite`).
3. **Forced-zero** — `and(shr(125,dVal),31)` ↔ `forcedZero` (`forcedZero_eq_evm_shape`);
   the `≠0` branch RETURNs `address(0)` = the model's `none`-via-`getD`.
4. **Tree loop** — induct over the `for { } lt(usr_t,25) { … }` running 25 times,
   each iteration producing leaf + 5 node hashes (the `*_climbLevel_*` lemmas) and
   writing the root at `0x40+32·t` (`MemoryLayout`); this is the long pole.
5. **Roots compression** — `keccak256(0,864)` = `compressRoots`
   (`roots_derivation_eq_*`), then `recoverRoot`.
6. **Address** — `keccak256(0,0x40) & low160` = `addressFromRoot`
   (`address_derivation_eq_overwrite`).

Once proved, `ForsRefines` discharges SoLean's oracle via the (proved)
sufficiency theorem in `Equivalence.lean` (adapted to the `.getD 0` form).
-/

end NiceTry.Fors.Bridge
