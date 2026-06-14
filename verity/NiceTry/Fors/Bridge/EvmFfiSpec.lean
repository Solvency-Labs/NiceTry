import EvmYul.MachineStateOps
import NiceTry.Fors.FullKeccak

/-!
# Class-M trusted memory-primitive layer (EVMYulLean FFI specs)

**Finding (this is why Class-M is not "just prove the bytes"):** EVMYulLean's
byte-level memory ops route through `@[extern] opaque` FFI primitives that have no
reducible body and no lemmas anywhere in the EVMYulLean tree:

* `ffi.ByteArray.zeroes : USize → ByteArray` — memory padding, used by BOTH
  `ByteArray.write` (hence `mstore`/`writeWord`) and `UInt256.toByteArray`.
* `ffi.keccak256` / `ffi.KEC` — the hash (already our trusted keccak).

Consequently byte-level memory equalities are **not kernel-reducible**. We localize
that into this small trusted spec — the minimal TCB additions for Class-M. These
are total-correctness specs of EVM memory primitives, NOT cryptographic
assumptions, so they don't touch the soundness story.

The transcript model now has one opaque `keccakWord`; `keccakHash16` and
`keccakAddress` are proved masks of that shared word. `TranscriptEncoding.lean`
provides the canonical EVM-byte encoding, and `evm_keccak_transcript` is the
single remaining cryptographic bridge. See `CLASS-M.md`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul

/-- `ffi.ByteArray.zeroes n` produces exactly `n` bytes. -/
axiom ffi_zeroes_size (n : USize) :
    (ffi.ByteArray.zeroes n).size = n.toNat

/-- `ffi.ByteArray.zeroes n` is all-zero. -/
axiom ffi_zeroes_get! (n : USize) (i : Nat) (h : i < n.toNat) :
    (ffi.ByteArray.zeroes n).get! i = (0 : UInt8)

/-- Zero-length padding is the empty array. Keyed on `.toNat` so it collapses the
    `zeroes ⟨k⟩` terms that `ByteArray.write`/`readWithPadding` leave behind
    regardless of how the `USize` literal is constructed. -/
axiom ffi_zeroes_eq_empty (n : USize) (h : n.toNat = 0) :
    ffi.ByteArray.zeroes n = ByteArray.empty

/-! ## Provable-but-upstream-private (intended to be discharged, not permanent trust)

The fact below is *true and provable* — EVMYulLean even has the lemmas
(`toBytes'_le`, `toBytes'_UInt256_le`) — but they and `toBytes'` are `private`, so
they cannot be referenced from this module, and EVMYulLean is consumed as a fetched
dependency (can't patch in place). Tracked as trust ONLY until an upstream PR to
`lfglabs-dev/EVMYulLean` de-privatizes `toBytes'_le`, after which this becomes a
`theorem`. It is a total-correctness fact about a 256-bit word's big-endian
encoding, not a cryptographic assumption. -/
axiom uint256_toByteArray_size (v : UInt256) : (UInt256.toByteArray v).size = 32

/-- Big-endian word encoding is a left inverse for EVM word decoding.

Like `uint256_toByteArray_size`, this is provable from EVMYulLean's private
`fromBytes'_toBytes'` and `toBytes'_UInt256_le` lemmas but cannot be referenced
from this project while EVMYulLean is consumed as a dependency. It is a byte-word
codec fact, not a cryptographic assumption. -/
axiom uint256_toByteArray_roundtrip (v : UInt256) :
    EvmYul.uInt256OfByteArray v.toByteArray = v

end NiceTry.Fors.Bridge
