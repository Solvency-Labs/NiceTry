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

Separately note the model itself has TWO unconnected opaque keccak families —
transcript-level (`keccakWord`/`keccakHash16`/`keccakAddress`, where the proved
theorems live) and memory-level (`keccakWordFromMemory`/…). The equivalence must
bridge: EVM bytes → memory-call → transcript. See `CLASS-M.md`.
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

end NiceTry.Fors.Bridge
