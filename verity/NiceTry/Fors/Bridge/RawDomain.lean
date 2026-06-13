import EvmYul.UInt256
import NiceTry.Fors.Types

/-!
# ABI-representable raw-signature domain

`recover(bytes,bytes32)` represents the dynamic bytes length as one EVM word.
The bridge therefore states runtime refinement over raw signatures whose
model-side `Nat` length fits in that word.
-/

namespace NiceTry.Fors.Bridge

open NiceTry.Fors

/-- Raw lengths that can be represented by an ABI `bytes.length` word. -/
def RawSigLenFitsEvmWord (raw : RawSig) : Prop :=
  raw.len < EvmYul.UInt256.size

/-- Every abstract 16-byte field is represented as a packed high-half EVM word,
    matching `RawSig.read16` and the calldata encoder. -/
def RawSigWellFormed (raw : RawSig) : Prop :=
  ∀ k : Nat, k ≤ 152 →
    raw.read16 (16 * k) % 2 ^ 128 = 0 ∧ raw.read16 (16 * k) < 2 ^ 256

/-- Digests representable by the ABI `bytes32` word. -/
def DigestFitsEvmWord (digest : Digest) : Prop :=
  digest < EvmYul.UInt256.size

/-- The exact model domain represented without truncation by
    `recover(bytes,bytes32)` calldata. -/
def ForsAbiInput (raw : RawSig) (digest : Digest) : Prop :=
  RawSigLenFitsEvmWord raw ∧ RawSigWellFormed raw ∧ DigestFitsEvmWord digest

end NiceTry.Fors.Bridge
