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

end NiceTry.Fors.Bridge
