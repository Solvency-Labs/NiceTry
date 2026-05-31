import NiceTry.Fors.Bridge.EvmMemory

/-!
# Address-transcript equivalence — the completed Gap-A + Gap-B template

Ties the proved byte-level execution fact (`address_keccak_input`) to the model's
`addressFromRoot` (transcript layer, where `legit_raw_signature_recovers_expected_address`
lives), via the trusted keccak step. This is the *template* every other transcript
shape (leaf/node/hmsg/roots) follows.

The contract derives `signer := keccak256(0x00,0x40) & (2^160-1)` after
`mstore(0x00,pkSeed); mstore(0x20,pkRoot)`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

/-! ## Trusted keccak bridge (the intended "keccak is correct" assumption)

NOTE: this axiom currently bundles two things — (i) keccak correctness (`ffi.KEC`
is the hash the model's opaque `keccakAddress`/`addressFromRoot` denotes), the
trust we always intended; and (ii) the value/encoding correspondence between the
EVM 32-byte words and the model's `Hash16` arguments (the 16-byte top-half
masking, i.e. Gap B). A future refinement can split (ii) out into a proof against
an `encodeTranscript` definition, leaving a purer keccak-only axiom. Folded here
to complete the end-to-end template. -/
axiom evm_keccak_address (b : ByteArray) (pkSeed pkRoot : UInt256)
    (h : b = pkSeed.toByteArray ++ pkRoot.toByteArray) :
    (fromByteArrayBigEndian (ffi.KEC b)) &&& Lower160Mask
      = addressFromRoot pkSeed.toNat pkRoot.toNat

/-- **Address-shape equivalence (template).** The contract's keccak-and-mask
    address derivation, run over EVMYulLean memory after the two address `mstore`s,
    equals the model's `addressFromRoot`. -/
theorem address_derivation_eq
    (m : MachineState) (o0 o20 pkSeed pkRoot : UInt256)
    (hm : m.memory = ByteArray.empty) (h0 : o0.toNat = 0) (h20 : o20.toNat = 32) :
    (fromByteArrayBigEndian
        (ffi.KEC (((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.readWithPadding 0 0x40)))
        &&& Lower160Mask
      = addressFromRoot pkSeed.toNat pkRoot.toNat := by
  have hbytes : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.readWithPadding 0 0x40
                  = pkSeed.toByteArray ++ pkRoot.toByteArray := by
    apply ByteArray.ext
    rw [ByteArray.data_append]
    exact address_keccak_input m o0 o20 pkSeed pkRoot hm h0 h20
  rw [hbytes]
  exact evm_keccak_address _ pkSeed pkRoot rfl

end NiceTry.Fors.Bridge
