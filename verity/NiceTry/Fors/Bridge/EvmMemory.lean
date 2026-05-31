import NiceTry.Fors.Bridge.ByteArrayLemmas

/-!
# MachineState-level memory lemmas (route i, Gap A continued)

Lifts the proved `ByteArray` lemmas to actual EVMYulLean execution: relates
`MachineState.mstore` to `ByteArray.write`, then assembles what `keccak256(0,0x40)`
reads after the FORS address-derivation `mstore(0x00,pkSeed); mstore(0x20,pkRoot)`.

Offsets are passed as `UInt256` with `.toNat` hypotheses, so the lemma is free of
`OfNat UInt256` literal-reduction concerns (the contract proof supplies them).
-/

namespace NiceTry.Fors.Bridge

open EvmYul

/-- `mstore` touches memory exactly as one `ByteArray.write` of the 32-byte word
    (the `activeWords` bookkeeping is irrelevant to `.memory`). -/
theorem mstore_memory (m : MachineState) (spos sval : UInt256) :
    (m.mstore spos sval).memory
      = ByteArray.write sval.toByteArray 0 m.memory spos.toNat 32 := by
  simp only [MachineState.mstore, MachineState.writeWord, writeBytes]

/-- After `mstore(0x00,pkSeed); mstore(0x20,pkRoot)` on empty memory, the region
    `keccak256(0x00,0x40)` hashes is exactly `pkSeed ‖ pkRoot` (32+32 bytes). -/
theorem address_keccak_input
    (m : MachineState) (o0 o20 pkSeed pkRoot : UInt256)
    (hm : m.memory = ByteArray.empty) (h0 : o0.toNat = 0) (h20 : o20.toNat = 32) :
    (((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.readWithPadding 0 0x40).data
      = pkSeed.toByteArray.data ++ pkRoot.toByteArray.data := by
  have hmem : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory
      = ByteArray.write pkRoot.toByteArray 0
          (ByteArray.write pkSeed.toByteArray 0 ByteArray.empty 0 32) 32 32 := by
    rw [mstore_memory, mstore_memory, h0, h20, hm]
  have hdata : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.data
      = pkSeed.toByteArray.data ++ pkRoot.toByteArray.data := by
    rw [hmem]; exact two_word_writes pkSeed pkRoot
  have hps : pkSeed.toByteArray.data.size = 32 := uint256_toByteArray_size pkSeed
  have hpr : pkRoot.toByteArray.data.size = 32 := uint256_toByteArray_size pkRoot
  have hsize : ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.size = 0x40 := by
    show ((m.mstore o0 pkSeed).mstore o20 pkRoot).memory.data.size = 0x40
    rw [hdata, Array.size_append]; omega
  rw [readWithPadding_exact _ 0x40 hsize.symm (by rw [hsize]; decide) (by rw [hsize]; decide),
      hdata]

end NiceTry.Fors.Bridge
