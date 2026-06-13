import NiceTry.Fors.Bridge.TreeMemory
import NiceTry.Fors.Bridge.CalldataBytes

/-!
# Verity-kernel keccak memory refinement (Class M, kernel-facing)

`TreeMemory.lean`'s extract calculus is artifact-agnostic, but the *deployed*
contract (`TreeLeaf.lean`) pre-stores `pkSeed@0x380` once and re-uses it across
iterations, so its leaf body emits only two scratch stores. The Verity kernel
(`Verity/TreeKeccakKernel.lean`) instead emits **all** transcript stores inside
its `unsafe do` block:

    mstore 0x380 pkSeed   -- leaf + node
    mstore 0x3a0 adrs      -- leaf + node
    mstore 0x3c0 sk        -- leaf  (= left for node)
    mstore 0x3e0 right     -- node only

This file discharges the kernel's two `keccak_memory_refinement` obligations
(`TreeKeccakKernel.lean` leaf / node, mirrored in `FullVerifierKernel.lean`):
over exactly that store sequence on any sufficiently sized machine state, the
`keccak256(0x380, len)` input window equals the `leafTranscript` /
`nodeTranscript` and the top-16 masking yields the model `leafHash` / `nodeHash`.

The single masked-keccak equation captures both halves of each obligation: the
input region equals the transcript (this is the `scratch_*_read_of_extracts`
hypothesis the `evm_keccak_*` bridge consumes) and the `&&& NMaskWord` is the
top-16-byte masking. The only residual is that the Verity compiler emits exactly
this `mstore` sequence — which is the `unsafe do` block verbatim.

The other per-keccak kernel obligations are discharged by existing
`AddressShape.lean` lemmas whose `mstore` chains already match the kernel
verbatim — `hmsg_derivation_eq_overwrite` (hmsg, 5-store) and
`roots_derivation_eq_from_buffer` (roots compression, pre-populated buffer +
single ADRS store). The address obligation needs a new theorem here
(`kernel_address_keccak_memory_refinement`), because the kernel emits both
address stores onto an arbitrary populated memory, which neither existing
address lemma covers.

The two Class-A calldata obligations are also discharged: `kernel_recover_abi_parse`
(this file) pins the `recover(bytes,bytes32)` ABI head/tail reads, and the
`rawWord` masked field reads are `TreeCalldata.lean`'s `masked_calldataload_read16`
/ `masked_calldataload_counter_read16`. For calldata the residual is the same kind
as for `mstore`: the compiler maps the kernel's `calldataload` to EVMYulLean's
verbatim.

NOT discharged (left `assumed`): the two choreography obligations
(`full_*_verifier_memory_refinement`). They are not closed `mstore`/`calldataload`
facts but assertions about the kernel `forEach` loop's *executed* memory behaviour
(pkSeed preserved, 25 roots written at `0x40+32·t`, scratch non-overlap, roots =
recovered values). Discharging them needs a kernel loop-execution model — the
deployed-contract analogue is the whole `TreeLoop.lean` induction over
`forsVerifierRuntime`; the kernel needs its own. Flipping them without that proof
would be a false `proved`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-- **Leaf kernel keccak memory refinement** (discharges `TreeKeccakKernel`'s
    `leafHash` obligation and `FullVerifierKernel`'s leaf obligation). After the
    kernel's three leaf scratch stores on any machine state whose memory already
    spans the leaf window, the masked `keccak256(0x380, 0x60)` equals the model
    `leafHash`. -/
theorem kernel_leaf_keccak_memory_refinement
    (m : MachineState) (a380 a3a0 a3c0 pkSeed adrs sk : UInt256) (tree leafIdx : Nat)
    (ha0 : a380.toNat = 0x380) (ha1 : a3a0.toNat = 0x3a0) (ha2 : a3c0.toNat = 0x3c0)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree leafIdx)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 sk).memory
          ScratchBase LeafHashLen)))
        &&& NMaskWord
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx) sk.toNat := by
  -- Memory is at least 0x3e0 bytes, so every store below is in-bounds.
  have hsz : (0x3e0 : Nat) ≤ m.memory.size := by
    unfold ScratchBase LeafHashLen at hsize; omega
  have hsz1 : (m.mstore a380 pkSeed).memory.size = m.memory.size :=
    mstore_memory_size m a380 pkSeed (by rw [ha0]; omega)
  have hsz2 : ((m.mstore a380 pkSeed).mstore a3a0 adrs).memory.size = m.memory.size := by
    rw [mstore_memory_size (m.mstore a380 pkSeed) a3a0 adrs (by rw [ha1, hsz1]; omega), hsz1]
  -- Per-slot extract facts, peeling the chain back to the relevant store.
  have h0 : (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 sk).memory.data.extract
        0x380 0x3a0 = pkSeed.toByteArray.data := by
    rw [mstore_extract_disjoint ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 sk 0x380 0x3a0
          (by rw [ha2, hsz2]; omega) (Or.inl (by rw [ha2]; omega))]
    rw [mstore_extract_disjoint (m.mstore a380 pkSeed) a3a0 adrs 0x380 0x3a0
          (by rw [ha1, hsz1]; omega) (Or.inl (by rw [ha1]))]
    have hs := mstore_extract_self m a380 pkSeed (by rw [ha0]; omega)
    rw [ha0, (by decide : (0x380 : Nat) + 32 = 0x3a0)] at hs
    exact hs
  have h1 : (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 sk).memory.data.extract
        0x3a0 0x3c0 = adrs.toByteArray.data := by
    rw [mstore_extract_disjoint ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 sk 0x3a0 0x3c0
          (by rw [ha2, hsz2]; omega) (Or.inl (by rw [ha2]))]
    have hs := mstore_extract_self (m.mstore a380 pkSeed) a3a0 adrs (by rw [ha1, hsz1]; omega)
    rw [ha1, (by decide : (0x3a0 : Nat) + 32 = 0x3c0)] at hs
    exact hs
  have h2 : (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 sk).memory.data.extract
        0x3c0 0x3e0 = sk.toByteArray.data := by
    have hs := mstore_extract_self ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 sk
      (by rw [ha2, hsz2]; omega)
    rw [ha2, (by decide : (0x3c0 : Nat) + 32 = 0x3e0)] at hs
    exact hs
  have hsize3 : ScratchBase + LeafHashLen
      ≤ (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 sk).memory.size := by
    rw [mstore_memory_size ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 sk
      (by rw [ha2, hsz2]; omega), hsz2]
    exact hsize
  exact leaf_derivation_of_extracts _ pkSeed adrs sk tree leafIdx hadrs hsize3 h0 h1 h2

/-- **Node kernel keccak memory refinement** (discharges `TreeKeccakKernel`'s
    `nodeHash` obligation and `FullVerifierKernel`'s node obligation). After the
    kernel's four node scratch stores on any machine state whose memory already
    spans the node window, the masked `keccak256(0x380, 0x80)` equals the model
    `nodeHash`. -/
theorem kernel_node_keccak_memory_refinement
    (m : MachineState) (a380 a3a0 a3c0 a3e0 pkSeed adrs left right : UInt256)
    (tree height parentIdx : Nat)
    (ha0 : a380.toNat = 0x380) (ha1 : a3a0.toNat = 0x3a0)
    (ha2 : a3c0.toNat = 0x3c0) (ha3 : a3e0.toNat = 0x3e0)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height parentIdx)
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right).memory
          ScratchBase NodeHashLen)))
        &&& NMaskWord
      = nodeHash pkSeed.toNat (nodeAdrs tree height parentIdx) left.toNat right.toNat := by
  -- Memory is at least 0x400 bytes, so every store below is in-bounds.
  have hsz : (0x400 : Nat) ≤ m.memory.size := by
    unfold ScratchBase NodeHashLen at hsize; omega
  have hsz1 : (m.mstore a380 pkSeed).memory.size = m.memory.size :=
    mstore_memory_size m a380 pkSeed (by rw [ha0]; omega)
  have hsz2 : ((m.mstore a380 pkSeed).mstore a3a0 adrs).memory.size = m.memory.size := by
    rw [mstore_memory_size (m.mstore a380 pkSeed) a3a0 adrs (by rw [ha1, hsz1]; omega), hsz1]
  have hsz3 : (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).memory.size
      = m.memory.size := by
    rw [mstore_memory_size ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 left
      (by rw [ha2, hsz2]; omega), hsz2]
  -- Per-slot extract facts, peeling the four-store chain back to each store.
  have h0 : (((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right)).memory.data.extract
        0x380 0x3a0 = pkSeed.toByteArray.data := by
    rw [mstore_extract_disjoint (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left) a3e0 right
          0x380 0x3a0 (by rw [ha3, hsz3]; omega) (Or.inl (by rw [ha3]; omega))]
    rw [mstore_extract_disjoint ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 left 0x380 0x3a0
          (by rw [ha2, hsz2]; omega) (Or.inl (by rw [ha2]; omega))]
    rw [mstore_extract_disjoint (m.mstore a380 pkSeed) a3a0 adrs 0x380 0x3a0
          (by rw [ha1, hsz1]; omega) (Or.inl (by rw [ha1]))]
    have hs := mstore_extract_self m a380 pkSeed (by rw [ha0]; omega)
    rw [ha0, (by decide : (0x380 : Nat) + 32 = 0x3a0)] at hs
    exact hs
  have h1 : (((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right)).memory.data.extract
        0x3a0 0x3c0 = adrs.toByteArray.data := by
    rw [mstore_extract_disjoint (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left) a3e0 right
          0x3a0 0x3c0 (by rw [ha3, hsz3]; omega) (Or.inl (by rw [ha3]; omega))]
    rw [mstore_extract_disjoint ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 left 0x3a0 0x3c0
          (by rw [ha2, hsz2]; omega) (Or.inl (by rw [ha2]))]
    have hs := mstore_extract_self (m.mstore a380 pkSeed) a3a0 adrs (by rw [ha1, hsz1]; omega)
    rw [ha1, (by decide : (0x3a0 : Nat) + 32 = 0x3c0)] at hs
    exact hs
  have h2 : (((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right)).memory.data.extract
        0x3c0 0x3e0 = left.toByteArray.data := by
    rw [mstore_extract_disjoint (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left) a3e0 right
          0x3c0 0x3e0 (by rw [ha3, hsz3]; omega) (Or.inl (by rw [ha3]))]
    have hs := mstore_extract_self ((m.mstore a380 pkSeed).mstore a3a0 adrs) a3c0 left
      (by rw [ha2, hsz2]; omega)
    rw [ha2, (by decide : (0x3c0 : Nat) + 32 = 0x3e0)] at hs
    exact hs
  have h3 : (((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right)).memory.data.extract
        0x3e0 0x400 = right.toByteArray.data := by
    have hs := mstore_extract_self (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left) a3e0 right
      (by rw [ha3, hsz3]; omega)
    rw [ha3, (by decide : (0x3e0 : Nat) + 32 = 0x400)] at hs
    exact hs
  have hsize4 : ScratchBase + NodeHashLen
      ≤ ((((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left).mstore a3e0 right).memory.size := by
    rw [mstore_memory_size (((m.mstore a380 pkSeed).mstore a3a0 adrs).mstore a3c0 left) a3e0 right
      (by rw [ha3, hsz3]; omega), hsz3]
    exact hsize
  exact node_derivation_of_extracts _ pkSeed adrs left right tree height parentIdx
    hadrs hsize4 h0 h1 h2 h3

/-- **Address kernel keccak memory refinement** (discharges `FullVerifierKernel`'s
    `addressFromRoot` obligation, #8). The kernel emits *both* address stores
    (`mstore 0x00 pkSeed; mstore 0x20 pkRoot`) on an arbitrary, already-populated
    memory — unlike `address_derivation_eq` (empty memory) and
    `address_derivation_eq_overwrite` (pkSeed pre-placed). We bridge by extracting
    `pkSeed@0x00` from the first store, then reusing the overwrite lemma. -/
theorem kernel_address_keccak_memory_refinement
    (m : MachineState) (a00 a20 pkSeed pkRoot : UInt256)
    (ha0 : a00.toNat = 0) (ha20 : a20.toNat = 32)
    (hsize : AddressHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (((m.mstore a00 pkSeed).mstore a20 pkRoot).memory.readWithPadding 0 0x40)))
        &&& Lower160Mask
      = addressFromRoot pkSeed.toNat pkRoot.toNat := by
  have hsz : (64 : Nat) ≤ m.memory.size := by unfold AddressHashLen at hsize; omega
  have hsize' : (64 : Nat) ≤ (m.mstore a00 pkSeed).memory.size := by
    rw [mstore_memory_size m a00 pkSeed (by rw [ha0]; omega)]; exact hsz
  have hpk : (m.mstore a00 pkSeed).memory.data.extract 0 32 = pkSeed.toByteArray.data := by
    have hs := mstore_extract_self m a00 pkSeed (by rw [ha0]; omega)
    rw [ha0] at hs
    simpa only [Nat.zero_add] using hs
  exact address_derivation_eq_overwrite (m.mstore a00 pkSeed) a20 pkSeed pkRoot ha20 hsize' hpk

/-- **ABI-parse refinement** (discharges `FullVerifierKernel`'s `recover`
    obligation, #11). On calldata that is the `recover(bytes,bytes32)` ABI
    encoding (`encodeForsCalldata raw digest`), the kernel's hardcoded reads land
    exactly on the ABI head/tail fields: `cd[4]` is the bytes offset (`0x40`),
    `cd[4+offset]` is `sig.length` (`raw.len`), and `cd[4+offset+32]` is the first
    `sig.data` word. (`4+0x40 = 0x44`, `4+0x40+32 = 100`.) The `calldataload`s
    are the documented EVMYulLean trust boundary the compiler maps the kernel's
    `calldataload` to verbatim. -/
theorem kernel_recover_abi_parse (raw : RawSig) (digest : Digest)
    (s : EvmYul.State .Yul)
    (hcd : s.executionEnv.calldata = encodeForsCalldata raw digest) :
    EvmYul.State.calldataload s (UInt256.ofNat 4) = UInt256.ofNat 0x40
    ∧ EvmYul.State.calldataload s (UInt256.ofNat (4 + 0x40)) = UInt256.ofNat raw.len
    ∧ EvmYul.State.calldataload s (UInt256.ofNat (4 + 0x40 + 32)) =
        EvmYul.uInt256OfByteArray (forsPayloadChunk raw 0 ++ forsPayloadChunk raw 1) := by
  refine ⟨calldataload_encode_offset raw digest s hcd, ?_, ?_⟩
  · rw [show (4 + 0x40 : Nat) = 0x44 from by norm_num]
    exact calldataload_encode_length raw digest s hcd
  · rw [show (4 + 0x40 + 32 : Nat) = 100 from by norm_num]
    exact calldataload_encode_payload_pair_0 raw digest s hcd

end NiceTry.Fors.Bridge
