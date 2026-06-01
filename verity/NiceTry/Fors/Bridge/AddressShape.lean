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

/-! ## Trusted keccak bridges for the next Class-M shapes

Like `evm_keccak_address`, these axioms deliberately isolate the opaque keccak
step plus the byte/value transcript correspondence. The input-byte facts they
consume (`*_keccak_input_overwrite`) are proved in `EvmMemory.lean`; the axioms
only say that hashing those bytes denotes the model transcript hash. A future
Gap-B split should replace the encoding/masking parts with proved lemmas and
leave keccak itself opaque.
-/

axiom evm_keccak_hmsg (b : ByteArray) (pkSeed r digest domain counter : UInt256)
    (hdomain : domain.toNat = ForsDomainWord)
    (h : b.data = concatData ([pkSeed, r, digest, domain, counter].map UInt256.toByteArray)) :
    fromByteArrayBigEndian (ffi.KEC b) =
      hMsg pkSeed.toNat r.toNat digest.toNat counter.toNat

axiom evm_keccak_leaf (b : ByteArray) (pkSeed adrs sk : UInt256) (tree leafIdx : Nat)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree leafIdx)
    (h : b.data = concatData ([pkSeed, adrs, sk].map UInt256.toByteArray)) :
    (fromByteArrayBigEndian (ffi.KEC b)) &&& NMaskWord =
      leafHash pkSeed.toNat (leafAdrs tree leafIdx) sk.toNat

axiom evm_keccak_node (b : ByteArray) (pkSeed adrs left right : UInt256)
    (tree height parentIdx : Nat)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height parentIdx)
    (h : b.data = concatData ([pkSeed, adrs, left, right].map UInt256.toByteArray)) :
    (fromByteArrayBigEndian (ffi.KEC b)) &&& NMaskWord =
      nodeHash pkSeed.toNat (nodeAdrs tree height parentIdx) left.toNat right.toNat

axiom evm_keccak_roots (b : ByteArray) (pkSeed rootsAdrs : UInt256)
    (roots : TreeIndex → UInt256)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (h : b.data = concatData (rootsBufferBytes pkSeed rootsAdrs roots)) :
    (fromByteArrayBigEndian (ffi.KEC b)) &&& NMaskWord =
      compressRoots pkSeed.toNat (fun i => (roots i).toNat)

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

/-- **Address-shape equivalence, real-contract version.** Same conclusion as
    `address_derivation_eq`, but matching the actual execution: `pkSeed` already
    sits at `0x00` in a larger, populated memory and the contract does a single
    `mstore(0x20, pkRoot)` (overwrite within bounds) before hashing. No
    empty-memory assumption. -/
theorem address_derivation_eq_overwrite
    (m : MachineState) (o20 pkSeed pkRoot : UInt256)
    (h20 : o20.toNat = 32) (hsize : 64 ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data) :
    (fromByteArrayBigEndian
        (ffi.KEC ((m.mstore o20 pkRoot).memory.readWithPadding 0 0x40)))
        &&& Lower160Mask
      = addressFromRoot pkSeed.toNat pkRoot.toNat := by
  have hbytes : (m.mstore o20 pkRoot).memory.readWithPadding 0 0x40
                  = pkSeed.toByteArray ++ pkRoot.toByteArray := by
    apply ByteArray.ext
    rw [ByteArray.data_append]
    exact address_keccak_input_overwrite m o20 pkSeed pkRoot h20 hsize hpk
  rw [hbytes]
  exact evm_keccak_address _ pkSeed pkRoot rfl

/-! ## Hmsg / leaf / node shape equivalences -/

/-- Hmsg-shape equivalence, real-contract overwrite version. The five proven
    `mstore`s produce exactly `pkSeed ‖ r ‖ digest ‖ domain ‖ counter`; the
    trusted bridge identifies keccak of those bytes with the model's `hMsg`. -/
theorem hmsg_derivation_eq_overwrite
    (m : MachineState) (o0 o20 o40 o60 o80 pkSeed r digest domain counter : UInt256)
    (h0 : o0.toNat = 0) (h20 : o20.toNat = 32) (h40 : o40.toNat = 64)
    (h60 : o60.toNat = 96) (h80 : o80.toNat = 128)
    (hdomain : domain.toNat = ForsDomainWord)
    (hsize : HMsgHashLen ≤ m.memory.size) :
    fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          (((((m.mstore o0 pkSeed).mstore o20 r).mstore o40 digest).mstore o60 domain).mstore o80 counter).memory
          0 HMsgHashLen))
      = hMsg pkSeed.toNat r.toNat digest.toNat counter.toNat := by
  exact evm_keccak_hmsg _ pkSeed r digest domain counter hdomain
    (hmsg_keccak_input_overwrite m o0 o20 o40 o60 o80 pkSeed r digest domain counter
      h0 h20 h40 h60 h80 hsize)

/-- Leaf-shape equivalence for the scratch transcript at `0x380`:
    `pkSeed ‖ ADRS_leaf(tree, leafIdx) ‖ sk`. -/
theorem leaf_derivation_eq_overwrite
    (m : MachineState) (oScratch oAdrs oLeft pkSeed adrs sk : UInt256) (tree leafIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree leafIdx)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          (((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sk).memory
          ScratchBase LeafHashLen))) &&& NMaskWord =
      leafHash pkSeed.toNat (leafAdrs tree leafIdx) sk.toNat := by
  exact evm_keccak_leaf _ pkSeed adrs sk tree leafIdx hadrs
    (leaf_keccak_input_overwrite m oScratch oAdrs oLeft pkSeed adrs sk
      hScratch hAdrs hLeft hsize)

/-- Leaf derivation packaged in the exact typed-model form used by the loop
    skeleton. The future execution proof supplies the value equalities for
    `pkSeed`, `sk`, and `leafIdx`; this lemma handles the keccak/memory shape. -/
theorem leaf_derivation_eq_model_leaf_overwrite
    (m : MachineState) (oScratch oAdrs oLeft pkSeed adrs sk : UInt256)
    (sig : TypedSig) (dVal : Word) (tree : TreeIndex) (leafIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset)
    (hpk : pkSeed.toNat = sig.pkSeed)
    (hsk : sk.toNat = (sig.openings tree).sk)
    (hidx : leafIdx = indexAt dVal tree.val)
    (hadrs : adrs.toNat = shapeLeafAdrsWord tree.val leafIdx)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          (((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sk).memory
          ScratchBase LeafHashLen))) &&& NMaskWord =
      leafHash sig.pkSeed (leafAdrs tree.val (indexAt dVal tree.val)) (sig.openings tree).sk := by
  rw [leaf_derivation_eq_overwrite m oScratch oAdrs oLeft pkSeed adrs sk tree.val leafIdx
    hScratch hAdrs hLeft hadrs hsize]
  rw [hpk, hsk, hidx]

/-- Node-shape equivalence for the scratch transcript at `0x380`:
    `pkSeed ‖ ADRS_node(tree, height, parentIdx) ‖ left ‖ right`. -/
theorem node_derivation_eq_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs left right : UInt256)
    (tree height parentIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height parentIdx)
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft left).mstore oRight right).memory
          ScratchBase NodeHashLen))) &&& NMaskWord =
      nodeHash pkSeed.toNat (nodeAdrs tree height parentIdx) left.toNat right.toNat := by
  exact evm_keccak_node _ pkSeed adrs left right tree height parentIdx hadrs
    (node_keccak_input_overwrite m oScratch oAdrs oLeft oRight pkSeed adrs left right
      hScratch hAdrs hLeft hRight hsize)

/-- Even-branch node derivation in the exact `climbLevel` shape: current node is
    the left child and the auth sibling is the right child. -/
theorem node_derivation_eq_climbLevel_even_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs node sibling : UInt256)
    (tree height pathIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hEven : pathIdx % 2 = 0)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft node).mstore oRight sibling).memory
          ScratchBase NodeHashLen))) &&& NMaskWord =
      climbLevel pkSeed.toNat tree height pathIdx node.toNat sibling.toNat := by
  rw [node_derivation_eq_overwrite m oScratch oAdrs oLeft oRight pkSeed adrs node sibling
    tree height (pathIdx / 2) hScratch hAdrs hLeft hRight hadrs hsize]
  simp [climbLevel, hEven]

/-- Odd-branch node derivation in the exact `climbLevel` shape: auth sibling is
    the left child and the current node is the right child. -/
theorem node_derivation_eq_climbLevel_odd_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs node sibling : UInt256)
    (tree height pathIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hOdd : pathIdx % 2 ≠ 0)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sibling).mstore oRight node).memory
          ScratchBase NodeHashLen))) &&& NMaskWord =
      climbLevel pkSeed.toNat tree height pathIdx node.toNat sibling.toNat := by
  rw [node_derivation_eq_overwrite m oScratch oAdrs oLeft oRight pkSeed adrs sibling node
    tree height (pathIdx / 2) hScratch hAdrs hLeft hRight hadrs hsize]
  simp [climbLevel, hOdd]

/-- Even-branch node derivation packaged with the model values expected by the
    loop skeleton. -/
theorem node_derivation_eq_model_climbLevel_even_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs node sibling : UInt256)
    (sigPkSeed current siblingVal : Nat) (tree height pathIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hEven : pathIdx % 2 = 0)
    (hpk : pkSeed.toNat = sigPkSeed)
    (hnode : node.toNat = current)
    (hsibling : sibling.toNat = siblingVal)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft node).mstore oRight sibling).memory
          ScratchBase NodeHashLen))) &&& NMaskWord =
      climbLevel sigPkSeed tree height pathIdx current siblingVal := by
  rw [node_derivation_eq_climbLevel_even_overwrite m oScratch oAdrs oLeft oRight pkSeed adrs node sibling
    tree height pathIdx hScratch hAdrs hLeft hRight hEven hadrs hsize]
  rw [hpk, hnode, hsibling]

/-- Odd-branch node derivation packaged with the model values expected by the
    loop skeleton. -/
theorem node_derivation_eq_model_climbLevel_odd_overwrite
    (m : MachineState) (oScratch oAdrs oLeft oRight pkSeed adrs node sibling : UInt256)
    (sigPkSeed current siblingVal : Nat) (tree height pathIdx : Nat)
    (hScratch : oScratch.toNat = ScratchBase) (hAdrs : oAdrs.toNat = ScratchAdrsOffset)
    (hLeft : oLeft.toNat = ScratchLeftOffset) (hRight : oRight.toNat = ScratchRightOffset)
    (hOdd : pathIdx % 2 ≠ 0)
    (hpk : pkSeed.toNat = sigPkSeed)
    (hnode : node.toNat = current)
    (hsibling : sibling.toNat = siblingVal)
    (hadrs : adrs.toNat = shapeNodeAdrsWord tree height (pathIdx / 2))
    (hsize : ScratchBase + NodeHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          ((((m.mstore oScratch pkSeed).mstore oAdrs adrs).mstore oLeft sibling).mstore oRight node).memory
          ScratchBase NodeHashLen))) &&& NMaskWord =
      climbLevel sigPkSeed tree height pathIdx current siblingVal := by
  rw [node_derivation_eq_climbLevel_odd_overwrite m oScratch oAdrs oLeft oRight pkSeed adrs node sibling
    tree height pathIdx hScratch hAdrs hLeft hRight hOdd hadrs hsize]
  rw [hpk, hnode, hsibling]

/-- Roots-compression-shape equivalence for the 27-word input:
    `pkSeed ‖ ADRS_roots ‖ root_0 ‖ … ‖ root_24`. This proves the roots keccak
    input shape and connects it to `compressRoots`, leaving the actual FORS
    tree-climb loop to prove the `roots` values themselves. -/
theorem roots_derivation_eq_overwrite
    (m : MachineState) (pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (hsize : RootsHashLen ≤ m.memory.size) :
    (fromByteArrayBigEndian
        (ffi.KEC (ByteArray.readWithPadding
          (mstoreWords32At 0 (rootsBufferValues pkSeed rootsAdrs roots) m).memory
          0 RootsHashLen))) &&& NMaskWord =
      compressRoots pkSeed.toNat (fun i => (roots i).toNat) := by
  exact evm_keccak_roots _ pkSeed rootsAdrs roots hadrs
    (roots_keccak_input_overwrite m pkSeed rootsAdrs roots hsize)

/-- Roots-compression equivalence for the real `compressRoots` call site. If the
    post-loop memory already contains `pkSeed` at `0x00` and the 25 roots in
    `0x40..0x35f`, then the contract's final `mstore(0x20, ADRS_roots)` and
    `keccak256(0,0x360)` refine the model's `compressRoots`. -/
theorem roots_derivation_eq_from_buffer
    (m : MachineState) (o20 pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (h20 : o20.toNat = RootsAdrsOffset)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (hsize : RootsHashLen ≤ m.memory.size)
    (hpk : m.memory.data.extract 0 32 = pkSeed.toByteArray.data)
    (hroots : m.memory.data.extract RootBufferStart RootsHashLen =
      concatData ((List.ofFn roots).map UInt256.toByteArray)) :
    (fromByteArrayBigEndian
        (ffi.KEC ((m.mstore o20 rootsAdrs).memory.readWithPadding 0 RootsHashLen)))
        &&& NMaskWord =
      compressRoots pkSeed.toNat (fun i => (roots i).toNat) := by
  exact evm_keccak_roots _ pkSeed rootsAdrs roots hadrs
    (roots_keccak_input_from_buffer m o20 pkSeed rootsAdrs roots h20 hsize hpk hroots)

/-- Roots-compression equivalence after the abstract root loop has populated the
    25 root slots. This is still not the tree-climb proof: the `roots` values are
    supplied abstractly, while this theorem closes the local memory handoff into
    the real final `mstore(0x20, ADRS_roots); keccak256(0,0x360)` call. -/
theorem roots_derivation_eq_after_loop_buffer_init
    (m : MachineState) (o20 pkSeed rootsAdrs : UInt256) (roots : TreeIndex → UInt256)
    (h20 : o20.toNat = RootsAdrsOffset)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (hsize : RootsHashLen ≤ m.memory.size) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
    (fromByteArrayBigEndian
        (ffi.KEC ((afterRoots.mstore o20 rootsAdrs).memory.readWithPadding 0 RootsHashLen)))
        &&& NMaskWord =
      compressRoots pkSeed.toNat (fun i => (roots i).toNat) := by
  dsimp
  let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
  let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
  have hpost := roots_loop_buffer_post_after_init_indexed m pkSeed roots hsize
  have hsz := roots_loop_buffer_size_after_init_indexed m pkSeed roots hsize
  exact roots_derivation_eq_from_buffer afterRoots o20 pkSeed rootsAdrs roots h20 hadrs
    (by
      rw [hsz]
      exact hsize)
    hpost.1 hpost.2

/-- Pure model-side handoff for the future tree loop: once every EVM root slot is
    known to contain the corresponding `reconstructTree` value, the roots
    compression target is exactly `recoverRoot`. -/
theorem compressRoots_eq_recoverRoot_of_model_roots
    (sig : TypedSig) (dVal : Word) (pkSeed : UInt256) (roots : TreeIndex → UInt256)
    (hpk : pkSeed.toNat = sig.pkSeed)
    (hroots : ∀ tree,
      (roots tree).toNat =
        reconstructTree sig.pkSeed tree (indexAt dVal tree.val) (sig.openings tree)) :
    compressRoots pkSeed.toNat (fun i => (roots i).toNat) = recoverRoot sig dVal := by
  unfold recoverRoot
  rw [hpk]
  congr
  funext tree
  exact hroots tree

/-- Pure loop skeleton: if the future EVM proof supplies the leaf result, five
    node results, and the final root-slot value for every tree, then it has
    established exactly the pointwise `reconstructTree` premise consumed by the
    roots/recovery handoff. -/
theorem roots_match_reconstructTree_of_hash_chains
    (sig : TypedSig) (dVal : Word)
    (roots leaf node1 node2 node3 node4 node5 : TreeIndex → UInt256)
    (hroot : ∀ t, (roots t).toNat = (node5 t).toNat)
    (hleaf : ∀ t,
      (leaf t).toNat =
        leafHash sig.pkSeed (leafAdrs t.val (indexAt dVal t.val)) (sig.openings t).sk)
    (hnode1 : ∀ t,
      (node1 t).toNat =
        climbLevel sig.pkSeed t.val 1 (indexAt dVal t.val)
          (leaf t).toNat ((sig.openings t).auth (Fin.mk 0 (by decide))))
    (hnode2 : ∀ t,
      (node2 t).toNat =
        climbLevel sig.pkSeed t.val 2 ((indexAt dVal t.val) / 2)
          (node1 t).toNat ((sig.openings t).auth (Fin.mk 1 (by decide))))
    (hnode3 : ∀ t,
      (node3 t).toNat =
        climbLevel sig.pkSeed t.val 3 (((indexAt dVal t.val) / 2) / 2)
          (node2 t).toNat ((sig.openings t).auth (Fin.mk 2 (by decide))))
    (hnode4 : ∀ t,
      (node4 t).toNat =
        climbLevel sig.pkSeed t.val 4 ((((indexAt dVal t.val) / 2) / 2) / 2)
          (node3 t).toNat ((sig.openings t).auth (Fin.mk 3 (by decide))))
    (hnode5 : ∀ t,
      (node5 t).toNat =
        climbLevel sig.pkSeed t.val 5 (((((indexAt dVal t.val) / 2) / 2) / 2) / 2)
          (node4 t).toNat ((sig.openings t).auth (Fin.mk 4 (by decide)))) :
    ∀ tree,
      (roots tree).toNat =
        reconstructTree sig.pkSeed tree (indexAt dVal tree.val) (sig.openings tree) := by
  intro tree
  rw [hroot tree, hnode5 tree, hnode4 tree, hnode3 tree, hnode2 tree, hnode1 tree, hleaf tree]
  rfl

/-- Combined roots handoff up to the typed recovery model. The remaining loop
    obligation is now just the pointwise `hroots` premise: each root slot must be
    proved equal to the model's `reconstructTree` for that tree. -/
theorem roots_derivation_eq_recoverRoot_after_loop_buffer_init
    (m : MachineState) (o20 pkSeed rootsAdrs : UInt256)
    (sig : TypedSig) (dVal : Word) (roots : TreeIndex → UInt256)
    (h20 : o20.toNat = RootsAdrsOffset)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (hsize : RootsHashLen ≤ m.memory.size)
    (hpk : pkSeed.toNat = sig.pkSeed)
    (hroots : ∀ tree,
      (roots tree).toNat =
        reconstructTree sig.pkSeed tree (indexAt dVal tree.val) (sig.openings tree)) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
    (fromByteArrayBigEndian
        (ffi.KEC ((afterRoots.mstore o20 rootsAdrs).memory.readWithPadding 0 RootsHashLen)))
        &&& NMaskWord =
      recoverRoot sig dVal := by
  exact (roots_derivation_eq_after_loop_buffer_init m o20 pkSeed rootsAdrs roots h20 hadrs hsize).trans
    (compressRoots_eq_recoverRoot_of_model_roots sig dVal pkSeed roots hpk hroots)

/-- Fully composed loop-handoff skeleton. After the future EVM loop proof supplies
    the six per-tree hash-chain facts and shows each root slot contains `node5`,
    the final roots compression already refines `recoverRoot`. -/
theorem roots_derivation_eq_recoverRoot_of_hash_chains_after_loop_buffer_init
    (m : MachineState) (o20 pkSeed rootsAdrs : UInt256)
    (sig : TypedSig) (dVal : Word)
    (roots leaf node1 node2 node3 node4 node5 : TreeIndex → UInt256)
    (h20 : o20.toNat = RootsAdrsOffset)
    (hadrs : rootsAdrs.toNat = ForsRootsAdrsWord)
    (hsize : RootsHashLen ≤ m.memory.size)
    (hpk : pkSeed.toNat = sig.pkSeed)
    (hroot : ∀ t, (roots t).toNat = (node5 t).toNat)
    (hleaf : ∀ t,
      (leaf t).toNat =
        leafHash sig.pkSeed (leafAdrs t.val (indexAt dVal t.val)) (sig.openings t).sk)
    (hnode1 : ∀ t,
      (node1 t).toNat =
        climbLevel sig.pkSeed t.val 1 (indexAt dVal t.val)
          (leaf t).toNat ((sig.openings t).auth (Fin.mk 0 (by decide))))
    (hnode2 : ∀ t,
      (node2 t).toNat =
        climbLevel sig.pkSeed t.val 2 ((indexAt dVal t.val) / 2)
          (node1 t).toNat ((sig.openings t).auth (Fin.mk 1 (by decide))))
    (hnode3 : ∀ t,
      (node3 t).toNat =
        climbLevel sig.pkSeed t.val 3 (((indexAt dVal t.val) / 2) / 2)
          (node2 t).toNat ((sig.openings t).auth (Fin.mk 2 (by decide))))
    (hnode4 : ∀ t,
      (node4 t).toNat =
        climbLevel sig.pkSeed t.val 4 ((((indexAt dVal t.val) / 2) / 2) / 2)
          (node3 t).toNat ((sig.openings t).auth (Fin.mk 3 (by decide))))
    (hnode5 : ∀ t,
      (node5 t).toNat =
        climbLevel sig.pkSeed t.val 5 (((((indexAt dVal t.val) / 2) / 2) / 2) / 2)
          (node4 t).toNat ((sig.openings t).auth (Fin.mk 4 (by decide)))) :
    let afterPk := m.mstore (UInt256.ofNat 0) pkSeed
    let afterRoots := mstoreWords32At RootBufferStart (List.ofFn roots) afterPk
    (fromByteArrayBigEndian
        (ffi.KEC ((afterRoots.mstore o20 rootsAdrs).memory.readWithPadding 0 RootsHashLen)))
        &&& NMaskWord =
      recoverRoot sig dVal := by
  exact roots_derivation_eq_recoverRoot_after_loop_buffer_init
    m o20 pkSeed rootsAdrs sig dVal roots h20 hadrs hsize hpk
    (roots_match_reconstructTree_of_hash_chains sig dVal roots leaf node1 node2 node3 node4 node5
      hroot hleaf hnode1 hnode2 hnode3 hnode4 hnode5)

end NiceTry.Fors.Bridge
