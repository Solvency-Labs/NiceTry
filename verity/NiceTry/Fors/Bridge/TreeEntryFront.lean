import NiceTry.Fors.Bridge.TreeEntry

/-!
# `fun_recover` hmsg front-half and complete pre-loop entry

This file runs `fun_recover.body[18:24]` through the five hmsg stores and
`keccak256(0, 0xa0)`, characterizes the resulting state, then composes it with
`exec_recover_tail_to_loopInv` to reach the proved tree loop at `LoopInv 0`.

The intermediate states are named deliberately. Keeping each machine-state
update one layer deep avoids expensive definitional reduction through the whole
seven-statement trace.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

private def hmsgMask16 : UInt256 :=
  UInt256.ofNat 0xffffffffffffffffffffffffffffffff

private def hmsgSigOffsetId : Identifier := "var_sig_offset"
private def hmsgProductId : Identifier := "product"
private def hmsgRetId : Identifier := "ret"
private def hmsgDigestId : Identifier := "var_digest"

local notation "M16" => UInt256.ofNat 0xffffffffffffffffffffffffffffffff

def recoverHmsgPkWord (raw : RawSig) (digest : Digest) : UInt256 :=
  let s := recoverAfterRet3FromRet2 raw digest
  (EvmYul.State.calldataload s.toState
    (s[hmsgSigOffsetId]!.add (UInt256.ofNat 0x10))).land hmsgMask16.lnot

def recoverHmsgAfterPk (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet3FromRet2 raw digest).insert "usr_pkSeed"
    (recoverHmsgPkWord raw digest)

def recoverHmsgAfterStore0 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterPk raw digest
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0)
    (recoverHmsgPkWord raw digest))

def recoverHmsgRWord (raw : RawSig) (digest : Digest) : UInt256 :=
  let s := recoverHmsgAfterStore0 raw digest
  treeMaskedCalldataWord s s[hmsgSigOffsetId]!

def recoverHmsgAfterStore32 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterStore0 raw digest
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0x20)
    (recoverHmsgRWord raw digest))

def recoverHmsgDigestWord (raw : RawSig) (digest : Digest) : UInt256 :=
  (recoverHmsgAfterStore32 raw digest)[hmsgDigestId]!

def recoverHmsgAfterStore64 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterStore32 raw digest
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0x40)
    (recoverHmsgDigestWord raw digest))

def recoverHmsgDomainWord : UInt256 := (UInt256.ofNat 2).lnot

def recoverHmsgAfterStore96 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterStore64 raw digest
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 96)
    recoverHmsgDomainWord)

def recoverHmsgCounterOffset (raw : RawSig) (digest : Digest) : UInt256 :=
  let s := recoverHmsgAfterStore96 raw digest
  (s[hmsgSigOffsetId]!.add s[hmsgProductId]!).add s[hmsgRetId]!

def recoverHmsgCounterWord (raw : RawSig) (digest : Digest) : UInt256 :=
  let s := recoverHmsgAfterStore96 raw digest
  treeMaskedCalldataWord s (recoverHmsgCounterOffset raw digest)

def recoverHmsgAfterStores (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterStore96 raw digest
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 128)
    (recoverHmsgCounterWord raw digest))

def recoverHmsgDVal (raw : RawSig) (digest : Digest) : UInt256 :=
  ((recoverHmsgAfterStores raw digest).toMachineState.keccak256
    (UInt256.ofNat 0) (UInt256.ofNat 0xa0)).1

def recoverAfterHmsg (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  let s := recoverHmsgAfterStores raw digest
  (s.setMachineState (s.toMachineState.keccak256
    (UInt256.ofNat 0) (UInt256.ofNat 0xa0)).2).insert "usr_dVal"
      (recoverHmsgDVal raw digest)

-- Execute the hmsg front-half, body statements 18 through 24.
set_option maxHeartbeats 4000000 in
theorem exec_recover_hmsg_named
    (raw : RawSig) (digest : Digest) (co : Option YulContract) (n : Nat) :
    exec (n + 37) (.Block (forsFunRecover.body.drop 18)) co
        (recoverAfterRet3FromRet2 raw digest)
      = exec (n + 30) (.Block (forsFunRecover.body.drop 25)) co
          (recoverAfterHmsg raw digest) := by
  rw [show forsFunRecover.body.drop 18
      = (.Let ["usr_pkSeed"] (.some (.Call (Sum.inl .AND)
          [.Call (Sum.inl .CALLDATALOAD)
            [.Call (Sum.inl .ADD) [.Var "var_sig_offset", .Lit (UInt256.ofNat 0x10)]],
           .Call (Sum.inl .NOT) [.Lit M16]])))
        :: forsFunRecover.body.drop 19 from rfl,
    exec_block_cons_ok (n := n + 36) (h := exec_let_masked_addvlit (n := n + 24)
      (co := co) (s := recoverAfterRet3FromRet2 raw digest) (x := "usr_pkSeed")
      (var := "var_sig_offset") (b := UInt256.ofNat 0x10)
      (mask := M16))]
  rw [show forsFunRecover.body.drop 19
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0), .Var "usr_pkSeed"]))
        :: forsFunRecover.body.drop 20 from rfl,
    exec_block_cons_ok (n := n + 35) (h := exec_mstore_lit (n := n + 29)
      (a := UInt256.ofNat 0) (e := .Var "usr_pkSeed") (he := by rw [eval_var]))]
  rw [show forsFunRecover.body.drop 20
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE) [.Var "ret",
          .Call (Sum.inl .AND) [.Call (Sum.inl .CALLDATALOAD) [.Var "var_sig_offset"],
            .Call (Sum.inl .NOT) [.Lit M16]]]))
        :: forsFunRecover.body.drop 21 from rfl,
    exec_block_cons_ok (n := n + 34) (h := exec_mstore_expr (n := n + 28)
      (a := UInt256.ofNat 0x20) (e₁ := .Var "ret")
      (he₁ := by rw [eval_var]; rfl)
      (he₂ := eval_tree_masked_calldata (n := n + 24)
        (he := eval_var (n := n + 25))))]
  rw [show forsFunRecover.body.drop 21
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0x40), .Var "var_digest"]))
        :: forsFunRecover.body.drop 22 from rfl,
    exec_block_cons_ok (n := n + 33) (h := exec_mstore_lit (n := n + 27)
      (a := UInt256.ofNat 0x40) (e := .Var "var_digest") (he := by rw [eval_var]))]
  rw [show forsFunRecover.body.drop 22
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE) [.Var "ret_2",
          .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 2)]]))
        :: forsFunRecover.body.drop 23 from rfl,
    exec_block_cons_ok (n := n + 32) (h := exec_mstore_expr (n := n + 26)
      (a := UInt256.ofNat 96) (e₁ := .Var "ret_2")
      (he₁ := by rw [eval_var]; rfl)
      (he₂ := eval_not_mask (n := n + 26) (UInt256.ofNat 2)))]
  rw [show forsFunRecover.body.drop 23
      = (.ExprStmtCall (.Call (Sum.inl .MSTORE) [.Lit (UInt256.ofNat 128),
          .Call (Sum.inl .AND) [.Call (Sum.inl .CALLDATALOAD)
            [.Call (Sum.inl .ADD)
              [.Call (Sum.inl .ADD) [.Var "var_sig_offset", .Var "product"],
               .Var "ret"]],
            .Call (Sum.inl .NOT) [.Lit M16]]]))
        :: forsFunRecover.body.drop 24 from rfl,
    exec_block_cons_ok (n := n + 31) (h := exec_mstore_lit (n := n + 25)
      (a := UInt256.ofNat 128)
      (he := eval_tree_masked_calldata (n := n + 21)
        (he := eval_binop2 (n := n + 17) (OP := .ADD) (f := UInt256.add)
          (hprim := primCall_add (n := n + 21) _ _)
          (he₁ := eval_tree_add_var_var (n := n + 13))
          (he₂ := eval_var (n := n + 20)))))]
  rw [show forsFunRecover.body.drop 24
      = (.Let ["usr_dVal"] (.some (.Call (Sum.inl .KECCAK256)
          [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0xa0)])))
        :: forsFunRecover.body.drop 25 from rfl,
    exec_block_cons_ok (n := n + 30) (h := exec_let_keccak_lit_lit (n := n + 22))]
  rfl

theorem recoverHmsg_entry_memory_size (raw : RawSig) (digest : Digest) :
    (recoverAfterRet3FromRet2 raw digest).toMachineState.memory.size = 96 := by
  have ho : (UInt256.ofNat 64).toNat = 64 :=
    uint256_ofNat_toNat_of_lt _ (by decide)
  rw [show (recoverAfterRet3FromRet2 raw digest).toMachineState
        = (Inhabited.default : MachineState).mstore
            (UInt256.ofNat 64) (UInt256.ofNat 0x80) from rfl,
    mstore_pad_size _ _ _ (by rw [ho]; exact Nat.zero_le _)
      (by rw [ho]; decide), ho]

theorem recoverHmsgAfterStores_toMachineState (raw : RawSig) (digest : Digest) :
    (recoverHmsgAfterStores raw digest).toMachineState =
      hmsgMem (recoverAfterRet3FromRet2 raw digest).toMachineState
        (recoverHmsgPkWord raw digest)
        (recoverHmsgRWord raw digest)
        (recoverHmsgDigestWord raw digest)
        recoverHmsgDomainWord
        (recoverHmsgCounterWord raw digest) := by
  rfl

theorem recoverAfterHmsg_toMachineState (raw : RawSig) (digest : Digest) :
    (recoverAfterHmsg raw digest).toMachineState =
      ((recoverHmsgAfterStores raw digest).toMachineState.keccak256
        (UInt256.ofNat 0) (UInt256.ofNat 0xa0)).2 := by
  rfl

theorem recoverHmsgDomainWord_toNat :
    recoverHmsgDomainWord.toNat = ForsDomainWord := by
  rfl

/-! ## Hmsg word/value identities -/

theorem recoverHmsgPkWord_toNat_of_wellFormed
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw) :
    (recoverHmsgPkWord raw digest).toNat = (decodeTyped raw).pkSeed := by
  obtain ⟨hlow, hlt⟩ := hwf 1 (by omega)
  have hoff :
      (recoverAfterRet3FromRet2 raw digest)[hmsgSigOffsetId]! = UInt256.ofNat 100 := by
    rfl
  unfold recoverHmsgPkWord
  change ((EvmYul.State.calldataload (recoverAfterRet3FromRet2 raw digest).toState
      (((recoverAfterRet3FromRet2 raw digest)[hmsgSigOffsetId]!).add (UInt256.ofNat 0x10))).land
        hmsgMask16.lnot).toNat = (decodeTyped raw).pkSeed
  rw [hoff]
  change ((EvmYul.State.calldataload (recoverAfterRet3FromRet2 raw digest).toState
      ((UInt256.ofNat 100).add (UInt256.ofNat 0x10))).land
        (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat =
    (decodeTyped raw).pkSeed
  rw [show (UInt256.ofNat 100).add (UInt256.ofNat 0x10) =
      UInt256.ofNat (100 + 16 * 1) from rfl]
  rw [show (decodeTyped raw).pkSeed = raw.read16 (16 * 1) from rfl]
  exact masked_calldataload_read16 raw digest (recoverAfterRet3FromRet2 raw digest).toState
    1 (by omega) (recoverAfterRet3FromRet2_toState_calldata raw digest) hlow hlt

theorem recoverHmsgRWord_toNat_of_wellFormed
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw) :
    (recoverHmsgRWord raw digest).toNat = (decodeTyped raw).r := by
  obtain ⟨hlow, hlt⟩ := hwf 0 (by omega)
  have hoff :
      (recoverHmsgAfterStore0 raw digest)[hmsgSigOffsetId]! = UInt256.ofNat 100 := by
    rfl
  unfold recoverHmsgRWord
  change (treeMaskedCalldataWord (recoverHmsgAfterStore0 raw digest)
      ((recoverHmsgAfterStore0 raw digest)[hmsgSigOffsetId]!)).toNat =
    (decodeTyped raw).r
  rw [hoff]
  rw [show (decodeTyped raw).r = raw.read16 (16 * 0) from rfl]
  exact treeMaskedCalldataWord_read16 raw digest (recoverHmsgAfterStore0 raw digest)
    0 (by omega) (by rfl) hlow hlt

theorem recoverHmsgDigestWord_eq (raw : RawSig) (digest : Digest) :
    recoverHmsgDigestWord raw digest = UInt256.ofNat digest := by
  rfl

theorem recoverHmsgDigestWord_toNat_of_lt
    (raw : RawSig) (digest : Digest)
    (hdigest : digest < UInt256.size) :
    (recoverHmsgDigestWord raw digest).toNat = digest := by
  rw [recoverHmsgDigestWord_eq]
  exact uint256_ofNat_toNat_of_lt _ hdigest

theorem recoverHmsgCounterWord_toNat_of_wellFormed
    (raw : RawSig) (digest : Digest)
    (hwf : RawSigWellFormed raw) :
    (recoverHmsgCounterWord raw digest).toNat = (decodeTyped raw).counter := by
  obtain ⟨hlow, hlt⟩ := hwf 152 (by omega)
  have hoff :
      (recoverHmsgAfterStore96 raw digest)[hmsgSigOffsetId]! = UInt256.ofNat 100 := by
    rfl
  have hprod :
      (recoverHmsgAfterStore96 raw digest)[hmsgProductId]! = UInt256.ofNat 2400 := by
    rfl
  have hret :
      (recoverHmsgAfterStore96 raw digest)[hmsgRetId]! = UInt256.ofNat 0x20 := by
    rfl
  unfold recoverHmsgCounterWord recoverHmsgCounterOffset
  change (treeMaskedCalldataWord (recoverHmsgAfterStore96 raw digest)
      ((((recoverHmsgAfterStore96 raw digest)[hmsgSigOffsetId]!).add
        ((recoverHmsgAfterStore96 raw digest)[hmsgProductId]!)).add
        ((recoverHmsgAfterStore96 raw digest)[hmsgRetId]!))).toNat =
    (decodeTyped raw).counter
  rw [hoff, hprod, hret]
  rw [show ((UInt256.ofNat 100).add (UInt256.ofNat 2400)).add (UInt256.ofNat 0x20) =
      UInt256.ofNat 2532 from rfl]
  rw [show (decodeTyped raw).counter = raw.read16 2432 from rfl]
  exact masked_calldataload_counter_read16 raw digest (recoverHmsgAfterStore96 raw digest).toState
    (by rfl) hlow hlt

/-- The interpreter's hmsg word is the model hMsg over the five stored words. -/
theorem recoverHmsgDVal_toNat (raw : RawSig) (digest : Digest) :
    (recoverHmsgDVal raw digest).toNat =
      hMsg (recoverHmsgPkWord raw digest).toNat
        (recoverHmsgRWord raw digest).toNat
        (recoverHmsgDigestWord raw digest).toNat
        (recoverHmsgCounterWord raw digest).toNat := by
  have hw := hmsg_window_after_5
    (recoverAfterRet3FromRet2 raw digest).toMachineState
    (recoverHmsgPkWord raw digest)
    (recoverHmsgRWord raw digest)
    (recoverHmsgDigestWord raw digest)
    recoverHmsgDomainWord
    (recoverHmsgCounterWord raw digest)
    (recoverHmsg_entry_memory_size raw digest)
  obtain ⟨h0, h1, h2, h3, h4, hsize⟩ := hw
  unfold recoverHmsgDVal
  rw [recoverHmsgAfterStores_toMachineState]
  exact hmsg_derivation_of_extracts _ _ _ _ _ _
    recoverHmsgDomainWord_toNat (by omega) h0 h1 h2 h3 h4

theorem recoverAfterHmsg_memory_size (raw : RawSig) (digest : Digest) :
    (recoverAfterHmsg raw digest).toMachineState.memory.size = 0xa0 := by
  rw [recoverAfterHmsg_toMachineState, keccak256_memory,
    recoverHmsgAfterStores_toMachineState]
  exact (hmsg_window_after_5
    (recoverAfterRet3FromRet2 raw digest).toMachineState
    (recoverHmsgPkWord raw digest)
    (recoverHmsgRWord raw digest)
    (recoverHmsgDigestWord raw digest)
    recoverHmsgDomainWord
    (recoverHmsgCounterWord raw digest)
    (recoverHmsg_entry_memory_size raw digest)).2.2.2.2.2

theorem recoverAfterHmsg_lookup_pkSeed (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "usr_pkSeed" (recoverAfterHmsg raw digest) =
      recoverHmsgPkWord raw digest := by
  rfl

theorem recoverAfterHmsg_lookup_dVal (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "usr_dVal" (recoverAfterHmsg raw digest) =
      recoverHmsgDVal raw digest := by
  rfl

theorem recoverAfterHmsg_lookup_ret (raw : RawSig) (digest : Digest) :
    (recoverAfterHmsg raw digest)[retId]! = UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterHmsg_lookup_ret2 (raw : RawSig) (digest : Digest) :
    (recoverAfterHmsg raw digest)[ret2Id]! = UInt256.ofNat 96 := by
  rfl

theorem recoverAfterHmsg_lookup_sig_offset (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "var_sig_offset" (recoverAfterHmsg raw digest) =
      UInt256.ofNat 100 := by
  rfl

theorem recoverAfterHmsg_ok (raw : RawSig) (digest : Digest) :
    ∃ (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore),
      recoverAfterHmsg raw digest = .Ok ss vs := by
  apply Exists.intro
  apply Exists.intro
  rfl

/-- Complete pre-loop trace from body statement 18 to the loop entry invariant. -/
theorem exec_recover_preloop_to_loopInv
    (raw : RawSig) (digest : Digest) (co : Option YulContract) (n : Nat)
    (hfz : (UInt256.shiftRight (recoverHmsgDVal raw digest) (UInt256.ofNat 125)).land
      (UInt256.ofNat 31) = (⟨0⟩ : UInt256)) :
    ∃ (ss : SharedState .Yul) (vs : EvmYul.Yul.VarStore),
      exec (n + 37) (.Block (forsFunRecover.body.drop 18)) co
          (recoverAfterRet3FromRet2 raw digest)
        = exec (n + 23) (.Block (forsFunRecover.body.drop 32)) co
            (loopEntryState ss vs (recoverHmsgPkWord raw digest)
              (recoverHmsgDVal raw digest))
      ∧ LoopInv
          (loopEntryState ss vs (recoverHmsgPkWord raw digest)
            (recoverHmsgDVal raw digest)).toState
          (recoverHmsgPkWord raw digest)
          (recoverHmsgDVal raw digest).toNat 132 0
          (loopEntryState ss vs (recoverHmsgPkWord raw digest)
            (recoverHmsgDVal raw digest)) := by
  obtain ⟨ss, vs, hs⟩ := recoverAfterHmsg_ok raw digest
  have hret : (EvmYul.Yul.State.Ok ss vs)[retId]! = UInt256.ofNat 0x20 := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_ret raw digest
  have hret2 : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96 := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_ret2 raw digest
  have hoff : EvmYul.Yul.State.lookup! "var_sig_offset" (.Ok ss vs) =
      UInt256.ofNat 100 := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_sig_offset raw digest
  have hdv : EvmYul.Yul.State.lookup! "usr_dVal" (.Ok ss vs) =
      recoverHmsgDVal raw digest := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_dVal raw digest
  have hpk : EvmYul.Yul.State.lookup! "usr_pkSeed" (.Ok ss vs) =
      recoverHmsgPkWord raw digest := by
    rw [← hs]
    exact recoverAfterHmsg_lookup_pkSeed raw digest
  have hmem : (EvmYul.Yul.State.Ok ss vs).toMachineState.memory.size = 0xa0 := by
    rw [← hs]
    exact recoverAfterHmsg_memory_size raw digest
  obtain ⟨htail, hinv⟩ := exec_recover_tail_to_loopInv ss vs co
    (recoverHmsgPkWord raw digest) (recoverHmsgDVal raw digest) n
    hret hret2 hoff hdv hpk hmem hfz
  refine ⟨ss, vs, ?_, hinv⟩
  rw [exec_recover_hmsg_named raw digest co n, hs]
  exact htail

end NiceTry.Fors.Bridge
