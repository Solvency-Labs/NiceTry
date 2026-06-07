import NiceTry.Fors.Bridge.ClassA

/-!
# Class-A constant getter stepping

Concrete interpreter facts for the `constant_FORS_SIG_LEN()` helper as called from
`fun_recover`. This file starts with the straight-line assignment prefix before
the helper's arithmetic overflow guards.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 800000

/-- Entry state of `constant_FORS_SIG_LEN()` when called from the good
    `fun_recover` path immediately after `var := 0`. -/
def constSigLenEntryState (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  👌 (recoverAfterVarInit raw digest).initcall [] []

def constAfterRet1Zero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constSigLenEntryState raw digest).insert "ret_1" (UInt256.ofNat 0)

def constAfterRet2Zero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterRet1Zero raw digest).insert "ret_2" (UInt256.ofNat 0)

def constAfterRet2NinetySix (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterRet2Zero raw digest).insert "ret_2" (UInt256.ofNat 96)

def constAfterProductZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterRet2NinetySix raw digest).insert "product" (UInt256.ofNat 0)

def constAfterProduct2400 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterProductZero raw digest).insert "product" (UInt256.ofNat 2400)

def constAfterScratchZero1 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterProduct2400 raw digest).insert "_1" (UInt256.ofNat 0)

def constAfterScratchZero2 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterScratchZero1 raw digest).insert "_1" (UInt256.ofNat 0)

def constAfterRet1Product (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterScratchZero2 raw digest).insert "ret_1" (UInt256.ofNat 2400)

theorem constAfterScratchZero2_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (constAfterScratchZero2 raw digest) =
      UInt256.ofNat 2400 := by
  rfl

/-- Execute the straight-line prefix of `constant_FORS_SIG_LEN()` through
    `ret_1 := product`, leaving the helper at `forsConstSigLen.body.drop 8`. -/
theorem exec_const_sig_len_prefix_to_ret1_product
    (raw : RawSig) (digest : Digest) :
    exec 40 (.Block forsConstSigLen.body) (some forsVerifierRuntime)
        (constSigLenEntryState raw digest) =
      exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
        (constAfterRet1Product raw digest) := by
  change exec 40
      (.Block (.Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 1))
      (some forsVerifierRuntime) (constSigLenEntryState raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 39) (co := some forsVerifierRuntime)
    (s := constSigLenEntryState raw digest)
    (st := .Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 1)
    (s₁ := constAfterRet1Zero raw digest)
    (h := by
      simpa [constAfterRet1Zero] using
        (exec_let_lit (n := 38) (co := some forsVerifierRuntime)
          (s := constSigLenEntryState raw digest)
          (vars := ["ret_1"]) (lit := UInt256.ofNat 0)))]
  change exec 39
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 2))
      (some forsVerifierRuntime) (constAfterRet1Zero raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 38) (co := some forsVerifierRuntime)
    (s := constAfterRet1Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 2)
    (s₁ := constAfterRet2Zero raw digest)
    (h := by
      simpa [constAfterRet2Zero] using
        (exec_let_lit (n := 37) (co := some forsVerifierRuntime)
          (s := constAfterRet1Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 0)))]
  change exec 38
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))) ::
        forsConstSigLen.body.drop 3))
      (some forsVerifierRuntime) (constAfterRet2Zero raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 37) (co := some forsVerifierRuntime)
    (s := constAfterRet2Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))))
    (sts := forsConstSigLen.body.drop 3)
    (s₁ := constAfterRet2NinetySix raw digest)
    (h := by
      simpa [constAfterRet2NinetySix] using
        (exec_let_lit (n := 36) (co := some forsVerifierRuntime)
          (s := constAfterRet2Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 96)))]
  change exec 37
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 4))
      (some forsVerifierRuntime) (constAfterRet2NinetySix raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 36) (co := some forsVerifierRuntime)
    (s := constAfterRet2NinetySix raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 4)
    (s₁ := constAfterProductZero raw digest)
    (h := by
      simpa [constAfterProductZero] using
        (exec_let_lit (n := 35) (co := some forsVerifierRuntime)
          (s := constAfterRet2NinetySix raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 0)))]
  change exec 36
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 2400))) ::
        forsConstSigLen.body.drop 5))
      (some forsVerifierRuntime) (constAfterProductZero raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 35) (co := some forsVerifierRuntime)
    (s := constAfterProductZero raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 2400))))
    (sts := forsConstSigLen.body.drop 5)
    (s₁ := constAfterProduct2400 raw digest)
    (h := by
      simpa [constAfterProduct2400] using
        (exec_let_lit (n := 34) (co := some forsVerifierRuntime)
          (s := constAfterProductZero raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 2400)))]
  change exec 35
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 6))
      (some forsVerifierRuntime) (constAfterProduct2400 raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 34) (co := some forsVerifierRuntime)
    (s := constAfterProduct2400 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 6)
    (s₁ := constAfterScratchZero1 raw digest)
    (h := by
      simpa [constAfterScratchZero1] using
        (exec_let_lit (n := 33) (co := some forsVerifierRuntime)
          (s := constAfterProduct2400 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec 34
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 7))
      (some forsVerifierRuntime) (constAfterScratchZero1 raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 33) (co := some forsVerifierRuntime)
    (s := constAfterScratchZero1 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 7)
    (s₁ := constAfterScratchZero2 raw digest)
    (h := by
      simpa [constAfterScratchZero2] using
        (exec_let_lit (n := 32) (co := some forsVerifierRuntime)
          (s := constAfterScratchZero1 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec 33
      (.Block (.Let ["ret_1"] (.some (.Var "product")) ::
        forsConstSigLen.body.drop 8))
      (some forsVerifierRuntime) (constAfterScratchZero2 raw digest) =
    exec 32 (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 32) (co := some forsVerifierRuntime)
    (s := constAfterScratchZero2 raw digest)
    (st := .Let ["ret_1"] (.some (.Var "product")))
    (sts := forsConstSigLen.body.drop 8)
    (s₁ := constAfterRet1Product raw digest)
    (h := by
      simpa [constAfterRet1Product, constAfterScratchZero2_lookup_product raw digest] using
        (exec_let_var (n := 31) (co := some forsVerifierRuntime)
          (s := constAfterScratchZero2 raw digest)
          (vars := ["ret_1"]) (id := "product")))]

end NiceTry.Fors.Bridge
