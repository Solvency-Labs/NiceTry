import NiceTry.Fors.Bridge.ClassAConst

/-!
# Class-A `fun_recover` stepping

Concrete interpreter facts for the good-length `fun_recover` path after
`constant_FORS_SIG_LEN()` has returned `expr = SigLen`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 800000

def recoverAfterRetZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterExprConst raw digest).insert "ret" (UInt256.ofNat 0)

def recoverAfterRetWord (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRetZero raw digest).insert "ret" (UInt256.ofNat 0x20)

def recoverAfterRet1Zero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRetWord raw digest).insert "ret_1" (UInt256.ofNat 0)

def recoverAfterRet2Zero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet1Zero raw digest).insert "ret_2" (UInt256.ofNat 0)

def recoverAfterRet2NinetySix (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet2Zero raw digest).insert "ret_2" (UInt256.ofNat 96)

def recoverAfterProductZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet2NinetySix raw digest).insert "product" (UInt256.ofNat 0)

def recoverAfterProduct2400 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterProductZero raw digest).insert "product" (UInt256.ofNat 2400)

def recoverAfterScratchZero1 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterProduct2400 raw digest).insert "_1" (UInt256.ofNat 0)

def recoverAfterScratchZero2 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterScratchZero1 raw digest).insert "_1" (UInt256.ofNat 0)

def recoverAfterRet1Product (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterScratchZero2 raw digest).insert "ret_1" (UInt256.ofNat 2400)

theorem recoverAfterRetWord_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterRetWord raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterScratchZero2_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (recoverAfterScratchZero2 raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem recoverAfterRet1Product_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (recoverAfterRet1Product raw digest) =
      UInt256.ofNat 2400 := by
  rfl

/-- Continue `fun_recover` after `expr := constant_FORS_SIG_LEN()` through
    `ret := 0; ret := 0x20`, leaving execution at `forsFunRecover.body.drop 4`. -/
theorem exec_recover_ret_init_after_expr
    (raw : RawSig) (digest : Digest) :
    exec 45 (.Block (forsFunRecover.body.drop 2)) (some forsVerifierRuntime)
        (recoverAfterExprConst raw digest) =
      exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
        (recoverAfterRetWord raw digest) := by
  change exec 45
      (.Block (.Let ["ret"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 3))
      (some forsVerifierRuntime) (recoverAfterExprConst raw digest) =
    exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
      (recoverAfterRetWord raw digest)
  rw [exec_block_cons_ok
    (n := 44) (co := some forsVerifierRuntime)
    (s := recoverAfterExprConst raw digest)
    (st := .Let ["ret"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 3)
    (s₁ := recoverAfterRetZero raw digest)
    (h := by
      simpa [recoverAfterRetZero] using
        (exec_let_lit (n := 43) (co := some forsVerifierRuntime)
          (s := recoverAfterExprConst raw digest)
          (vars := ["ret"]) (lit := UInt256.ofNat 0)))]
  change exec 44
      (.Block (.Let ["ret"] (.some (.Lit (UInt256.ofNat 0x20))) ::
        forsFunRecover.body.drop 4))
      (some forsVerifierRuntime) (recoverAfterRetZero raw digest) =
    exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
      (recoverAfterRetWord raw digest)
  rw [exec_block_cons_ok
    (n := 43) (co := some forsVerifierRuntime)
    (s := recoverAfterRetZero raw digest)
    (st := .Let ["ret"] (.some (.Lit (UInt256.ofNat 0x20))))
    (sts := forsFunRecover.body.drop 4)
    (s₁ := recoverAfterRetWord raw digest)
    (h := by
      simpa [recoverAfterRetWord] using
        (exec_let_lit (n := 42) (co := some forsVerifierRuntime)
          (s := recoverAfterRetZero raw digest)
          (vars := ["ret"]) (lit := UInt256.ofNat 0x20)))]

/-- Continue `fun_recover` after `ret := 0x20` through `ret_1 := product`,
    leaving execution at `forsFunRecover.body.drop 12`. -/
theorem exec_recover_prefix_to_ret1_product
    (raw : RawSig) (digest : Digest) :
    exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
        (recoverAfterRetWord raw digest) =
      exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
        (recoverAfterRet1Product raw digest) := by
  change exec 43
      (.Block (.Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 5))
      (some forsVerifierRuntime) (recoverAfterRetWord raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 42) (co := some forsVerifierRuntime)
    (s := recoverAfterRetWord raw digest)
    (st := .Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 5)
    (s₁ := recoverAfterRet1Zero raw digest)
    (h := by
      simpa [recoverAfterRet1Zero] using
        (exec_let_lit (n := 41) (co := some forsVerifierRuntime)
          (s := recoverAfterRetWord raw digest)
          (vars := ["ret_1"]) (lit := UInt256.ofNat 0)))]
  change exec 42
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 6))
      (some forsVerifierRuntime) (recoverAfterRet1Zero raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 41) (co := some forsVerifierRuntime)
    (s := recoverAfterRet1Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 6)
    (s₁ := recoverAfterRet2Zero raw digest)
    (h := by
      simpa [recoverAfterRet2Zero] using
        (exec_let_lit (n := 40) (co := some forsVerifierRuntime)
          (s := recoverAfterRet1Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 0)))]
  change exec 41
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))) ::
        forsFunRecover.body.drop 7))
      (some forsVerifierRuntime) (recoverAfterRet2Zero raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 40) (co := some forsVerifierRuntime)
    (s := recoverAfterRet2Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))))
    (sts := forsFunRecover.body.drop 7)
    (s₁ := recoverAfterRet2NinetySix raw digest)
    (h := by
      simpa [recoverAfterRet2NinetySix] using
        (exec_let_lit (n := 39) (co := some forsVerifierRuntime)
          (s := recoverAfterRet2Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 96)))]
  change exec 40
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 8))
      (some forsVerifierRuntime) (recoverAfterRet2NinetySix raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 39) (co := some forsVerifierRuntime)
    (s := recoverAfterRet2NinetySix raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 8)
    (s₁ := recoverAfterProductZero raw digest)
    (h := by
      simpa [recoverAfterProductZero] using
        (exec_let_lit (n := 38) (co := some forsVerifierRuntime)
          (s := recoverAfterRet2NinetySix raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 0)))]
  change exec 39
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 2400))) ::
        forsFunRecover.body.drop 9))
      (some forsVerifierRuntime) (recoverAfterProductZero raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 38) (co := some forsVerifierRuntime)
    (s := recoverAfterProductZero raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 2400))))
    (sts := forsFunRecover.body.drop 9)
    (s₁ := recoverAfterProduct2400 raw digest)
    (h := by
      simpa [recoverAfterProduct2400] using
        (exec_let_lit (n := 37) (co := some forsVerifierRuntime)
          (s := recoverAfterProductZero raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 2400)))]
  change exec 38
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 10))
      (some forsVerifierRuntime) (recoverAfterProduct2400 raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 37) (co := some forsVerifierRuntime)
    (s := recoverAfterProduct2400 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 10)
    (s₁ := recoverAfterScratchZero1 raw digest)
    (h := by
      simpa [recoverAfterScratchZero1] using
        (exec_let_lit (n := 36) (co := some forsVerifierRuntime)
          (s := recoverAfterProduct2400 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec 37
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 11))
      (some forsVerifierRuntime) (recoverAfterScratchZero1 raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 36) (co := some forsVerifierRuntime)
    (s := recoverAfterScratchZero1 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 11)
    (s₁ := recoverAfterScratchZero2 raw digest)
    (h := by
      simpa [recoverAfterScratchZero2] using
        (exec_let_lit (n := 35) (co := some forsVerifierRuntime)
          (s := recoverAfterScratchZero1 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec 36
      (.Block (.Let ["ret_1"] (.some (.Var "product")) ::
        forsFunRecover.body.drop 12))
      (some forsVerifierRuntime) (recoverAfterScratchZero2 raw digest) =
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
      (recoverAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := 35) (co := some forsVerifierRuntime)
    (s := recoverAfterScratchZero2 raw digest)
    (st := .Let ["ret_1"] (.some (.Var "product")))
    (sts := forsFunRecover.body.drop 12)
    (s₁ := recoverAfterRet1Product raw digest)
    (h := by
      simpa [recoverAfterRet1Product, recoverAfterScratchZero2_lookup_product raw digest] using
        (exec_let_var (n := 34) (co := some forsVerifierRuntime)
          (s := recoverAfterScratchZero2 raw digest)
          (vars := ["ret_1"]) (id := "product")))]

end NiceTry.Fors.Bridge
