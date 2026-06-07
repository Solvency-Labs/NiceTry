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

/-- `add(ret, product)` in `fun_recover`'s setup. -/
def recoverSetupSumExpr : Expr :=
  .Call (Sum.inl .ADD) [.Var "ret", .Var "product"]

/-- `gt(ret, sum)`, the setup overflow guard before the signature length check. -/
def recoverSetupOverflowGuardExpr : Expr :=
  .Call (Sum.inl .GT) [.Var "ret", .Var "sum"]

/-- `iszero(eq(var_sig_length, expr))`, the internal good-length check in
    `fun_recover`. -/
def recoverLengthRejectGuardExpr : Expr :=
  .Call (Sum.inl .ISZERO)
    [.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"]]

/-- `add(var_sig_offset, 0x10)`, the calldata word used to recover `usr_pkSeed`. -/
def recoverPkSeedCalldataOffsetExpr : Expr :=
  .Call (Sum.inl .ADD) [.Var "var_sig_offset", .Lit (UInt256.ofNat 0x10)]

/-- `calldataload(add(var_sig_offset, 0x10))`, before the high-16-byte mask. -/
def recoverPkSeedCalldataReadExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [recoverPkSeedCalldataOffsetExpr]

/-- `calldataload(var_sig_offset)`, the R header word before the high-16-byte mask. -/
def recoverRCalldataReadExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [.Var "var_sig_offset"]

/-- The literal mask whose complement keeps the high 16 bytes of a calldata word. -/
def recoverLow16Mask : UInt256 :=
  UInt256.ofNat 0xffffffffffffffffffffffffffffffff

/-- `not(0xffff...ffff)`, the high-16-byte mask reused by header reads. -/
def recoverHigh16MaskExpr : Expr :=
  .Call (Sum.inl .NOT) [.Lit recoverLow16Mask]

/-- `add(var_sig_offset, product)`, the base of the trailer/counter read. -/
def recoverCounterCalldataBaseExpr : Expr :=
  .Call (Sum.inl .ADD) [.Var "var_sig_offset", .Var "product"]

/-- `add(add(var_sig_offset, product), ret)`, the calldata word used for the counter. -/
def recoverCounterCalldataOffsetExpr : Expr :=
  .Call (Sum.inl .ADD) [recoverCounterCalldataBaseExpr, .Var "ret"]

/-- `calldataload(add(add(var_sig_offset, product), ret))`, before the high-16-byte mask. -/
def recoverCounterCalldataReadExpr : Expr :=
  .Call (Sum.inl .CALLDATALOAD) [recoverCounterCalldataOffsetExpr]

/-- `not(2)`, the FORS hmsg domain word written before `keccak256(0, 0xa0)`. -/
def recoverHmsgDomainExpr : Expr :=
  .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 2)]

def recoverLengthRejectBody : List Stmt :=
  [.Let ["var"] (.some (.Lit (UInt256.ofNat 0))), .Leave]

def recoverAfterSumZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet1Product raw digest).insert "sum" (UInt256.ofNat 0)

def recoverAfterSumAdd (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterSumZero raw digest).insert "sum" (UInt256.ofNat 2432)

def recoverAfterRet3Zero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterSumAdd raw digest).insert "ret_3" (UInt256.ofNat 0)

def recoverAfterRet3FromRet2 (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRet3Zero raw digest).insert "ret_3" (UInt256.ofNat 96)

private theorem uint256_add_ret_product :
    (UInt256.ofNat 0x20).add (UInt256.ofNat 2400) = UInt256.ofNat 2432 := by
  rfl

private theorem uint256_add_sig_offset_pkSeed :
    (UInt256.ofNat 100).add (UInt256.ofNat 0x10) = UInt256.ofNat 116 := by
  rfl

private theorem uint256_add_sig_offset_product :
    (UInt256.ofNat 100).add (UInt256.ofNat 2400) = UInt256.ofNat 2500 := by
  rfl

private theorem uint256_add_counter_base_ret :
    (UInt256.ofNat 2500).add (UInt256.ofNat 0x20) = UInt256.ofNat 2532 := by
  rfl

private theorem uint256_not_low16_mask :
    recoverLow16Mask.lnot =
      UInt256.ofNat 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000 := by
  rfl

private theorem uint256_not_two_domain :
    (UInt256.ofNat 2).lnot =
      UInt256.ofNat 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd := by
  rfl

private theorem uint256_gt_ret_sum :
    UInt256.gt (UInt256.ofNat 0x20) (UInt256.ofNat 2432) = UInt256.ofNat 0 := by
  rfl

private theorem uint256_eq_sigLen_sigLen :
    UInt256.eq (UInt256.ofNat SigLen) (UInt256.ofNat SigLen) = UInt256.ofNat 1 := by
  rfl

private theorem uint256_isZero_one :
    (UInt256.ofNat 1).isZero = UInt256.ofNat 0 := by
  rfl

theorem recoverAfterRetWord_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterRetWord raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterRet1Product_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterRet1Product raw digest) =
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

theorem recoverAfterSumZero_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterSumZero raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterSumZero_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (recoverAfterSumZero raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem recoverAfterSumAdd_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterSumAdd raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterSumAdd_lookup_sum
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "sum" (recoverAfterSumAdd raw digest) =
      UInt256.ofNat 2432 := by
  rfl

theorem recoverAfterSumAdd_lookup_ret2
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret_2" (recoverAfterSumAdd raw digest) =
      UInt256.ofNat 96 := by
  rfl

theorem recoverAfterRet3Zero_lookup_ret2
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret_2" (recoverAfterRet3Zero raw digest) =
      UInt256.ofNat 96 := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_sig_length
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "var_sig_length" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat SigLen := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_sig_offset
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "var_sig_offset" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat 100 := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_ret2
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret_2" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat 96 := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_digest
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "var_digest" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat digest := by
  rfl

theorem recoverAfterRet3FromRet2_lookup_expr
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "expr" (recoverAfterRet3FromRet2 raw digest) =
      UInt256.ofNat SigLen := by
  rfl

theorem recoverAfterRet3FromRet2_toState_calldata
    (raw : RawSig) (digest : Digest) :
    (recoverAfterRet3FromRet2 raw digest).toState.executionEnv.calldata =
      encodeForsCalldata raw digest := by
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

theorem exec_recover_sum_zero
    (raw : RawSig) (digest : Digest) :
    exec 34 (.Let ["sum"] (.some (.Lit (UInt256.ofNat 0))))
        (some forsVerifierRuntime) (recoverAfterRet1Product raw digest) =
      .ok (recoverAfterSumZero raw digest) := by
  simpa [recoverAfterSumZero] using
    (exec_let_lit (n := 33) (co := some forsVerifierRuntime)
      (s := recoverAfterRet1Product raw digest)
      (vars := ["sum"]) (lit := UInt256.ofNat 0))

theorem exec_recover_sum_add
    (raw : RawSig) (digest : Digest) :
    exec 33 (.Let ["sum"] (.some recoverSetupSumExpr))
        (some forsVerifierRuntime) (recoverAfterSumZero raw digest) =
      .ok (recoverAfterSumAdd raw digest) := by
  let s := recoverAfterSumZero raw digest
  have hret :
      EvmYul.Yul.State.lookup! "ret" s = UInt256.ofNat 0x20 := by
    dsimp [s]
    exact recoverAfterSumZero_lookup_ret raw digest
  have hproduct :
      EvmYul.Yul.State.lookup! "product" s = UInt256.ofNat 2400 := by
    dsimp [s]
    exact recoverAfterSumZero_lookup_product raw digest
  have hvarProduct : eval 31 (.Var "product") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2400) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "product" s) =
      Except.ok (s, UInt256.ofNat 2400)
    rw [hproduct]
  have hvarRet : eval 29 (.Var "ret") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0x20) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "ret" s) =
      Except.ok (s, UInt256.ofNat 0x20)
    rw [hret]
  change exec 33
      (.Let ["sum"] (.some
        (.Call (Sum.inl .ADD) [.Var "ret", .Var "product"])))
      (some forsVerifierRuntime) s = .ok (recoverAfterSumAdd raw digest)
  rw [exec_let_prim (n := 32)]
  show execPrimCall 32 .ADD ["sum"]
      (reverse' (evalArgs 32 [.Var "product", .Var "ret"]
        (some forsVerifierRuntime) s)) =
    .ok (recoverAfterSumAdd raw digest)
  rw [evalArgs_cons_ok (n := 31) (arg := .Var "product")
    (args := [.Var "ret"]) (co := some forsVerifierRuntime) (s := s)
    (h := hvarProduct)]
  rw [evalTail_cons_ok (n := 30)]
  rw [evalArgs_cons_ok (n := 29) (arg := .Var "ret")
    (args := []) (co := some forsVerifierRuntime) (s := s) (h := hvarRet)]
  rw [evalTail_cons_ok (n := 28), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rw [execPrimCall_ok
    (vars := ["sum"]) (prim := .ADD)
    (args := [UInt256.ofNat 0x20, UInt256.ofNat 2400])
    (s₁ := s) (vals := [UInt256.ofNat 2432]) (s := s)
    (h := by
      simpa [uint256_add_ret_product] using
        (primCall_add (n := 31) (s := s)
          (UInt256.ofNat 0x20) (UInt256.ofNat 2400)))]
  rfl

theorem eval_recover_setup_overflow_guard
    (raw : RawSig) (digest : Digest) :
    eval 31 recoverSetupOverflowGuardExpr (some forsVerifierRuntime)
        (recoverAfterSumAdd raw digest) =
      .ok (recoverAfterSumAdd raw digest, UInt256.ofNat 0) := by
  let s := recoverAfterSumAdd raw digest
  have hret :
      EvmYul.Yul.State.lookup! "ret" s = UInt256.ofNat 0x20 := by
    dsimp [s]
    exact recoverAfterSumAdd_lookup_ret raw digest
  have hsum :
      EvmYul.Yul.State.lookup! "sum" s = UInt256.ofNat 2432 := by
    dsimp [s]
    exact recoverAfterSumAdd_lookup_sum raw digest
  have hvarRet : eval 27 (.Var "ret") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0x20) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "ret" s) =
      Except.ok (s, UInt256.ofNat 0x20)
    rw [hret]
  have hvarSum : eval 29 (.Var "sum") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2432) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "sum" s) =
      Except.ok (s, UInt256.ofNat 2432)
    rw [hsum]
  change eval 31
      (.Call (Sum.inl .GT) [.Var "ret", .Var "sum"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := 25) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := 29) (s := s)
        (UInt256.ofNat 0x20) (UInt256.ofNat 2432))
      hvarRet hvarSum
  simpa [recoverSetupOverflowGuardExpr, uint256_gt_ret_sum] using hgt

theorem exec_recover_setup_overflow_guard
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec 32 (.If recoverSetupOverflowGuardExpr body) (some forsVerifierRuntime)
        (recoverAfterSumAdd raw digest) =
      .ok (recoverAfterSumAdd raw digest) := by
  exact exec_if_false
    (n := 31) (co := some forsVerifierRuntime)
    (s := recoverAfterSumAdd raw digest)
    (cond := recoverSetupOverflowGuardExpr) (body := body)
    (s' := recoverAfterSumAdd raw digest)
    (eval_recover_setup_overflow_guard raw digest)

theorem exec_recover_ret3_zero
    (raw : RawSig) (digest : Digest) :
    exec 31 (.Let ["ret_3"] (.some (.Lit (UInt256.ofNat 0))))
        (some forsVerifierRuntime) (recoverAfterSumAdd raw digest) =
      .ok (recoverAfterRet3Zero raw digest) := by
  simpa [recoverAfterRet3Zero] using
    (exec_let_lit (n := 30) (co := some forsVerifierRuntime)
      (s := recoverAfterSumAdd raw digest)
      (vars := ["ret_3"]) (lit := UInt256.ofNat 0))

theorem exec_recover_ret3_from_ret2
    (raw : RawSig) (digest : Digest) :
    exec 30 (.Let ["ret_3"] (.some (.Var "ret_2")))
        (some forsVerifierRuntime) (recoverAfterRet3Zero raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest) := by
  let s := recoverAfterRet3Zero raw digest
  have hret2 :
      EvmYul.Yul.State.lookup! "ret_2" s = UInt256.ofNat 96 := by
    dsimp [s]
    exact recoverAfterRet3Zero_lookup_ret2 raw digest
  change exec 30 (.Let ["ret_3"] (.some (.Var "ret_2")))
      (some forsVerifierRuntime) s = .ok (recoverAfterRet3FromRet2 raw digest)
  rw [exec_let_var (n := 29)]
  change Except.ok (s.insert "ret_3" (EvmYul.Yul.State.lookup! "ret_2" s)) =
    Except.ok (recoverAfterRet3FromRet2 raw digest)
  rw [hret2]
  rfl

theorem eval_recover_length_reject_guard
    (raw : RawSig) (digest : Digest) :
    eval 28 recoverLengthRejectGuardExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest, UInt256.ofNat 0) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hsig :
      EvmYul.Yul.State.lookup! "var_sig_length" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_sig_length raw digest
  have hexpr :
      EvmYul.Yul.State.lookup! "expr" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_expr raw digest
  have hvarSig : eval 22 (.Var "var_sig_length") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat SigLen) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_length" s) =
      Except.ok (s, UInt256.ofNat SigLen)
    rw [hsig]
  have hvarExpr : eval 24 (.Var "expr") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat SigLen) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "expr" s) =
      Except.ok (s, UInt256.ofNat SigLen)
    rw [hexpr]
  have heq : eval 26
        (.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"])
        (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 1) := by
    have hraw := eval_binop2 (n := 20) (co := some forsVerifierRuntime) (OP := .EQ)
        (f := UInt256.eq)
        (primCall_eq (n := 24) (s := s)
          (UInt256.ofNat SigLen) (UInt256.ofNat SigLen))
        hvarSig hvarExpr
    simpa [uint256_eq_sigLen_sigLen] using hraw
  change eval 28
      (.Call (Sum.inl .ISZERO)
        [.Call (Sum.inl .EQ) [.Var "var_sig_length", .Var "expr"]])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  simpa [recoverLengthRejectGuardExpr, uint256_isZero_one] using
    (eval_unop1 (n := 24) (co := some forsVerifierRuntime) (OP := .ISZERO)
      (f := UInt256.isZero)
      (primCall_iszero (n := 26) (s := s) (UInt256.ofNat 1)) heq)

theorem exec_recover_length_reject_if
    (raw : RawSig) (digest : Digest) :
    exec 29 (.If recoverLengthRejectGuardExpr recoverLengthRejectBody)
        (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest) := by
  exact exec_if_false
    (n := 28) (co := some forsVerifierRuntime)
    (s := recoverAfterRet3FromRet2 raw digest)
    (cond := recoverLengthRejectGuardExpr) (body := recoverLengthRejectBody)
    (s' := recoverAfterRet3FromRet2 raw digest)
    (eval_recover_length_reject_guard raw digest)

/-- Continue `fun_recover` from `sum := 0` through the internal good-length check,
    leaving execution at `forsFunRecover.body.drop 18`. -/
theorem exec_recover_through_length_guard
    (raw : RawSig) (digest : Digest) :
    exec 35 (.Block (forsFunRecover.body.drop 12)) (some forsVerifierRuntime)
        (recoverAfterRet1Product raw digest) =
      exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) := by
  change exec 35
      (.Block (.Let ["sum"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 13))
      (some forsVerifierRuntime) (recoverAfterRet1Product raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 34) (co := some forsVerifierRuntime)
    (s := recoverAfterRet1Product raw digest)
    (st := .Let ["sum"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 13)
    (s₁ := recoverAfterSumZero raw digest)
    (h := exec_recover_sum_zero raw digest)]
  change exec 34
      (.Block (.Let ["sum"] (.some recoverSetupSumExpr) ::
        forsFunRecover.body.drop 14))
      (some forsVerifierRuntime) (recoverAfterSumZero raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 33) (co := some forsVerifierRuntime)
    (s := recoverAfterSumZero raw digest)
    (st := .Let ["sum"] (.some recoverSetupSumExpr))
    (sts := forsFunRecover.body.drop 14)
    (s₁ := recoverAfterSumAdd raw digest)
    (h := exec_recover_sum_add raw digest)]
  change exec 33
      (.Block (.If recoverSetupOverflowGuardExpr constOverflowPanicBody ::
        forsFunRecover.body.drop 15))
      (some forsVerifierRuntime) (recoverAfterSumAdd raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 32) (co := some forsVerifierRuntime)
    (s := recoverAfterSumAdd raw digest)
    (st := .If recoverSetupOverflowGuardExpr constOverflowPanicBody)
    (sts := forsFunRecover.body.drop 15)
    (s₁ := recoverAfterSumAdd raw digest)
    (h := exec_recover_setup_overflow_guard raw digest constOverflowPanicBody)]
  change exec 32
      (.Block (.Let ["ret_3"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 16))
      (some forsVerifierRuntime) (recoverAfterSumAdd raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 31) (co := some forsVerifierRuntime)
    (s := recoverAfterSumAdd raw digest)
    (st := .Let ["ret_3"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 16)
    (s₁ := recoverAfterRet3Zero raw digest)
    (h := exec_recover_ret3_zero raw digest)]
  change exec 31
      (.Block (.Let ["ret_3"] (.some (.Var "ret_2")) ::
        forsFunRecover.body.drop 17))
      (some forsVerifierRuntime) (recoverAfterRet3Zero raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 30) (co := some forsVerifierRuntime)
    (s := recoverAfterRet3Zero raw digest)
    (st := .Let ["ret_3"] (.some (.Var "ret_2")))
    (sts := forsFunRecover.body.drop 17)
    (s₁ := recoverAfterRet3FromRet2 raw digest)
    (h := exec_recover_ret3_from_ret2 raw digest)]
  change exec 30
      (.Block (.If recoverLengthRejectGuardExpr recoverLengthRejectBody ::
        forsFunRecover.body.drop 18))
      (some forsVerifierRuntime) (recoverAfterRet3FromRet2 raw digest) =
    exec 29 (.Block (forsFunRecover.body.drop 18)) (some forsVerifierRuntime)
      (recoverAfterRet3FromRet2 raw digest)
  rw [exec_block_cons_ok
    (n := 29) (co := some forsVerifierRuntime)
    (s := recoverAfterRet3FromRet2 raw digest)
    (st := .If recoverLengthRejectGuardExpr recoverLengthRejectBody)
    (sts := forsFunRecover.body.drop 18)
    (s₁ := recoverAfterRet3FromRet2 raw digest)
    (h := exec_recover_length_reject_if raw digest)]

theorem eval_recover_pkSeed_calldata_offset
    (raw : RawSig) (digest : Digest) :
    eval 7 recoverPkSeedCalldataOffsetExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest, UInt256.ofNat 116) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hoffset :
      EvmYul.Yul.State.lookup! "var_sig_offset" s = UInt256.ofNat 100 := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_sig_offset raw digest
  have hvar : eval 3 (.Var "var_sig_offset") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 100) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_offset" s) =
      Except.ok (s, UInt256.ofNat 100)
    rw [hoffset]
  change eval 7
      (.Call (Sum.inl .ADD) [.Var "var_sig_offset", .Lit (UInt256.ofNat 0x10)])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 116)
  have hadd := eval_binop2 (n := 1) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := 5) (s := s)
        (UInt256.ofNat 100) (UInt256.ofNat 0x10))
      hvar
      (eval_lit (n := 4) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 0x10))
  simpa [recoverPkSeedCalldataOffsetExpr, uint256_add_sig_offset_pkSeed] using hadd

theorem eval_recover_high16_mask
    (raw : RawSig) (digest : Digest) :
    eval 4 recoverHigh16MaskExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest,
        UInt256.ofNat 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000) := by
  let s := recoverAfterRet3FromRet2 raw digest
  simpa [recoverHigh16MaskExpr, uint256_not_low16_mask] using
    (eval_unop1 (n := 0) (co := some forsVerifierRuntime) (OP := .NOT)
      (f := UInt256.lnot)
      (primCall_not (n := 2) (s := s) recoverLow16Mask)
      (eval_lit (n := 1) (co := some forsVerifierRuntime) (s := s)
        (val := recoverLow16Mask)))

theorem eval_recover_pkSeed_calldataload_pair
    (raw : RawSig) (digest : Digest) :
    eval 9 recoverPkSeedCalldataReadExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest,
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 1 ++ forsPayloadChunk raw 2)) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 116) =
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 1 ++ forsPayloadChunk raw 2) := by
    dsimp [s]
    exact calldataload_encode_payload_pair_1 raw digest
      (recoverAfterRet3FromRet2 raw digest).toState
      (recoverAfterRet3FromRet2_toState_calldata raw digest)
  change eval 9 (.Call (Sum.inl .CALLDATALOAD) [recoverPkSeedCalldataOffsetExpr])
      (some forsVerifierRuntime) s =
    .ok (s, EvmYul.uInt256OfByteArray
      (forsPayloadChunk raw 1 ++ forsPayloadChunk raw 2))
  have h := eval_unop1_thread (n := 5) (co := some forsVerifierRuntime)
      (primCall_calldataload (n := 7) s (UInt256.ofNat 116))
      (eval_recover_pkSeed_calldata_offset raw digest)
  rw [hload] at h
  exact h

theorem eval_recover_r_calldataload_pair
    (raw : RawSig) (digest : Digest) :
    eval 4 recoverRCalldataReadExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest,
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 0 ++ forsPayloadChunk raw 1)) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hoffset :
      EvmYul.Yul.State.lookup! "var_sig_offset" s = UInt256.ofNat 100 := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_sig_offset raw digest
  have hvar : eval 2 (.Var "var_sig_offset") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 100) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_offset" s) =
      Except.ok (s, UInt256.ofNat 100)
    rw [hoffset]
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 100) =
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 0 ++ forsPayloadChunk raw 1) := by
    dsimp [s]
    exact calldataload_encode_payload_pair_0 raw digest
      (recoverAfterRet3FromRet2 raw digest).toState
      (recoverAfterRet3FromRet2_toState_calldata raw digest)
  change eval 4 (.Call (Sum.inl .CALLDATALOAD) [.Var "var_sig_offset"])
      (some forsVerifierRuntime) s =
    .ok (s, EvmYul.uInt256OfByteArray
      (forsPayloadChunk raw 0 ++ forsPayloadChunk raw 1))
  have h := eval_unop1_thread (n := 0) (co := some forsVerifierRuntime)
      (primCall_calldataload (n := 2) s (UInt256.ofNat 100))
      hvar
  rw [hload] at h
  exact h

theorem eval_recover_hmsg_domain_word
    (raw : RawSig) (digest : Digest) :
    eval 4 recoverHmsgDomainExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest,
        UInt256.ofNat 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd) := by
  let s := recoverAfterRet3FromRet2 raw digest
  simpa [recoverHmsgDomainExpr, uint256_not_two_domain] using
    (eval_unop1 (n := 0) (co := some forsVerifierRuntime) (OP := .NOT)
      (f := UInt256.lnot)
      (primCall_not (n := 2) (s := s) (UInt256.ofNat 2))
      (eval_lit (n := 1) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 2)))

theorem eval_recover_counter_calldata_base
    (raw : RawSig) (digest : Digest) :
    eval 7 recoverCounterCalldataBaseExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest, UInt256.ofNat 2500) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hoffset :
      EvmYul.Yul.State.lookup! "var_sig_offset" s = UInt256.ofNat 100 := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_sig_offset raw digest
  have hproduct :
      EvmYul.Yul.State.lookup! "product" s = UInt256.ofNat 2400 := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_product raw digest
  have hvarOffset : eval 3 (.Var "var_sig_offset") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 100) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "var_sig_offset" s) =
      Except.ok (s, UInt256.ofNat 100)
    rw [hoffset]
  have hvarProduct : eval 5 (.Var "product") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2400) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "product" s) =
      Except.ok (s, UInt256.ofNat 2400)
    rw [hproduct]
  change eval 7
      (.Call (Sum.inl .ADD) [.Var "var_sig_offset", .Var "product"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 2500)
  have hadd := eval_binop2 (n := 1) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := 5) (s := s)
        (UInt256.ofNat 100) (UInt256.ofNat 2400))
      hvarOffset hvarProduct
  simpa [recoverCounterCalldataBaseExpr, uint256_add_sig_offset_product] using hadd

theorem eval_recover_counter_calldata_offset
    (raw : RawSig) (digest : Digest) :
    eval 11 recoverCounterCalldataOffsetExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest, UInt256.ofNat 2532) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hret :
      EvmYul.Yul.State.lookup! "ret" s = UInt256.ofNat 0x20 := by
    dsimp [s]
    exact recoverAfterRet3FromRet2_lookup_ret raw digest
  have hvarRet : eval 9 (.Var "ret") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 0x20) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "ret" s) =
      Except.ok (s, UInt256.ofNat 0x20)
    rw [hret]
  change eval 11
      (.Call (Sum.inl .ADD) [recoverCounterCalldataBaseExpr, .Var "ret"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 2532)
  have hadd := eval_binop2 (n := 5) (co := some forsVerifierRuntime) (OP := .ADD)
      (f := UInt256.add)
      (primCall_add (n := 9) (s := s)
        (UInt256.ofNat 2500) (UInt256.ofNat 0x20))
      (eval_recover_counter_calldata_base raw digest) hvarRet
  simpa [recoverCounterCalldataOffsetExpr, uint256_add_counter_base_ret] using hadd

theorem eval_recover_counter_calldataload
    (raw : RawSig) (digest : Digest) :
    eval 13 recoverCounterCalldataReadExpr (some forsVerifierRuntime)
        (recoverAfterRet3FromRet2 raw digest) =
      .ok (recoverAfterRet3FromRet2 raw digest,
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 152 ++
            ffi.ByteArray.zeroes
              ({ toBitVec := (↑32 - ↑16 : BitVec System.Platform.numBits) } : USize))) := by
  let s := recoverAfterRet3FromRet2 raw digest
  have hload :
      EvmYul.State.calldataload s.toState (UInt256.ofNat 2532) =
        EvmYul.uInt256OfByteArray
          (forsPayloadChunk raw 152 ++
            ffi.ByteArray.zeroes
              ({ toBitVec := (↑32 - ↑16 : BitVec System.Platform.numBits) } : USize)) := by
    dsimp [s]
    exact calldataload_encode_counter raw digest
      (recoverAfterRet3FromRet2 raw digest).toState
      (recoverAfterRet3FromRet2_toState_calldata raw digest)
  change eval 13 (.Call (Sum.inl .CALLDATALOAD) [recoverCounterCalldataOffsetExpr])
      (some forsVerifierRuntime) s =
    .ok (s, EvmYul.uInt256OfByteArray
      (forsPayloadChunk raw 152 ++
        ffi.ByteArray.zeroes
          ({ toBitVec := (↑32 - ↑16 : BitVec System.Platform.numBits) } : USize)))
  have h := eval_unop1_thread (n := 9) (co := some forsVerifierRuntime)
      (primCall_calldataload (n := 11) s (UInt256.ofNat 2532))
      (eval_recover_counter_calldata_offset raw digest)
  rw [hload] at h
  exact h

end NiceTry.Fors.Bridge
