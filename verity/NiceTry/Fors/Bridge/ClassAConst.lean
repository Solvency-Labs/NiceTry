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

variable {base : Nat}

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

/-- `add(32, product)` in `constant_FORS_SIG_LEN()`. -/
def constSigLenSumExpr : Expr :=
  .Call (Sum.inl .ADD) [.Lit (UInt256.ofNat 32), .Var "product"]

/-- `gt(32, sum)`, the first overflow guard in `constant_FORS_SIG_LEN()`. -/
def constSigLenFirstGuardExpr : Expr :=
  .Call (Sum.inl .GT) [.Lit (UInt256.ofNat 32), .Var "sum"]

/-- `add(product, 48)` in `constant_FORS_SIG_LEN()`. -/
def constSigLenSum1Expr : Expr :=
  .Call (Sum.inl .ADD) [.Var "product", .Lit (UInt256.ofNat 48)]

/-- `gt(sum, sum_1)`, the second overflow guard in `constant_FORS_SIG_LEN()`. -/
def constSigLenSecondGuardExpr : Expr :=
  .Call (Sum.inl .GT) [.Var "sum", .Var "sum_1"]

/-- Shared panic/revert body used by the constant getter's overflow guards. -/
def constOverflowPanicBody : List Stmt :=
  [.ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Lit (UInt256.ofNat 0),
     .Call (Sum.inl .SHL)
      [.Lit (UInt256.ofNat 224), .Lit (UInt256.ofNat 0x4e487b71)]]),
   .ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Lit (UInt256.ofNat 4), .Lit (UInt256.ofNat 0x11)]),
   .ExprStmtCall (.Call (Sum.inl .REVERT)
    [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 0x24)])]

def constAfterSumZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterRet1Product raw digest).insert "sum" (UInt256.ofNat 0)

def constAfterSumAdd (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterSumZero raw digest).insert "sum" (UInt256.ofNat 2432)

def constAfterSum1Add (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterSumAdd raw digest).insert "sum_1" (UInt256.ofNat SigLen)

def constAfterRet (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (constAfterSum1Add raw digest).insert "ret" (UInt256.ofNat SigLen)

/-- Recover-frame state after `expr := constant_FORS_SIG_LEN()` returns. -/
def recoverAfterExprConst (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterVarInit raw digest).insert "expr" (UInt256.ofNat SigLen)

private theorem uint256_add_32_product :
    (UInt256.ofNat 32).add (UInt256.ofNat 2400) = UInt256.ofNat 2432 := by
  rfl

private theorem uint256_add_product_48 :
    (UInt256.ofNat 2400).add (UInt256.ofNat 48) = UInt256.ofNat SigLen := by
  rfl

private theorem uint256_gt_32_sum :
    UInt256.gt (UInt256.ofNat 32) (UInt256.ofNat 2432) = UInt256.ofNat 0 := by
  rfl

private theorem uint256_gt_sum_sum1 :
    UInt256.gt (UInt256.ofNat 2432) (UInt256.ofNat SigLen) = UInt256.ofNat 0 := by
  rfl

theorem constAfterScratchZero2_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (constAfterScratchZero2 raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem constAfterRet1Product_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (constAfterRet1Product raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem constAfterSumZero_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (constAfterSumZero raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem constAfterSumAdd_lookup_sum
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "sum" (constAfterSumAdd raw digest) =
      UInt256.ofNat 2432 := by
  rfl

theorem constAfterSumAdd_lookup_product
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "product" (constAfterSumAdd raw digest) =
      UInt256.ofNat 2400 := by
  rfl

theorem constAfterSum1Add_lookup_sum
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "sum" (constAfterSum1Add raw digest) =
      UInt256.ofNat 2432 := by
  rfl

theorem constAfterSum1Add_lookup_sum1
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "sum_1" (constAfterSum1Add raw digest) =
      UInt256.ofNat SigLen := by
  rfl

theorem constAfterRet_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (constAfterRet raw digest) =
      UInt256.ofNat SigLen := by
  rfl

theorem recoverAfterExprConst_lookup_expr
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "expr" (recoverAfterExprConst raw digest) =
      UInt256.ofNat SigLen := by
  rfl

/-- Execute the straight-line prefix of `constant_FORS_SIG_LEN()` through
    `ret_1 := product`, leaving the helper at `forsConstSigLen.body.drop 8`. -/
theorem exec_const_sig_len_prefix_to_ret1_product
    (raw : RawSig) (digest : Digest) :
    exec (base + 40) (.Block forsConstSigLen.body) (some forsVerifierRuntime)
        (constSigLenEntryState raw digest) =
      exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
        (constAfterRet1Product raw digest) := by
  change exec (base + 40)
      (.Block (.Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 1))
      (some forsVerifierRuntime) (constSigLenEntryState raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 39) (co := some forsVerifierRuntime)
    (s := constSigLenEntryState raw digest)
    (st := .Let ["ret_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 1)
    (s₁ := constAfterRet1Zero raw digest)
    (h := by
      simpa [constAfterRet1Zero] using
        (exec_let_lit (n := base + 38) (co := some forsVerifierRuntime)
          (s := constSigLenEntryState raw digest)
          (vars := ["ret_1"]) (lit := UInt256.ofNat 0)))]
  change exec (base + 39)
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 2))
      (some forsVerifierRuntime) (constAfterRet1Zero raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 38) (co := some forsVerifierRuntime)
    (s := constAfterRet1Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 2)
    (s₁ := constAfterRet2Zero raw digest)
    (h := by
      simpa [constAfterRet2Zero] using
        (exec_let_lit (n := base + 37) (co := some forsVerifierRuntime)
          (s := constAfterRet1Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 0)))]
  change exec (base + 38)
      (.Block (.Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))) ::
        forsConstSigLen.body.drop 3))
      (some forsVerifierRuntime) (constAfterRet2Zero raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 37) (co := some forsVerifierRuntime)
    (s := constAfterRet2Zero raw digest)
    (st := .Let ["ret_2"] (.some (.Lit (UInt256.ofNat 96))))
    (sts := forsConstSigLen.body.drop 3)
    (s₁ := constAfterRet2NinetySix raw digest)
    (h := by
      simpa [constAfterRet2NinetySix] using
        (exec_let_lit (n := base + 36) (co := some forsVerifierRuntime)
          (s := constAfterRet2Zero raw digest)
          (vars := ["ret_2"]) (lit := UInt256.ofNat 96)))]
  change exec (base + 37)
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 4))
      (some forsVerifierRuntime) (constAfterRet2NinetySix raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 36) (co := some forsVerifierRuntime)
    (s := constAfterRet2NinetySix raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 4)
    (s₁ := constAfterProductZero raw digest)
    (h := by
      simpa [constAfterProductZero] using
        (exec_let_lit (n := base + 35) (co := some forsVerifierRuntime)
          (s := constAfterRet2NinetySix raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 0)))]
  change exec (base + 36)
      (.Block (.Let ["product"] (.some (.Lit (UInt256.ofNat 2400))) ::
        forsConstSigLen.body.drop 5))
      (some forsVerifierRuntime) (constAfterProductZero raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 35) (co := some forsVerifierRuntime)
    (s := constAfterProductZero raw digest)
    (st := .Let ["product"] (.some (.Lit (UInt256.ofNat 2400))))
    (sts := forsConstSigLen.body.drop 5)
    (s₁ := constAfterProduct2400 raw digest)
    (h := by
      simpa [constAfterProduct2400] using
        (exec_let_lit (n := base + 34) (co := some forsVerifierRuntime)
          (s := constAfterProductZero raw digest)
          (vars := ["product"]) (lit := UInt256.ofNat 2400)))]
  change exec (base + 35)
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 6))
      (some forsVerifierRuntime) (constAfterProduct2400 raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 34) (co := some forsVerifierRuntime)
    (s := constAfterProduct2400 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 6)
    (s₁ := constAfterScratchZero1 raw digest)
    (h := by
      simpa [constAfterScratchZero1] using
        (exec_let_lit (n := base + 33) (co := some forsVerifierRuntime)
          (s := constAfterProduct2400 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec (base + 34)
      (.Block (.Let ["_1"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 7))
      (some forsVerifierRuntime) (constAfterScratchZero1 raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 33) (co := some forsVerifierRuntime)
    (s := constAfterScratchZero1 raw digest)
    (st := .Let ["_1"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 7)
    (s₁ := constAfterScratchZero2 raw digest)
    (h := by
      simpa [constAfterScratchZero2] using
        (exec_let_lit (n := base + 32) (co := some forsVerifierRuntime)
          (s := constAfterScratchZero1 raw digest)
          (vars := ["_1"]) (lit := UInt256.ofNat 0)))]
  change exec (base + 33)
      (.Block (.Let ["ret_1"] (.some (.Var "product")) ::
        forsConstSigLen.body.drop 8))
      (some forsVerifierRuntime) (constAfterScratchZero2 raw digest) =
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
      (constAfterRet1Product raw digest)
  rw [exec_block_cons_ok
    (n := base + 32) (co := some forsVerifierRuntime)
    (s := constAfterScratchZero2 raw digest)
    (st := .Let ["ret_1"] (.some (.Var "product")))
    (sts := forsConstSigLen.body.drop 8)
    (s₁ := constAfterRet1Product raw digest)
    (h := by
      simpa [constAfterRet1Product, constAfterScratchZero2_lookup_product raw digest] using
        (exec_let_var (n := base + 31) (co := some forsVerifierRuntime)
          (s := constAfterScratchZero2 raw digest)
          (vars := ["ret_1"]) (id := "product")))]

theorem exec_const_sig_len_sum_zero
    (raw : RawSig) (digest : Digest) :
    exec (base + 31) (.Let ["sum"] (.some (.Lit (UInt256.ofNat 0))))
        (some forsVerifierRuntime) (constAfterRet1Product raw digest) =
      .ok (constAfterSumZero raw digest) := by
  simpa [constAfterSumZero] using
    (exec_let_lit (n := base + 30) (co := some forsVerifierRuntime)
      (s := constAfterRet1Product raw digest)
      (vars := ["sum"]) (lit := UInt256.ofNat 0))

theorem exec_const_sig_len_sum_add
    (raw : RawSig) (digest : Digest) :
    exec (base + 30) (.Let ["sum"] (.some constSigLenSumExpr))
        (some forsVerifierRuntime) (constAfterSumZero raw digest) =
      .ok (constAfterSumAdd raw digest) := by
  let s := constAfterSumZero raw digest
  have hproduct :
      EvmYul.Yul.State.lookup! "product" s = UInt256.ofNat 2400 := by
    dsimp [s]
    exact constAfterSumZero_lookup_product raw digest
  have hvar : eval (base + 28) (.Var "product") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2400) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "product" s) =
      Except.ok (s, UInt256.ofNat 2400)
    rw [hproduct]
  change exec (base + 30)
      (.Let ["sum"] (.some
        (.Call (Sum.inl .ADD) [.Lit (UInt256.ofNat 32), .Var "product"])))
      (some forsVerifierRuntime) s = .ok (constAfterSumAdd raw digest)
  rw [exec_let_prim (n := base + 29)]
  show execPrimCall (base + 29) .ADD ["sum"]
      (reverse' (evalArgs (base + 29) [.Var "product", .Lit (UInt256.ofNat 32)]
        (some forsVerifierRuntime) s)) =
    .ok (constAfterSumAdd raw digest)
  rw [evalArgs_cons_ok (n := base + 28) (arg := .Var "product")
    (args := [.Lit (UInt256.ofNat 32)])
    (co := some forsVerifierRuntime) (s := s) (h := hvar)]
  rw [evalTail_cons_ok (n := base + 27)]
  rw [evalArgs_cons_ok (n := base + 26) (arg := .Lit (UInt256.ofNat 32))
    (args := []) (co := some forsVerifierRuntime) (s := s)
    (h := eval_lit (n := base + 25))]
  rw [evalTail_cons_ok (n := base + 25), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rw [execPrimCall_ok
    (vars := ["sum"]) (prim := .ADD)
    (args := [UInt256.ofNat 32, UInt256.ofNat 2400])
    (s₁ := s) (vals := [UInt256.ofNat 2432]) (s := s)
    (h := by
      simpa [uint256_add_32_product] using
        (primCall_add (n := base + 28) (s := s)
          (UInt256.ofNat 32) (UInt256.ofNat 2400)))]
  rfl

theorem eval_const_sig_len_first_guard
    (raw : RawSig) (digest : Digest) :
    eval (base + 28) constSigLenFirstGuardExpr (some forsVerifierRuntime)
        (constAfterSumAdd raw digest) =
      .ok (constAfterSumAdd raw digest, UInt256.ofNat 0) := by
  let s := constAfterSumAdd raw digest
  have hsum :
      EvmYul.Yul.State.lookup! "sum" s = UInt256.ofNat 2432 := by
    dsimp [s]
    exact constAfterSumAdd_lookup_sum raw digest
  have hvar : eval (base + 26) (.Var "sum") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2432) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "sum" s) =
      Except.ok (s, UInt256.ofNat 2432)
    rw [hsum]
  change eval (base + 28)
      (.Call (Sum.inl .GT) [.Lit (UInt256.ofNat 32), .Var "sum"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := base + 22) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := base + 26) (s := s)
        (UInt256.ofNat 32) (UInt256.ofNat 2432))
      (eval_lit (n := base + 23) (co := some forsVerifierRuntime) (s := s)
        (val := UInt256.ofNat 32))
      hvar
  simpa [constSigLenFirstGuardExpr, uint256_gt_32_sum] using hgt

theorem exec_const_sig_len_first_guard
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec (base + 29) (.If constSigLenFirstGuardExpr body) (some forsVerifierRuntime)
        (constAfterSumAdd raw digest) =
      .ok (constAfterSumAdd raw digest) := by
  exact exec_if_false
    (n := base + 28) (co := some forsVerifierRuntime)
    (s := constAfterSumAdd raw digest)
    (cond := constSigLenFirstGuardExpr) (body := body)
    (s' := constAfterSumAdd raw digest)
    (eval_const_sig_len_first_guard raw digest)

/-- Continue `constant_FORS_SIG_LEN()` through `sum := add(32, product)` and the
    first overflow guard, leaving execution at `forsConstSigLen.body.drop 11`. -/
theorem exec_const_sig_len_through_first_guard
    (raw : RawSig) (digest : Digest) :
    exec (base + 32) (.Block (forsConstSigLen.body.drop 8)) (some forsVerifierRuntime)
        (constAfterRet1Product raw digest) =
      exec (base + 29) (.Block (forsConstSigLen.body.drop 11)) (some forsVerifierRuntime)
        (constAfterSumAdd raw digest) := by
  change exec (base + 32)
      (.Block (.Let ["sum"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsConstSigLen.body.drop 9))
      (some forsVerifierRuntime) (constAfterRet1Product raw digest) =
    exec (base + 29) (.Block (forsConstSigLen.body.drop 11)) (some forsVerifierRuntime)
      (constAfterSumAdd raw digest)
  rw [exec_block_cons_ok
    (n := base + 31) (co := some forsVerifierRuntime)
    (s := constAfterRet1Product raw digest)
    (st := .Let ["sum"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsConstSigLen.body.drop 9)
    (s₁ := constAfterSumZero raw digest)
    (h := exec_const_sig_len_sum_zero raw digest)]
  change exec (base + 31)
      (.Block (.Let ["sum"] (.some constSigLenSumExpr) ::
        forsConstSigLen.body.drop 10))
      (some forsVerifierRuntime) (constAfterSumZero raw digest) =
    exec (base + 29) (.Block (forsConstSigLen.body.drop 11)) (some forsVerifierRuntime)
      (constAfterSumAdd raw digest)
  rw [exec_block_cons_ok
    (n := base + 30) (co := some forsVerifierRuntime)
    (s := constAfterSumZero raw digest)
    (st := .Let ["sum"] (.some constSigLenSumExpr)
    )
    (sts := forsConstSigLen.body.drop 10)
    (s₁ := constAfterSumAdd raw digest)
    (h := exec_const_sig_len_sum_add raw digest)]
  change exec (base + 30)
      (.Block (.If constSigLenFirstGuardExpr constOverflowPanicBody ::
        forsConstSigLen.body.drop 11))
      (some forsVerifierRuntime) (constAfterSumAdd raw digest) =
    exec (base + 29) (.Block (forsConstSigLen.body.drop 11)) (some forsVerifierRuntime)
      (constAfterSumAdd raw digest)
  rw [exec_block_cons_ok
    (n := base + 29) (co := some forsVerifierRuntime)
    (s := constAfterSumAdd raw digest)
    (st := .If constSigLenFirstGuardExpr constOverflowPanicBody)
    (sts := forsConstSigLen.body.drop 11)
    (s₁ := constAfterSumAdd raw digest)
    (h := exec_const_sig_len_first_guard raw digest constOverflowPanicBody)]

theorem exec_const_sig_len_sum1_add
    (raw : RawSig) (digest : Digest) :
    exec (base + 28) (.Let ["sum_1"] (.some constSigLenSum1Expr))
        (some forsVerifierRuntime) (constAfterSumAdd raw digest) =
      .ok (constAfterSum1Add raw digest) := by
  let s := constAfterSumAdd raw digest
  have hproduct :
      EvmYul.Yul.State.lookup! "product" s = UInt256.ofNat 2400 := by
    dsimp [s]
    exact constAfterSumAdd_lookup_product raw digest
  have hvar : eval (base + 24) (.Var "product") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2400) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "product" s) =
      Except.ok (s, UInt256.ofNat 2400)
    rw [hproduct]
  change exec (base + 28)
      (.Let ["sum_1"] (.some
        (.Call (Sum.inl .ADD) [.Var "product", .Lit (UInt256.ofNat 48)])))
      (some forsVerifierRuntime) s = .ok (constAfterSum1Add raw digest)
  rw [exec_let_prim (n := base + 27)]
  show execPrimCall (base + 27) .ADD ["sum_1"]
      (reverse' (evalArgs (base + 27) [.Lit (UInt256.ofNat 48), .Var "product"]
        (some forsVerifierRuntime) s)) =
    .ok (constAfterSum1Add raw digest)
  rw [evalArgs_cons_ok (n := base + 26) (arg := .Lit (UInt256.ofNat 48))
    (args := [.Var "product"])
    (co := some forsVerifierRuntime) (s := s)
    (h := eval_lit (n := base + 25))]
  rw [evalTail_cons_ok (n := base + 25)]
  rw [evalArgs_cons_ok (n := base + 24) (arg := .Var "product")
    (args := []) (co := some forsVerifierRuntime) (s := s) (h := hvar)]
  rw [evalTail_cons_ok (n := base + 23), evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  rw [execPrimCall_ok
    (vars := ["sum_1"]) (prim := .ADD)
    (args := [UInt256.ofNat 2400, UInt256.ofNat 48])
    (s₁ := s) (vals := [UInt256.ofNat SigLen]) (s := s)
    (h := by
      simpa [uint256_add_product_48] using
        (primCall_add (n := base + 26) (s := s)
          (UInt256.ofNat 2400) (UInt256.ofNat 48)))]
  rfl

theorem eval_const_sig_len_second_guard
    (raw : RawSig) (digest : Digest) :
    eval (base + 26) constSigLenSecondGuardExpr (some forsVerifierRuntime)
        (constAfterSum1Add raw digest) =
      .ok (constAfterSum1Add raw digest, UInt256.ofNat 0) := by
  let s := constAfterSum1Add raw digest
  have hsum :
      EvmYul.Yul.State.lookup! "sum" s = UInt256.ofNat 2432 := by
    dsimp [s]
    exact constAfterSum1Add_lookup_sum raw digest
  have hsum1 :
      EvmYul.Yul.State.lookup! "sum_1" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact constAfterSum1Add_lookup_sum1 raw digest
  have hvarSum : eval (base + 22) (.Var "sum") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat 2432) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "sum" s) =
      Except.ok (s, UInt256.ofNat 2432)
    rw [hsum]
  have hvarSum1 : eval (base + 24) (.Var "sum_1") (some forsVerifierRuntime) s =
      .ok (s, UInt256.ofNat SigLen) := by
    rw [eval_var]
    change Except.ok (s, EvmYul.Yul.State.lookup! "sum_1" s) =
      Except.ok (s, UInt256.ofNat SigLen)
    rw [hsum1]
  change eval (base + 26)
      (.Call (Sum.inl .GT) [.Var "sum", .Var "sum_1"])
      (some forsVerifierRuntime) s = .ok (s, UInt256.ofNat 0)
  have hgt := eval_binop2 (n := base + 20) (co := some forsVerifierRuntime) (OP := .GT)
      (f := UInt256.gt)
      (primCall_gt (n := base + 24) (s := s)
        (UInt256.ofNat 2432) (UInt256.ofNat SigLen))
      hvarSum hvarSum1
  simpa [constSigLenSecondGuardExpr, uint256_gt_sum_sum1] using hgt

theorem exec_const_sig_len_second_guard
    (raw : RawSig) (digest : Digest) (body : List Stmt) :
    exec (base + 27) (.If constSigLenSecondGuardExpr body) (some forsVerifierRuntime)
        (constAfterSum1Add raw digest) =
      .ok (constAfterSum1Add raw digest) := by
  exact exec_if_false
    (n := base + 26) (co := some forsVerifierRuntime)
    (s := constAfterSum1Add raw digest)
    (cond := constSigLenSecondGuardExpr) (body := body)
    (s' := constAfterSum1Add raw digest)
    (eval_const_sig_len_second_guard raw digest)

theorem exec_const_sig_len_ret
    (raw : RawSig) (digest : Digest) :
    exec (base + 26) (.Let ["ret"] (.some (.Var "sum_1")))
        (some forsVerifierRuntime) (constAfterSum1Add raw digest) =
      .ok (constAfterRet raw digest) := by
  let s := constAfterSum1Add raw digest
  have hsum1 :
      EvmYul.Yul.State.lookup! "sum_1" s = UInt256.ofNat SigLen := by
    dsimp [s]
    exact constAfterSum1Add_lookup_sum1 raw digest
  change exec (base + 26) (.Let ["ret"] (.some (.Var "sum_1")))
      (some forsVerifierRuntime) s = .ok (constAfterRet raw digest)
  rw [exec_let_var (n := base + 25)]
  change Except.ok (s.insert "ret" (EvmYul.Yul.State.lookup! "sum_1" s)) =
    Except.ok (constAfterRet raw digest)
  rw [hsum1]
  rfl

/-- Finish `constant_FORS_SIG_LEN()` from `forsConstSigLen.body.drop 11`, binding
    `ret = SigLen`. -/
theorem exec_const_sig_len_tail_to_ret
    (raw : RawSig) (digest : Digest) :
    exec (base + 29) (.Block (forsConstSigLen.body.drop 11)) (some forsVerifierRuntime)
        (constAfterSumAdd raw digest) =
      .ok (constAfterRet raw digest) := by
  change exec (base + 29)
      (.Block (.Let ["sum_1"] (.some constSigLenSum1Expr) ::
        forsConstSigLen.body.drop 12))
      (some forsVerifierRuntime) (constAfterSumAdd raw digest) =
    .ok (constAfterRet raw digest)
  rw [exec_block_cons_ok
    (n := base + 28) (co := some forsVerifierRuntime)
    (s := constAfterSumAdd raw digest)
    (st := .Let ["sum_1"] (.some constSigLenSum1Expr))
    (sts := forsConstSigLen.body.drop 12)
    (s₁ := constAfterSum1Add raw digest)
    (h := exec_const_sig_len_sum1_add raw digest)]
  change exec (base + 28)
      (.Block (.If constSigLenSecondGuardExpr constOverflowPanicBody ::
        forsConstSigLen.body.drop 13))
      (some forsVerifierRuntime) (constAfterSum1Add raw digest) =
    .ok (constAfterRet raw digest)
  rw [exec_block_cons_ok
    (n := base + 27) (co := some forsVerifierRuntime)
    (s := constAfterSum1Add raw digest)
    (st := .If constSigLenSecondGuardExpr constOverflowPanicBody)
    (sts := forsConstSigLen.body.drop 13)
    (s₁ := constAfterSum1Add raw digest)
    (h := exec_const_sig_len_second_guard raw digest constOverflowPanicBody)]
  change exec (base + 27)
      (.Block (.Let ["ret"] (.some (.Var "sum_1")) ::
        forsConstSigLen.body.drop 14))
      (some forsVerifierRuntime) (constAfterSum1Add raw digest) =
    .ok (constAfterRet raw digest)
  rw [exec_block_cons_ok
    (n := base + 26) (co := some forsVerifierRuntime)
    (s := constAfterSum1Add raw digest)
    (st := .Let ["ret"] (.some (.Var "sum_1")))
    (sts := forsConstSigLen.body.drop 14)
    (s₁ := constAfterRet raw digest)
    (h := exec_const_sig_len_ret raw digest)]
  change exec (base + 26) (.Block []) (some forsVerifierRuntime)
      (constAfterRet raw digest) = .ok (constAfterRet raw digest)
  exact exec_block_nil (n := base + 25) (co := some forsVerifierRuntime)
    (s := constAfterRet raw digest)

/-- Full execution of `constant_FORS_SIG_LEN()` from the good `fun_recover` call
    entry returns with `ret = SigLen`. -/
theorem exec_const_sig_len_body
    (raw : RawSig) (digest : Digest) :
    exec (base + 40) (.Block forsConstSigLen.body) (some forsVerifierRuntime)
        (constSigLenEntryState raw digest) =
      .ok (constAfterRet raw digest) := by
  rw [exec_const_sig_len_prefix_to_ret1_product raw digest]
  rw [exec_const_sig_len_through_first_guard raw digest]
  exact exec_const_sig_len_tail_to_ret raw digest

theorem exec_recover_const_sig_len_call
    (raw : RawSig) (digest : Digest) :
    execCall (base + 42) "constant_FORS_SIG_LEN" ["expr"] (some forsVerifierRuntime)
        (.ok (recoverAfterVarInit raw digest, [])) =
      .ok (recoverAfterExprConst raw digest) := by
  rw [execCall_ok (n := base + 41)]
  rw [call_ok
    (n := base + 40)
    (s := recoverAfterVarInit raw digest)
    (args := [])
    (fn := "constant_FORS_SIG_LEN")
    (yc := { (Inhabited.default : EvmYul.Account .Yul) with code := forsVerifierRuntime })
    (f := forsConstSigLen)
    (s₂ := constAfterRet raw digest)
    (recoverAfterVarInit_account_find raw digest)
    (by simpa using forsVerifierRuntime_lookup_const_sig_len)
    (exec_const_sig_len_body raw digest)]
  rfl

theorem exec_recover_let_expr_const
    (raw : RawSig) (digest : Digest) :
    exec (base + 43) (.Let ["expr"] (.some (.Call (Sum.inr "constant_FORS_SIG_LEN") [])))
        (some forsVerifierRuntime) (recoverAfterVarInit raw digest) =
      .ok (recoverAfterExprConst raw digest) := by
  rw [exec_recover_let_expr_const_call_args raw digest (base + 41)]
  exact exec_recover_const_sig_len_call raw digest

end NiceTry.Fors.Bridge
