import NiceTry.Fors.Bridge.InterpHash
import NiceTry.Fors.Bridge.InterpCall
import NiceTry.Fors.Bridge.AddressShape
import NiceTry.Fors.Bridge.ForsRuntime

/-!
# Tree-loop leaf template (A2): per-iteration memory bookkeeping + leaf hash

`fun_recover`'s 25-tree `for`-loop body starts every iteration with the leaf
derivation:

    mstore(0x3a0, or(shl(128, 3), or(usr_tLeafBase, and(usr_dCursor, 31))))
    mstore(0x3c0, and(calldataload(usr_treePtr), not(0xff…ff)))
    let usr_node := and(keccak256(0x380, ret_2), not(0xff…ff))

This file fixes the loop AST (`forsTreeCond`/`forsTreePost`/`forsTreeBody`, tied
to the transcription by `forsFunRecover_tree_for`), executes the three-statement
leaf prefix **generically in fuel** (`exec_tree_body_leaf_prefix`), shows the
resulting machine state is exactly the `AddressShape` mstore chain over the
pkSeed-factored scratch base (`treeAfterLeafSk_toMachineState`), and concludes
that the bound `usr_node` value is the model's `leafHash`
(`tree_leaf_node_value_eq_leafHash`), via `masked_keccak_toNat` +
`leaf_derivation_eq_overwrite`.

The five node hashes of the body mirror this template (A3); the loop induction
(A4) threads `treeAfterLeafHash` through them.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-! ## Interpreter glue: `multifill` normal forms + statement reducers -/

/-- `multifill` with no variables is a no-op (coarity-0 builtins like `mstore`). -/
theorem multifill_nil_vars (s : EvmYul.Yul.State) (vals : List EvmYul.Literal) :
    s.multifill [] vals = s := by cases s <;> rfl

/-- `multifill` of a single variable is `insert`. -/
theorem multifill_single (s : EvmYul.Yul.State) (x : Identifier) (v : EvmYul.Literal) :
    s.multifill [x] [v] = s.insert x v := by cases s <;> rfl

/-- `mstore(<lit>, e)` for a pure (state-preserving) value expression. -/
theorem exec_mstore_lit {n co} {s : EvmYul.Yul.State} {a v : UInt256} {e : Expr}
    (he : eval (n+4) e co s = .ok (s, v)) :
    exec (n+6) (.ExprStmtCall (.Call (Sum.inl .MSTORE) [.Lit a, e])) co s
      = .ok (s.setMachineState (s.toMachineState.mstore a v)) := by
  rw [exec_exprstmt_prim (n := n+5)]
  show execPrimCall (n+5) .MSTORE [] (reverse' (evalArgs (n+5) [e, .Lit a] co s)) = _
  rw [evalArgs_cons_ok (n := n+4) (h := he), evalTail_cons_ok (n := n+3),
    evalArgs_cons_ok (n := n+2) (h := eval_lit (n := n+1)),
    evalTail_cons_ok (n := n+1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_mstore (n := n+4) s a v), multifill_nil_vars]

/-- `keccak256(<lit>, <var>)` — the leaf hash reads its length from `ret_2`. -/
theorem eval_keccak_lit_var {n co} {s : EvmYul.Yul.State} {off : UInt256}
    {lenVar : Identifier} :
    eval (n+6) (.Call (Sum.inl .KECCAK256) [.Lit off, .Var lenVar]) co s
      = .ok (s.setMachineState (s.toMachineState.keccak256 off s[lenVar]!).2,
             (s.toMachineState.keccak256 off s[lenVar]!).1) :=
  eval_binop2_thread (n := n) (hprim := primCall_keccak256 (n := n+4) s off s[lenVar]!)
    (he₁ := eval_lit (n := n+1)) (he₂ := eval_var (n := n+3))

/-- `let x := and(keccak256(<lit>, <var>), not(<lit>))` — the leaf-hash statement. -/
theorem exec_let_masked_keccak_var_len {n co} {s : EvmYul.Yul.State}
    {x : Identifier} {off maskLit : UInt256} {lenVar : Identifier} :
    exec (n+10) (.Let [x] (.some (.Call (Sum.inl .AND)
        [.Call (Sum.inl .KECCAK256) [.Lit off, .Var lenVar],
         .Call (Sum.inl .NOT) [.Lit maskLit]]))) co s
      = .ok ((s.setMachineState (s.toMachineState.keccak256 off s[lenVar]!).2).insert x
              (((s.toMachineState.keccak256 off s[lenVar]!).1).land maskLit.lnot)) := by
  rw [exec_let_prim (n := n+9)]
  show execPrimCall (n+9) .AND [x]
      (reverse' (evalArgs (n+9)
        [.Call (Sum.inl .NOT) [.Lit maskLit],
         .Call (Sum.inl .KECCAK256) [.Lit off, .Var lenVar]] co s)) = _
  rw [evalArgs_cons_ok (n := n+8) (h := eval_not_mask (n := n+4) maskLit),
    evalTail_cons_ok (n := n+7),
    evalArgs_cons_ok (n := n+6) (h := eval_keccak_lit_var (n := n)),
    evalTail_cons_ok (n := n+5), evalArgs_nil (n := n+4)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_and (n := n+8)
    (s := s.setMachineState (s.toMachineState.keccak256 off s[lenVar]!).2)
    (s.toMachineState.keccak256 off s[lenVar]!).1 maskLit.lnot), multifill_single]

/-- `mstore(e₁, e₂)` for pure (state-preserving) offset and value expressions —
    the node levels' `mstore(xor(0x3c0, usr_s), …)` swap stores. -/
theorem exec_mstore_expr {n co} {s : EvmYul.Yul.State} {a v : UInt256} {e₁ e₂ : Expr}
    (he₁ : eval (n+2) e₁ co s = .ok (s, a))
    (he₂ : eval (n+4) e₂ co s = .ok (s, v)) :
    exec (n+6) (.ExprStmtCall (.Call (Sum.inl .MSTORE) [e₁, e₂])) co s
      = .ok (s.setMachineState (s.toMachineState.mstore a v)) := by
  rw [exec_exprstmt_prim (n := n+5)]
  show execPrimCall (n+5) .MSTORE [] (reverse' (evalArgs (n+5) [e₂, e₁] co s)) = _
  rw [evalArgs_cons_ok (n := n+4) (h := he₂), evalTail_cons_ok (n := n+3),
    evalArgs_cons_ok (n := n+2) (h := he₁),
    evalTail_cons_ok (n := n+1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_mstore (n := n+4) s a v), multifill_nil_vars]

/-- `let x := OP(e₁, e₂)` for a pure binop on pure operands — the node levels'
    selector `let`s (`usr_s_k := and(…, ret)`). -/
theorem exec_let_binop {n co} {s : EvmYul.Yul.State} {x : Identifier}
    {OP : PrimOp} {e₁ e₂ : Expr} {v₁ v₂ out : UInt256}
    (hprim : primCall (n+5) s OP [v₁, v₂] = .ok (s, [out]))
    (he₁ : eval (n+2) e₁ co s = .ok (s, v₁))
    (he₂ : eval (n+4) e₂ co s = .ok (s, v₂)) :
    exec (n+6) (.Let [x] (.some (.Call (Sum.inl OP) [e₁, e₂]))) co s
      = .ok (s.insert x out) := by
  rw [exec_let_prim (n := n+5)]
  show execPrimCall (n+5) OP [x] (reverse' (evalArgs (n+5) [e₂, e₁] co s)) = _
  rw [evalArgs_cons_ok (n := n+4) (h := he₂), evalTail_cons_ok (n := n+3),
    evalArgs_cons_ok (n := n+2) (h := he₁),
    evalTail_cons_ok (n := n+1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := hprim), multifill_single]

/-- `let x := and(keccak256(<lit>, <lit>), not(<lit>))` — the five node-hash
    statements (`keccak256(0x380, 128)`). -/
theorem exec_let_masked_keccak_lit_lit {n co} {s : EvmYul.Yul.State}
    {x : Identifier} {off len maskLit : UInt256} :
    exec (n+10) (.Let [x] (.some (.Call (Sum.inl .AND)
        [.Call (Sum.inl .KECCAK256) [.Lit off, .Lit len],
         .Call (Sum.inl .NOT) [.Lit maskLit]]))) co s
      = .ok ((s.setMachineState (s.toMachineState.keccak256 off len).2).insert x
              (((s.toMachineState.keccak256 off len).1).land maskLit.lnot)) := by
  rw [exec_let_prim (n := n+9)]
  show execPrimCall (n+9) .AND [x]
      (reverse' (evalArgs (n+9)
        [.Call (Sum.inl .NOT) [.Lit maskLit],
         .Call (Sum.inl .KECCAK256) [.Lit off, .Lit len]] co s)) = _
  rw [evalArgs_cons_ok (n := n+8) (h := eval_not_mask (n := n+4) maskLit),
    evalTail_cons_ok (n := n+7),
    evalArgs_cons_ok (n := n+6) (h := eval_keccak (n := n) off len),
    evalTail_cons_ok (n := n+5), evalArgs_nil (n := n+4)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_and (n := n+8)
    (s := s.setMachineState (s.toMachineState.keccak256 off len).2)
    (s.toMachineState.keccak256 off len).1 maskLit.lnot), multifill_single]

/-! ## The tree-loop AST (tied to `forsFunRecover` by `forsFunRecover_tree_for`) -/

/-- Leaf ADRS expression: `or(shl(128, 3), or(usr_tLeafBase, and(usr_dCursor, 31)))`. -/
def treeLeafAdrsExpr : Expr :=
  .Call (Sum.inl .OR)
    [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat 128), .Lit (UInt256.ofNat 3)],
     .Call (Sum.inl .OR)
       [.Var "usr_tLeafBase",
        .Call (Sum.inl .AND) [.Var "usr_dCursor", .Lit (UInt256.ofNat 31)]]]

/-- `mstore(0x3a0, <leaf ADRS>)` — body statement 0. -/
def treeLeafAdrsStmt : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE) [.Lit (UInt256.ofNat 0x3a0), treeLeafAdrsExpr])

/-- Masked sk read: `and(calldataload(usr_treePtr), not(0xff…ff))`. -/
def treeSkReadExpr : Expr :=
  .Call (Sum.inl .AND)
    [.Call (Sum.inl .CALLDATALOAD) [.Var "usr_treePtr"],
     .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]

/-- `mstore(0x3c0, <masked sk>)` — body statement 1. -/
def treeSkStmt : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE) [.Lit (UInt256.ofNat 0x3c0), treeSkReadExpr])

/-- `let usr_node := and(keccak256(0x380, ret_2), not(0xff…ff))` — body statement 2,
    the leaf hash. -/
def treeLeafNodeStmt : Stmt :=
  .Let ["usr_node"] (.some (.Call (Sum.inl .AND)
    [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0x380), .Var "ret_2"],
     .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]))

/-- `and(keccak256(0x380, 128), not(0xff…ff))` — the node-hash expression
    (each of the five climb levels and the root store hash this). -/
def treeNodeHashExpr : Expr :=
  .Call (Sum.inl .AND)
    [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0x380), .Lit (UInt256.ofNat 128)],
     .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]

/-- `mstore(xor(0x3c0, <s>), <node>)` — current node into the swap-selected slot. -/
def treeNodeStoreStmt (sVar nodeVar : Identifier) : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Call (Sum.inl .XOR) [.Lit (UInt256.ofNat 0x3c0), .Var sVar], .Var nodeVar])

/-- `mstore(xor(0x3e0, <s>), and(calldataload(<sibOff>), not(0xff…ff)))` — auth
    sibling into the other slot. -/
def treeSiblingStoreStmt (sVar : Identifier) (sibOff : Expr) : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Call (Sum.inl .XOR) [.Lit (UInt256.ofNat 0x3e0), .Var sVar],
     .Call (Sum.inl .AND)
       [.Call (Sum.inl .CALLDATALOAD) [sibOff],
        .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]])

/-- `mstore(0x3a0, or(or(shl(<k>, usr_t), and(shr(<j>, usr_dCursor), <m>)), <C>))`
    — the per-level node ADRS store. -/
def treeNodeAdrsStmt (shlBits shrBits maskLit adrsConst : Nat) : Stmt :=
  .ExprStmtCall (.Call (Sum.inl .MSTORE)
    [.Lit (UInt256.ofNat 0x3a0),
     .Call (Sum.inl .OR)
       [.Call (Sum.inl .OR)
          [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat shlBits), .Var "usr_t"],
           .Call (Sum.inl .AND)
             [.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat shrBits), .Var "usr_dCursor"],
              .Lit (UInt256.ofNat maskLit)]],
        .Lit (UInt256.ofNat adrsConst)]])

/-- `let <x> := and(and(and(shl(<b>, usr_dCursor), not(31)), <m>), ret)` — the
    per-level sibling-swap selector. -/
def treeSelectorLetStmt (x : Identifier) (shlBits : Nat) (mid : Expr) : Stmt :=
  .Let [x] (.some (.Call (Sum.inl .AND)
    [.Call (Sum.inl .AND)
       [.Call (Sum.inl .AND)
          [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat shlBits), .Var "usr_dCursor"],
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 31)]],
        mid],
     .Var "ret"]))

/-- `let usr_s := and(shl(5, usr_dCursor), ret)` — the leaf-level swap selector. -/
def treeSelector0LetStmt : Stmt :=
  .Let ["usr_s"] (.some (.Call (Sum.inl .AND)
    [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat 5), .Var "usr_dCursor"], .Var "ret"]))

/-- The loop condition `lt(usr_t, 25)`. -/
def forsTreeCond : Expr := .Call (Sum.inl .LT) [.Var "usr_t", .Lit (UInt256.ofNat 25)]

/-- The loop post block (pointer advance + `usr_dCursor := shr(5, usr_dCursor)`). -/
def forsTreePost : List Stmt :=
  [.Let ["usr_t"] (.some (.Call (Sum.inl .ADD) [.Var "usr_t", .Lit (UInt256.ofNat 1)])),
   .Let ["usr_treePtr"] (.some (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Var "ret_2"])),
   .Let ["usr_rootPtr"] (.some (.Call (Sum.inl .ADD) [.Var "usr_rootPtr", .Var "ret"])),
   .Let ["usr_tLeafBase"] (.some (.Call (Sum.inl .ADD) [.Var "usr_tLeafBase", .Var "ret"])),
   .Let ["usr_dCursor"] (.some (.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat 5), .Var "usr_dCursor"]))]

/-- The 25-tree `for`-loop body of `fun_recover`, verbatim from the transcription. -/
def forsTreeBody : List Stmt :=
  [treeLeafAdrsStmt,
   treeSkStmt,
   treeLeafNodeStmt,
   treeSelector0LetStmt,
   treeNodeAdrsStmt 4 1 15 1020847100762815390390123822299599601664,
   treeNodeStoreStmt "usr_s" "usr_node",
   treeSiblingStoreStmt "usr_s"
     (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 16)]),
   .Let ["usr_node_1"] (.some treeNodeHashExpr),
   treeSelectorLetStmt "usr_s_1" 4 (.Lit (UInt256.ofNat 480)),
   treeNodeAdrsStmt 3 2 7 1020847100762815390390123822303894568960,
   treeNodeStoreStmt "usr_s_1" "usr_node_1",
   treeSiblingStoreStmt "usr_s_1"
     (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Var "ret"]),
   .Let ["usr_node_2"] (.some treeNodeHashExpr),
   treeSelectorLetStmt "usr_s_2" 3 (.Lit (UInt256.ofNat 224)),
   treeNodeAdrsStmt 2 3 3 1020847100762815390390123822308189536256,
   treeNodeStoreStmt "usr_s_2" "usr_node_2",
   treeSiblingStoreStmt "usr_s_2"
     (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 48)]),
   .Let ["usr_node_3"] (.some treeNodeHashExpr),
   treeSelectorLetStmt "usr_s_3" 2 (.Var "ret_2"),
   treeNodeAdrsStmt 1 4 1 1020847100762815390390123822312484503552,
   treeNodeStoreStmt "usr_s_3" "usr_node_3",
   treeSiblingStoreStmt "usr_s_3"
     (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 64)]),
   .Let ["usr_node_4"] (.some treeNodeHashExpr),
   treeSelectorLetStmt "usr_s_4" 1 (.Var "ret"),
   .ExprStmtCall (.Call (Sum.inl .MSTORE)
     [.Lit (UInt256.ofNat 0x3a0),
      .Call (Sum.inl .OR)
        [.Var "usr_t", .Lit (UInt256.ofNat 1020847100762815390390123822316779470848)]]),
   treeNodeStoreStmt "usr_s_4" "usr_node_4",
   treeSiblingStoreStmt "usr_s_4"
     (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 80)]),
   .ExprStmtCall (.Call (Sum.inl .MSTORE) [.Var "usr_rootPtr", treeNodeHashExpr])]

/-- The FORS tree `for` statement. -/
def forsTreeFor : Stmt := .For forsTreeCond forsTreePost forsTreeBody

/-- **Tie-down**: the statement at position 32 of `fun_recover`'s body is exactly
    `forsTreeFor`. Everything proved about `forsTreeBody` is about the real
    transcription. -/
theorem forsFunRecover_tree_for : forsFunRecover.body[32]? = some forsTreeFor := rfl

/-! ## Post-states of the leaf prefix -/

/-- Pre-typed loop-variable identifiers. (`Identifier` is a non-reducible `def`
    of `String`, so a raw string literal does not trigger the `Yul.State`
    `GetElem` instance; these constants do, and stay defeq to the literals the
    AST carries.) -/
def tLeafBaseId : Identifier := "usr_tLeafBase"
def dCursorId : Identifier := "usr_dCursor"
def treePtrId : Identifier := "usr_treePtr"
def ret2Id : Identifier := "ret_2"
def usrNodeId : Identifier := "usr_node"

/-- Contract-side leaf ADRS word: `or(shl(128, 3), or(tLeafBase, and(dCursor, 31)))`. -/
def treeLeafAdrsWord (tLeafBase dCursor : UInt256) : UInt256 :=
  (UInt256.shiftLeft (UInt256.ofNat 3) (UInt256.ofNat 128)).lor
    (tLeafBase.lor (dCursor.land (UInt256.ofNat 31)))

/-- State after `mstore(0x3a0, <leaf ADRS>)`. -/
def treeAfterLeafAdrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0x3a0)
    (treeLeafAdrsWord s[tLeafBaseId]! s[dCursorId]!))

/-- Contract-side masked sk word (the calldata read at `usr_treePtr`). -/
def treeSkWord (s : EvmYul.Yul.State) : UInt256 :=
  (EvmYul.State.calldataload s.toState s[treePtrId]!).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the two leaf `mstore`s. -/
def treeAfterLeafSk (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterLeafAdrs s).setMachineState
    ((treeAfterLeafAdrs s).toMachineState.mstore (UInt256.ofNat 0x3c0)
      (treeSkWord (treeAfterLeafAdrs s)))

/-- The value the leaf prefix binds to `usr_node` (the masked leaf keccak). -/
def treeLeafNodeWord (s : EvmYul.Yul.State) : UInt256 :=
  (((treeAfterLeafSk s).toMachineState.keccak256 (UInt256.ofNat 0x380)
      (treeAfterLeafSk s)[ret2Id]!).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the whole leaf prefix (`usr_node` bound, keccak `activeWords` bumped). -/
def treeAfterLeafHash (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  ((treeAfterLeafSk s).setMachineState
      ((treeAfterLeafSk s).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (treeAfterLeafSk s)[ret2Id]!).2).insert "usr_node" (treeLeafNodeWord s)

/-! ## Executing the leaf prefix -/

/-- The leaf ADRS expression evaluates to `treeLeafAdrsWord` (pure). -/
theorem eval_tree_leaf_adrs {n co} {s : EvmYul.Yul.State} :
    eval (n+10) treeLeafAdrsExpr co s
      = .ok (s, treeLeafAdrsWord s[tLeafBaseId]! s[dCursorId]!) :=
  eval_binop2 (n := n+4) (f := UInt256.lor)
    (hprim := primCall_or (n := n+8) (s := s)
      (UInt256.shiftLeft (UInt256.ofNat 3) (UInt256.ofNat 128))
      (s[tLeafBaseId]!.lor (s[dCursorId]!.land (UInt256.ofNat 31))))
    (he₁ := eval_binop2 (n := n) (f := fun a b => UInt256.shiftLeft b a)
      (hprim := primCall_shl (n := n+4) (s := s) (UInt256.ofNat 128) (UInt256.ofNat 3))
      (he₁ := eval_lit (n := n+1)) (he₂ := eval_lit (n := n+3)))
    (he₂ := eval_binop2 (n := n+2) (f := UInt256.lor)
      (hprim := primCall_or (n := n+6) (s := s) s[tLeafBaseId]!
        (s[dCursorId]!.land (UInt256.ofNat 31)))
      (he₁ := eval_var (n := n+3))
      (he₂ := eval_binop2 (n := n) (f := UInt256.land)
        (hprim := primCall_and (n := n+4) (s := s) s[dCursorId]! (UInt256.ofNat 31))
        (he₁ := eval_var (n := n+1)) (he₂ := eval_lit (n := n+3))))

/-- Body statement 0: the leaf ADRS store. -/
theorem exec_tree_leaf_adrs_mstore {n co} (s : EvmYul.Yul.State) :
    exec (n+12) treeLeafAdrsStmt co s = .ok (treeAfterLeafAdrs s) :=
  exec_mstore_lit (n := n+6) (he := eval_tree_leaf_adrs (n := n))

/-- The masked sk read evaluates to `treeSkWord` (pure). -/
theorem eval_tree_sk_read {n co} {s : EvmYul.Yul.State} :
    eval (n+8) treeSkReadExpr co s = .ok (s, treeSkWord s) :=
  eval_binop2 (n := n+2) (f := UInt256.land)
    (hprim := primCall_and (n := n+6) (s := s)
      (EvmYul.State.calldataload s.toState s[treePtrId]!)
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)
    (he₁ := eval_unop1 (n := n) (f := EvmYul.State.calldataload s.toState)
      (hprim := primCall_calldataload (n := n+2) s s[treePtrId]!)
      (he := eval_var (n := n+1)))
    (he₂ := eval_not_mask (n := n+2) (UInt256.ofNat 0xffffffffffffffffffffffffffffffff))

/-- Body statement 1: the masked sk store. -/
theorem exec_tree_sk_mstore {n co} (s : EvmYul.Yul.State) :
    exec (n+10) treeSkStmt co s
      = .ok (s.setMachineState
          (s.toMachineState.mstore (UInt256.ofNat 0x3c0) (treeSkWord s))) :=
  exec_mstore_lit (n := n+4) (he := eval_tree_sk_read (n := n))

/-- Body statement 2: the leaf keccak `let`. -/
theorem exec_tree_leaf_node_let {n co} (s : EvmYul.Yul.State) :
    exec (n+10) treeLeafNodeStmt co s
      = .ok ((s.setMachineState
            (s.toMachineState.keccak256 (UInt256.ofNat 0x380) s[ret2Id]!).2).insert
          "usr_node"
          (((s.toMachineState.keccak256 (UInt256.ofNat 0x380) s[ret2Id]!).1).land
            (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) :=
  exec_let_masked_keccak_var_len (n := n)

/-- **Leaf-prefix execution.** The first three loop-body statements, generically
    in fuel, ending in `treeAfterLeafHash`. -/
theorem exec_tree_body_leaf_prefix (n : Nat) (co : Option YulContract)
    (ss : SharedState .Yul) (vs : VarStore) :
    exec (n+13) (.Block forsTreeBody) co (.Ok ss vs)
      = exec (n+10) (.Block (forsTreeBody.drop 3)) co (treeAfterLeafHash (.Ok ss vs)) := by
  show exec (n+13)
      (.Block (treeLeafAdrsStmt :: treeSkStmt :: treeLeafNodeStmt :: forsTreeBody.drop 3))
      co (.Ok ss vs) = _
  rw [exec_block_cons_ok (h := exec_tree_leaf_adrs_mstore (n := n) (.Ok ss vs))]
  rw [exec_block_cons_ok (h := show
    exec (n+11) treeSkStmt co (treeAfterLeafAdrs (.Ok ss vs))
      = .ok (treeAfterLeafSk (.Ok ss vs)) from
    exec_tree_sk_mstore (n := n+1) (treeAfterLeafAdrs (.Ok ss vs)))]
  rw [exec_block_cons_ok (h := show
    exec (n+10) treeLeafNodeStmt co (treeAfterLeafSk (.Ok ss vs))
      = .ok (treeAfterLeafHash (.Ok ss vs)) from
    exec_tree_leaf_node_let (n := n) (treeAfterLeafSk (.Ok ss vs)))]

/-! ## A2: the memory-bookkeeping bridge to `AddressShape` -/

/-- The first store leaves the varstore untouched. -/
theorem treeAfterLeafAdrs_getElem (ss : SharedState .Yul) (vs : VarStore)
    (x : Identifier) :
    (treeAfterLeafAdrs (.Ok ss vs))[x]! = (EvmYul.Yul.State.Ok ss vs)[x]! := rfl

/-- The first store leaves `toState` (hence calldata) untouched. -/
theorem treeAfterLeafAdrs_toState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterLeafAdrs (.Ok ss vs)).toState = (EvmYul.Yul.State.Ok ss vs).toState := rfl

/-- Both stores leave the varstore untouched. -/
theorem treeAfterLeafSk_getElem (ss : SharedState .Yul) (vs : VarStore)
    (x : Identifier) :
    (treeAfterLeafSk (.Ok ss vs))[x]! = (EvmYul.Yul.State.Ok ss vs)[x]! := rfl

/-- The sk word read after the ADRS store is the entry state's sk word. -/
theorem treeSkWord_after_adrs (ss : SharedState .Yul) (vs : VarStore) :
    treeSkWord (treeAfterLeafAdrs (.Ok ss vs)) = treeSkWord (.Ok ss vs) := rfl

/-- **A2 bookkeeping.** After the two leaf `mstore`s the machine state is exactly
    the `AddressShape` mstore chain on the entry machine state — the form
    `leaf_derivation_eq_overwrite` consumes once the entry machine state is
    factored as `m.mstore 0x380 pkSeed`. -/
theorem treeAfterLeafSk_toMachineState (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterLeafSk (.Ok ss vs)).toMachineState
      = ((EvmYul.Yul.State.Ok ss vs).toMachineState.mstore (UInt256.ofNat 0x3a0)
            (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
              (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)).mstore
          (UInt256.ofNat 0x3c0) (treeSkWord (.Ok ss vs)) := rfl

/-! ### Reading the varstore after the leaf prefix (A3 handoff) -/

/-- `getElem!` ↔ `lookup!` on an `.Ok` state (the `GetElem` instance ignores the
    membership proof; an out-of-store read defaults to `0` on both sides). -/
theorem state_getElem!_eq_lookup! (ss : SharedState .Yul) (vs : VarStore)
    (y : Identifier) :
    (EvmYul.Yul.State.Ok ss vs)[y]! = EvmYul.Yul.State.lookup! y (.Ok ss vs) := by
  by_cases h : y ∈ vs
  · rw [getElem!_pos]
    · rfl
    · exact h
  · rw [getElem!_neg]
    · show Inhabited.default = ((vs.lookup y).get!)
      rw [Finmap.lookup_eq_none.mpr h]
      rfl
    · exact h

/-- Reading a freshly inserted variable. -/
theorem state_getElem_insert_self (ss : SharedState .Yul) (vs : VarStore)
    (x : Identifier) (v : EvmYul.Literal) :
    ((EvmYul.Yul.State.Ok ss vs).insert x v)[x]! = v := by
  show (EvmYul.Yul.State.Ok ss (vs.insert x v))[x]! = v
  rw [getElem!_pos]
  · show ((vs.insert x v).lookup x).get! = v
    rw [Finmap.lookup_insert]
    rfl
  · show x ∈ vs.insert x v
    exact Finmap.mem_insert.mpr (Or.inl rfl)

/-- Reading any other variable after an insert. -/
theorem state_getElem_insert_ne (ss : SharedState .Yul) (vs : VarStore)
    {x y : Identifier} (v : EvmYul.Literal) (h : y ≠ x) :
    ((EvmYul.Yul.State.Ok ss vs).insert x v)[y]!
      = (EvmYul.Yul.State.Ok ss vs)[y]! := by
  show (EvmYul.Yul.State.Ok ss (vs.insert x v))[y]! = _
  rw [state_getElem!_eq_lookup!, state_getElem!_eq_lookup!]
  show ((vs.insert x v).lookup y).get! = ((vs.lookup y).get!)
  rw [Finmap.lookup_insert_of_ne _ h]

/-- Reading `usr_node` back after the leaf prefix — what statement 5's
    `mstore(xor(0x3c0, usr_s), usr_node)` evaluates `usr_node` to (A3). -/
theorem treeAfterLeafHash_getElem_usr_node (ss : SharedState .Yul) (vs : VarStore) :
    (treeAfterLeafHash (.Ok ss vs))[usrNodeId]! = treeLeafNodeWord (.Ok ss vs) :=
  state_getElem_insert_self _ _ _ _

/-- Concrete-offset `toNat` bridge (mirrors `EvmMemory`'s private lemma). -/
private theorem uint256_ofNat_toNat (k : Nat) (h : k < EvmYul.UInt256.size) :
    (UInt256.ofNat k).toNat = k := by
  unfold UInt256.ofNat UInt256.toNat
  rw [Fin.ofNat_eq_cast]
  exact Fin.val_cast_of_lt h

/-- **A2 (leaf template, end-to-end value).** Under the factored scratch form
    (`pkSeed` at `0x380`, `ret_2 = 96`), the value the leaf prefix binds to
    `usr_node` is the model's `leafHash` of the (still symbolic) masked sk word.
    `hadrs` is the ADRS-word arithmetic the loop invariant supplies (A4). -/
theorem tree_leaf_node_value_eq_leafHash
    (ss : SharedState .Yul) (vs : VarStore) (m : MachineState)
    (oScratch pkSeed : UInt256) (tree leafIdx : Nat)
    (hm : (EvmYul.Yul.State.Ok ss vs).toMachineState = m.mstore oScratch pkSeed)
    (hScratch : oScratch.toNat = ScratchBase)
    (hlen : (EvmYul.Yul.State.Ok ss vs)[ret2Id]! = UInt256.ofNat 96)
    (hadrs : (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
        (EvmYul.Yul.State.Ok ss vs)[dCursorId]!).toNat = shapeLeafAdrsWord tree leafIdx)
    (hsize : ScratchBase + LeafHashLen ≤ m.memory.size) :
    (treeLeafNodeWord (.Ok ss vs)).toNat
      = leafHash pkSeed.toNat (leafAdrs tree leafIdx)
          (treeSkWord (.Ok ss vs)).toNat := by
  unfold treeLeafNodeWord
  rw [treeAfterLeafSk_getElem, hlen, masked_keccak_toNat,
    treeAfterLeafSk_toMachineState, hm]
  rw [show (UInt256.ofNat 0x380).toNat = ScratchBase from
        uint256_ofNat_toNat 0x380 (by decide),
      show (UInt256.ofNat 96).toNat = LeafHashLen from
        uint256_ofNat_toNat 96 (by decide)]
  exact leaf_derivation_eq_overwrite m oScratch (UInt256.ofNat 0x3a0) (UInt256.ofNat 0x3c0)
    pkSeed
    (treeLeafAdrsWord (EvmYul.Yul.State.Ok ss vs)[tLeafBaseId]!
      (EvmYul.Yul.State.Ok ss vs)[dCursorId]!)
    (treeSkWord (.Ok ss vs)) tree leafIdx hScratch
    (uint256_ofNat_toNat 0x3a0 (by decide)) (uint256_ofNat_toNat 0x3c0 (by decide))
    hadrs hsize

end NiceTry.Fors.Bridge
