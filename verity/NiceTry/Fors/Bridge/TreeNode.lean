import NiceTry.Fors.Bridge.TreeLeaf

/-!
# Tree-loop node template (A3): executing node level 1

After the leaf prefix (`TreeLeaf.lean`), each loop iteration climbs five levels.
Level 1 is body statements 3–7:

    let usr_s := and(shl(5, usr_dCursor), ret)
    mstore(0x3a0, or(or(shl(4, usr_t), and(shr(1, usr_dCursor), 15)), <C1>))
    mstore(xor(0x3c0, usr_s), usr_node)
    mstore(xor(0x3e0, usr_s), and(calldataload(add(usr_treePtr, 16)), not(0xff…ff)))
    let usr_node_1 := and(keccak256(0x380, 128), not(0xff…ff))

This file executes them generically in fuel (`exec_tree_body_node1`), with the
per-statement lemmas parameterized so levels 2–5 reuse them (the node-ADRS
store over `(shlBits, shrBits, maskLit, adrsConst)`, the swap stores over the
selector variable, the sibling store over its calldata-offset expression).

Still open for the node value bridge (next): the `usr_s ∈ {0, 32}` case split
reconciling the `xor(0x3c0/0x3e0, usr_s)` swap stores with
`node_derivation_eq_climbLevel_{even,odd}_overwrite`'s left/right chain, which
needs mstore same-offset collapse + disjoint-commute bookkeeping.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 1000000

/-- Pre-typed identifiers for the node levels (see `TreeLeaf.lean` on why). -/
def usrSId : Identifier := "usr_s"
def usrTId : Identifier := "usr_t"
def retId : Identifier := "ret"
def usrNode1Id : Identifier := "usr_node_1"

/-! ## Contract-side words -/

/-- `and(shl(5, usr_dCursor), ret)` — the leaf-level swap selector. -/
def treeSelector0Word (s : EvmYul.Yul.State) : UInt256 :=
  (UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 5)).land s[retId]!

/-- `or(or(shl(<k>, usr_t), and(shr(<j>, usr_dCursor), <m>)), <C>)` — the
    per-level node ADRS word. -/
def treeNodeAdrsWord (s : EvmYul.Yul.State)
    (shlBits shrBits maskLit adrsConst : Nat) : UInt256 :=
  ((UInt256.shiftLeft s[usrTId]! (UInt256.ofNat shlBits)).lor
      ((UInt256.shiftRight s[dCursorId]! (UInt256.ofNat shrBits)).land
        (UInt256.ofNat maskLit))).lor
    (UInt256.ofNat adrsConst)

/-- `and(calldataload(<p>), not(0xff…ff))` — a masked sibling/sk calldata read. -/
def treeMaskedCalldataWord (s : EvmYul.Yul.State) (p : UInt256) : UInt256 :=
  (EvmYul.State.calldataload s.toState p).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-! ## Pure operand evaluations -/

theorem eval_tree_shl_lit_var {n co} {s : EvmYul.Yul.State} {b : UInt256}
    {x : Identifier} :
    eval (n+6) (.Call (Sum.inl .SHL) [.Lit b, .Var x]) co s
      = .ok (s, UInt256.shiftLeft s[x]! b) :=
  eval_binop2 (n := n) (f := fun a b => UInt256.shiftLeft b a)
    (hprim := primCall_shl (n := n+4) (s := s) b s[x]!)
    (he₁ := eval_lit (n := n+1)) (he₂ := eval_var (n := n+3))

theorem eval_tree_shr_lit_var {n co} {s : EvmYul.Yul.State} {b : UInt256}
    {x : Identifier} :
    eval (n+6) (.Call (Sum.inl .SHR) [.Lit b, .Var x]) co s
      = .ok (s, UInt256.shiftRight s[x]! b) :=
  eval_binop2 (n := n) (f := fun a b => UInt256.shiftRight b a)
    (hprim := primCall_shr (n := n+4) (s := s) b s[x]!)
    (he₁ := eval_lit (n := n+1)) (he₂ := eval_var (n := n+3))

theorem eval_tree_xor_lit_var {n co} {s : EvmYul.Yul.State} {b : UInt256}
    {x : Identifier} :
    eval (n+6) (.Call (Sum.inl .XOR) [.Lit b, .Var x]) co s
      = .ok (s, b.xor s[x]!) :=
  eval_binop2 (n := n) (f := UInt256.xor)
    (hprim := primCall_xor (n := n+4) (s := s) b s[x]!)
    (he₁ := eval_lit (n := n+1)) (he₂ := eval_var (n := n+3))

theorem eval_tree_add_var_lit {n co} {s : EvmYul.Yul.State} {x : Identifier}
    {b : UInt256} :
    eval (n+6) (.Call (Sum.inl .ADD) [.Var x, .Lit b]) co s
      = .ok (s, s[x]!.add b) :=
  eval_binop2 (n := n) (f := UInt256.add)
    (hprim := primCall_add (n := n+4) (s := s) s[x]! b)
    (he₁ := eval_var (n := n+1)) (he₂ := eval_lit (n := n+3))

theorem eval_tree_add_var_var {n co} {s : EvmYul.Yul.State} {x y : Identifier} :
    eval (n+6) (.Call (Sum.inl .ADD) [.Var x, .Var y]) co s
      = .ok (s, s[x]!.add s[y]!) :=
  eval_binop2 (n := n) (f := UInt256.add)
    (hprim := primCall_add (n := n+4) (s := s) s[x]! s[y]!)
    (he₁ := eval_var (n := n+1)) (he₂ := eval_var (n := n+3))

/-- The node-ADRS expression evaluates to `treeNodeAdrsWord` (pure). -/
theorem eval_tree_node_adrs {n co} {s : EvmYul.Yul.State}
    (shlBits shrBits maskLit adrsConst : Nat) :
    eval (n+16) (.Call (Sum.inl .OR)
      [.Call (Sum.inl .OR)
         [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat shlBits), .Var "usr_t"],
          .Call (Sum.inl .AND)
            [.Call (Sum.inl .SHR) [.Lit (UInt256.ofNat shrBits), .Var "usr_dCursor"],
             .Lit (UInt256.ofNat maskLit)]],
       .Lit (UInt256.ofNat adrsConst)]) co s
      = .ok (s, treeNodeAdrsWord s shlBits shrBits maskLit adrsConst) :=
  eval_binop2 (n := n+10) (f := UInt256.lor)
    (hprim := primCall_or (n := n+14) (s := s)
      ((UInt256.shiftLeft s[usrTId]! (UInt256.ofNat shlBits)).lor
        ((UInt256.shiftRight s[dCursorId]! (UInt256.ofNat shrBits)).land
          (UInt256.ofNat maskLit)))
      (UInt256.ofNat adrsConst))
    (he₁ := eval_binop2 (n := n+6) (f := UInt256.lor)
      (hprim := primCall_or (n := n+10) (s := s)
        (UInt256.shiftLeft s[usrTId]! (UInt256.ofNat shlBits))
        ((UInt256.shiftRight s[dCursorId]! (UInt256.ofNat shrBits)).land
          (UInt256.ofNat maskLit)))
      (he₁ := eval_tree_shl_lit_var (n := n+2))
      (he₂ := eval_binop2 (n := n+4) (f := UInt256.land)
        (hprim := primCall_and (n := n+8) (s := s)
          (UInt256.shiftRight s[dCursorId]! (UInt256.ofNat shrBits))
          (UInt256.ofNat maskLit))
        (he₁ := eval_tree_shr_lit_var (n := n))
        (he₂ := eval_lit (n := n+7))))
    (he₂ := eval_lit (n := n+13))

/-- A masked calldata read at a pure offset expression. -/
theorem eval_tree_masked_calldata {n co} {s : EvmYul.Yul.State} {e : Expr}
    {p : UInt256}
    (he : eval (n+2) e co s = .ok (s, p)) :
    eval (n+8) (.Call (Sum.inl .AND)
      [.Call (Sum.inl .CALLDATALOAD) [e],
       .Call (Sum.inl .NOT)
         [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]) co s
      = .ok (s, treeMaskedCalldataWord s p) :=
  eval_binop2 (n := n+2) (f := UInt256.land)
    (hprim := primCall_and (n := n+6) (s := s)
      (EvmYul.State.calldataload s.toState p)
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)
    (he₁ := eval_unop1 (n := n) (f := EvmYul.State.calldataload s.toState)
      (hprim := primCall_calldataload (n := n+2) s p) (he := he))
    (he₂ := eval_not_mask (n := n+2)
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff))

/-! ## Statement lemmas (reused by all five levels) -/

/-- Body statement 3: the leaf-level swap selector `let`. -/
theorem exec_tree_selector0_let {n co} (s : EvmYul.Yul.State) :
    exec (n+10) treeSelector0LetStmt co s
      = .ok (s.insert "usr_s" (treeSelector0Word s)) :=
  exec_let_binop (n := n+4)
    (hprim := primCall_and (n := n+8) (s := s)
      (UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 5)) s[retId]!)
    (he₁ := eval_tree_shl_lit_var (n := n))
    (he₂ := eval_var (n := n+7))

/-- The per-level node ADRS store. -/
theorem exec_tree_node_adrs_mstore {n co} (s : EvmYul.Yul.State)
    (shlBits shrBits maskLit adrsConst : Nat) :
    exec (n+18) (treeNodeAdrsStmt shlBits shrBits maskLit adrsConst) co s
      = .ok (s.setMachineState (s.toMachineState.mstore (UInt256.ofNat 0x3a0)
          (treeNodeAdrsWord s shlBits shrBits maskLit adrsConst))) :=
  exec_mstore_lit (n := n+12)
    (he := eval_tree_node_adrs (n := n) shlBits shrBits maskLit adrsConst)

/-- The per-level node swap store `mstore(xor(0x3c0, <s>), <node>)`. -/
theorem exec_tree_node_store {n co} (s : EvmYul.Yul.State)
    (sVar nodeVar : Identifier) :
    exec (n+10) (treeNodeStoreStmt sVar nodeVar) co s
      = .ok (s.setMachineState (s.toMachineState.mstore
          ((UInt256.ofNat 0x3c0).xor s[sVar]!) s[nodeVar]!)) :=
  exec_mstore_expr (n := n+4)
    (he₁ := eval_tree_xor_lit_var (n := n))
    (he₂ := eval_var (n := n+7))

/-- The per-level sibling swap store `mstore(xor(0x3e0, <s>), <masked read>)`. -/
theorem exec_tree_sibling_store {n co} {s : EvmYul.Yul.State}
    (sVar : Identifier) {sibOff : Expr} {p : UInt256}
    (hoff : eval (n+2) sibOff co s = .ok (s, p)) :
    exec (n+10) (treeSiblingStoreStmt sVar sibOff) co s
      = .ok (s.setMachineState (s.toMachineState.mstore
          ((UInt256.ofNat 0x3e0).xor s[sVar]!) (treeMaskedCalldataWord s p))) :=
  exec_mstore_expr (n := n+4)
    (he₁ := eval_tree_xor_lit_var (n := n))
    (he₂ := eval_tree_masked_calldata (n := n) (he := hoff))

/-- The per-level node hash `let <x> := and(keccak256(0x380, 128), not(0xff…ff))`. -/
theorem exec_tree_node_hash_let {n co} (s : EvmYul.Yul.State) (x : Identifier) :
    exec (n+10) (.Let [x] (.some treeNodeHashExpr)) co s
      = .ok ((s.setMachineState
            (s.toMachineState.keccak256 (UInt256.ofNat 0x380) (UInt256.ofNat 128)).2).insert x
          (((s.toMachineState.keccak256 (UInt256.ofNat 0x380) (UInt256.ofNat 128)).1).land
            (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) :=
  exec_let_masked_keccak_lit_lit (n := n)

/-! ## Node level 1: post-states and the assembled trace -/

/-- State after `let usr_s := …` (statement 3). -/
def treeAfterSel0 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_s" (treeSelector0Word s)

/-- State after the level-1 ADRS store (statement 4). -/
def treeAfterNode1Adrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterSel0 s).setMachineState ((treeAfterSel0 s).toMachineState.mstore
    (UInt256.ofNat 0x3a0)
    (treeNodeAdrsWord (treeAfterSel0 s) 4 1 15
      1020847100762815390390123822299599601664))

/-- State after the level-1 node swap store (statement 5). -/
def treeAfterNode1Store (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode1Adrs s).setMachineState ((treeAfterNode1Adrs s).toMachineState.mstore
    ((UInt256.ofNat 0x3c0).xor (treeAfterNode1Adrs s)[usrSId]!)
    (treeAfterNode1Adrs s)[usrNodeId]!)

/-- State after the level-1 sibling swap store (statement 6). -/
def treeAfterSibling1 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode1Store s).setMachineState ((treeAfterNode1Store s).toMachineState.mstore
    ((UInt256.ofNat 0x3e0).xor (treeAfterNode1Store s)[usrSId]!)
    (treeMaskedCalldataWord (treeAfterNode1Store s)
      ((treeAfterNode1Store s)[treePtrId]!.add (UInt256.ofNat 16))))

/-- The value bound to `usr_node_1` (the masked level-1 node keccak). -/
def treeNode1Word (s : EvmYul.Yul.State) : UInt256 :=
  (((treeAfterSibling1 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
      (UInt256.ofNat 128)).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the whole level-1 block (`usr_node_1` bound). -/
def treeAfterNode1 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  ((treeAfterSibling1 s).setMachineState
      ((treeAfterSibling1 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_1" (treeNode1Word s)

/-- **Node level 1 execution.** Body statements 3–7, generically in fuel, from
    any state (the loop instantiates `s := treeAfterLeafHash …`). -/
theorem exec_tree_body_node1 (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+20) (.Block (forsTreeBody.drop 3)) co s
      = exec (n+15) (.Block (forsTreeBody.drop 8)) co (treeAfterNode1 s) := by
  show exec (n+20)
      (.Block (treeSelector0LetStmt
        :: treeNodeAdrsStmt 4 1 15 1020847100762815390390123822299599601664
        :: treeNodeStoreStmt "usr_s" "usr_node"
        :: treeSiblingStoreStmt "usr_s"
             (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 16)])
        :: .Let ["usr_node_1"] (.some treeNodeHashExpr)
        :: forsTreeBody.drop 8)) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+19) treeSelector0LetStmt co s = .ok (treeAfterSel0 s) from
    exec_tree_selector0_let (n := n+9) s)]
  rw [exec_block_cons_ok (h := show
    exec (n+18) (treeNodeAdrsStmt 4 1 15 1020847100762815390390123822299599601664)
        co (treeAfterSel0 s)
      = .ok (treeAfterNode1Adrs s) from
    exec_tree_node_adrs_mstore (n := n) (treeAfterSel0 s) 4 1 15
      1020847100762815390390123822299599601664)]
  rw [exec_block_cons_ok (h := show
    exec (n+17) (treeNodeStoreStmt "usr_s" "usr_node") co (treeAfterNode1Adrs s)
      = .ok (treeAfterNode1Store s) from
    exec_tree_node_store (n := n+7) (treeAfterNode1Adrs s) usrSId usrNodeId)]
  rw [exec_block_cons_ok (h := show
    exec (n+16) (treeSiblingStoreStmt "usr_s"
        (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 16)]))
        co (treeAfterNode1Store s)
      = .ok (treeAfterSibling1 s) from
    exec_tree_sibling_store (n := n+6) usrSId
      (hoff := eval_tree_add_var_lit (n := n+2)))]
  rw [exec_block_cons_ok (h := show
    exec (n+15) (.Let ["usr_node_1"] (.some treeNodeHashExpr)) co (treeAfterSibling1 s)
      = .ok (treeAfterNode1 s) from
    exec_tree_node_hash_let (n := n+5) (treeAfterSibling1 s) usrNode1Id)]

end NiceTry.Fors.Bridge
