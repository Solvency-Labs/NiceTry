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

/-- The per-level swap selector
    `let <x> := and(and(and(shl(<b>, usr_dCursor), not(31)), <mid>), ret)`
    (levels 2–5; `<mid>` is a literal or a variable, supplied as `hmid`). -/
theorem exec_tree_selector_let {n co} {s : EvmYul.Yul.State} (x : Identifier)
    (shlBits : Nat) {mid : Expr} {midVal : UInt256}
    (hmid : eval (n+12) mid co s = .ok (s, midVal)) :
    exec (n+18) (treeSelectorLetStmt x shlBits mid) co s
      = .ok (s.insert x
          ((((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat shlBits)).land
              (UInt256.ofNat 31).lnot).land midVal).land s[retId]!)) :=
  exec_let_binop (n := n+12)
    (hprim := primCall_and (n := n+16) (s := s)
      (((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat shlBits)).land
          (UInt256.ofNat 31).lnot).land midVal)
      s[retId]!)
    (he₁ := eval_binop2 (n := n+8) (f := UInt256.land)
      (hprim := primCall_and (n := n+12) (s := s)
        ((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat shlBits)).land
          (UInt256.ofNat 31).lnot)
        midVal)
      (he₁ := eval_binop2 (n := n+4) (f := UInt256.land)
        (hprim := primCall_and (n := n+8) (s := s)
          (UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat shlBits))
          (UInt256.ofNat 31).lnot)
        (he₁ := eval_tree_shl_lit_var (n := n))
        (he₂ := eval_not_mask (n := n+4) (UInt256.ofNat 31)))
      (he₂ := hmid))
    (he₂ := eval_var (n := n+15))

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

/-! ## Node level 2: post-states and the assembled trace (statements 8–12) -/

def usrS1Id : Identifier := "usr_s_1"
def usrNode2Id : Identifier := "usr_node_2"

/-- State after `let usr_s_1 := …` (statement 8). -/
def treeAfterSel1 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_s_1"
    ((((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 4)).land
        (UInt256.ofNat 31).lnot).land (UInt256.ofNat 480)).land s[retId]!)

/-- State after the level-2 ADRS store (statement 9). -/
def treeAfterNode2Adrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterSel1 s).setMachineState ((treeAfterSel1 s).toMachineState.mstore
    (UInt256.ofNat 0x3a0)
    (treeNodeAdrsWord (treeAfterSel1 s) 3 2 7
      1020847100762815390390123822303894568960))

/-- State after the level-2 node swap store (statement 10). -/
def treeAfterNode2Store (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode2Adrs s).setMachineState ((treeAfterNode2Adrs s).toMachineState.mstore
    ((UInt256.ofNat 0x3c0).xor (treeAfterNode2Adrs s)[usrS1Id]!)
    (treeAfterNode2Adrs s)[usrNode1Id]!)

/-- State after the level-2 sibling swap store (statement 11; the sibling offset
    is `add(usr_treePtr, ret)`). -/
def treeAfterSibling2 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode2Store s).setMachineState ((treeAfterNode2Store s).toMachineState.mstore
    ((UInt256.ofNat 0x3e0).xor (treeAfterNode2Store s)[usrS1Id]!)
    (treeMaskedCalldataWord (treeAfterNode2Store s)
      ((treeAfterNode2Store s)[treePtrId]!.add (treeAfterNode2Store s)[retId]!)))

/-- The value bound to `usr_node_2` (the masked level-2 node keccak). -/
def treeNode2Word (s : EvmYul.Yul.State) : UInt256 :=
  (((treeAfterSibling2 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
      (UInt256.ofNat 128)).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the whole level-2 block (`usr_node_2` bound). -/
def treeAfterNode2 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  ((treeAfterSibling2 s).setMachineState
      ((treeAfterSibling2 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_2" (treeNode2Word s)

/-- **Node level 2 execution.** Body statements 8–12, generically in fuel. -/
theorem exec_tree_body_node2 (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+20) (.Block (forsTreeBody.drop 8)) co s
      = exec (n+15) (.Block (forsTreeBody.drop 13)) co (treeAfterNode2 s) := by
  show exec (n+20)
      (.Block (treeSelectorLetStmt "usr_s_1" 4 (.Lit (UInt256.ofNat 480))
        :: treeNodeAdrsStmt 3 2 7 1020847100762815390390123822303894568960
        :: treeNodeStoreStmt "usr_s_1" "usr_node_1"
        :: treeSiblingStoreStmt "usr_s_1"
             (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Var "ret"])
        :: .Let ["usr_node_2"] (.some treeNodeHashExpr)
        :: forsTreeBody.drop 13)) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+19) (treeSelectorLetStmt "usr_s_1" 4 (.Lit (UInt256.ofNat 480))) co s
      = .ok (treeAfterSel1 s) from
    exec_tree_selector_let (n := n+1) usrS1Id 4
      (hmid := eval_lit (n := n+12)))]
  rw [exec_block_cons_ok (h := show
    exec (n+18) (treeNodeAdrsStmt 3 2 7 1020847100762815390390123822303894568960)
        co (treeAfterSel1 s)
      = .ok (treeAfterNode2Adrs s) from
    exec_tree_node_adrs_mstore (n := n) (treeAfterSel1 s) 3 2 7
      1020847100762815390390123822303894568960)]
  rw [exec_block_cons_ok (h := show
    exec (n+17) (treeNodeStoreStmt "usr_s_1" "usr_node_1") co (treeAfterNode2Adrs s)
      = .ok (treeAfterNode2Store s) from
    exec_tree_node_store (n := n+7) (treeAfterNode2Adrs s) usrS1Id usrNode1Id)]
  rw [exec_block_cons_ok (h := show
    exec (n+16) (treeSiblingStoreStmt "usr_s_1"
        (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Var "ret"]))
        co (treeAfterNode2Store s)
      = .ok (treeAfterSibling2 s) from
    exec_tree_sibling_store (n := n+6) usrS1Id
      (hoff := eval_tree_add_var_var (n := n+2)))]
  rw [exec_block_cons_ok (h := show
    exec (n+15) (.Let ["usr_node_2"] (.some treeNodeHashExpr)) co (treeAfterSibling2 s)
      = .ok (treeAfterNode2 s) from
    exec_tree_node_hash_let (n := n+5) (treeAfterSibling2 s) usrNode2Id)]

/-! ## Node level 3: post-states and the assembled trace (statements 13–17) -/

def usrS2Id : Identifier := "usr_s_2"
def usrNode3Id : Identifier := "usr_node_3"

/-- State after `let usr_s_2 := …` (statement 13). -/
def treeAfterSel2 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_s_2"
    ((((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 3)).land
        (UInt256.ofNat 31).lnot).land (UInt256.ofNat 224)).land s[retId]!)

/-- State after the level-3 ADRS store (statement 14). -/
def treeAfterNode3Adrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterSel2 s).setMachineState ((treeAfterSel2 s).toMachineState.mstore
    (UInt256.ofNat 0x3a0)
    (treeNodeAdrsWord (treeAfterSel2 s) 2 3 3
      1020847100762815390390123822308189536256))

/-- State after the level-3 node swap store (statement 15). -/
def treeAfterNode3Store (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode3Adrs s).setMachineState ((treeAfterNode3Adrs s).toMachineState.mstore
    ((UInt256.ofNat 0x3c0).xor (treeAfterNode3Adrs s)[usrS2Id]!)
    (treeAfterNode3Adrs s)[usrNode2Id]!)

/-- State after the level-3 sibling swap store (statement 16). -/
def treeAfterSibling3 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode3Store s).setMachineState ((treeAfterNode3Store s).toMachineState.mstore
    ((UInt256.ofNat 0x3e0).xor (treeAfterNode3Store s)[usrS2Id]!)
    (treeMaskedCalldataWord (treeAfterNode3Store s)
      ((treeAfterNode3Store s)[treePtrId]!.add (UInt256.ofNat 48))))

/-- The value bound to `usr_node_3`. -/
def treeNode3Word (s : EvmYul.Yul.State) : UInt256 :=
  (((treeAfterSibling3 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
      (UInt256.ofNat 128)).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the whole level-3 block. -/
def treeAfterNode3 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  ((treeAfterSibling3 s).setMachineState
      ((treeAfterSibling3 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_3" (treeNode3Word s)

/-- **Node level 3 execution.** Body statements 13–17, generically in fuel. -/
theorem exec_tree_body_node3 (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+20) (.Block (forsTreeBody.drop 13)) co s
      = exec (n+15) (.Block (forsTreeBody.drop 18)) co (treeAfterNode3 s) := by
  show exec (n+20)
      (.Block (treeSelectorLetStmt "usr_s_2" 3 (.Lit (UInt256.ofNat 224))
        :: treeNodeAdrsStmt 2 3 3 1020847100762815390390123822308189536256
        :: treeNodeStoreStmt "usr_s_2" "usr_node_2"
        :: treeSiblingStoreStmt "usr_s_2"
             (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 48)])
        :: .Let ["usr_node_3"] (.some treeNodeHashExpr)
        :: forsTreeBody.drop 18)) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+19) (treeSelectorLetStmt "usr_s_2" 3 (.Lit (UInt256.ofNat 224))) co s
      = .ok (treeAfterSel2 s) from
    exec_tree_selector_let (n := n+1) usrS2Id 3
      (hmid := eval_lit (n := n+12)))]
  rw [exec_block_cons_ok (h := show
    exec (n+18) (treeNodeAdrsStmt 2 3 3 1020847100762815390390123822308189536256)
        co (treeAfterSel2 s)
      = .ok (treeAfterNode3Adrs s) from
    exec_tree_node_adrs_mstore (n := n) (treeAfterSel2 s) 2 3 3
      1020847100762815390390123822308189536256)]
  rw [exec_block_cons_ok (h := show
    exec (n+17) (treeNodeStoreStmt "usr_s_2" "usr_node_2") co (treeAfterNode3Adrs s)
      = .ok (treeAfterNode3Store s) from
    exec_tree_node_store (n := n+7) (treeAfterNode3Adrs s) usrS2Id usrNode2Id)]
  rw [exec_block_cons_ok (h := show
    exec (n+16) (treeSiblingStoreStmt "usr_s_2"
        (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 48)]))
        co (treeAfterNode3Store s)
      = .ok (treeAfterSibling3 s) from
    exec_tree_sibling_store (n := n+6) usrS2Id
      (hoff := eval_tree_add_var_lit (n := n+2)))]
  rw [exec_block_cons_ok (h := show
    exec (n+15) (.Let ["usr_node_3"] (.some treeNodeHashExpr)) co (treeAfterSibling3 s)
      = .ok (treeAfterNode3 s) from
    exec_tree_node_hash_let (n := n+5) (treeAfterSibling3 s) usrNode3Id)]

/-! ## Node level 4: post-states and the assembled trace (statements 18–22) -/

def usrS3Id : Identifier := "usr_s_3"
def usrNode4Id : Identifier := "usr_node_4"

/-- State after `let usr_s_3 := …` (statement 18; the mid operand is `ret_2`). -/
def treeAfterSel3 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_s_3"
    ((((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 2)).land
        (UInt256.ofNat 31).lnot).land s[ret2Id]!).land s[retId]!)

/-- State after the level-4 ADRS store (statement 19). -/
def treeAfterNode4Adrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterSel3 s).setMachineState ((treeAfterSel3 s).toMachineState.mstore
    (UInt256.ofNat 0x3a0)
    (treeNodeAdrsWord (treeAfterSel3 s) 1 4 1
      1020847100762815390390123822312484503552))

/-- State after the level-4 node swap store (statement 20). -/
def treeAfterNode4Store (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode4Adrs s).setMachineState ((treeAfterNode4Adrs s).toMachineState.mstore
    ((UInt256.ofNat 0x3c0).xor (treeAfterNode4Adrs s)[usrS3Id]!)
    (treeAfterNode4Adrs s)[usrNode3Id]!)

/-- State after the level-4 sibling swap store (statement 21). -/
def treeAfterSibling4 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode4Store s).setMachineState ((treeAfterNode4Store s).toMachineState.mstore
    ((UInt256.ofNat 0x3e0).xor (treeAfterNode4Store s)[usrS3Id]!)
    (treeMaskedCalldataWord (treeAfterNode4Store s)
      ((treeAfterNode4Store s)[treePtrId]!.add (UInt256.ofNat 64))))

/-- The value bound to `usr_node_4`. -/
def treeNode4Word (s : EvmYul.Yul.State) : UInt256 :=
  (((treeAfterSibling4 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
      (UInt256.ofNat 128)).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the whole level-4 block. -/
def treeAfterNode4 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  ((treeAfterSibling4 s).setMachineState
      ((treeAfterSibling4 s).toMachineState.keccak256 (UInt256.ofNat 0x380)
        (UInt256.ofNat 128)).2).insert "usr_node_4" (treeNode4Word s)

/-- **Node level 4 execution.** Body statements 18–22, generically in fuel. -/
theorem exec_tree_body_node4 (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+20) (.Block (forsTreeBody.drop 18)) co s
      = exec (n+15) (.Block (forsTreeBody.drop 23)) co (treeAfterNode4 s) := by
  show exec (n+20)
      (.Block (treeSelectorLetStmt "usr_s_3" 2 (.Var "ret_2")
        :: treeNodeAdrsStmt 1 4 1 1020847100762815390390123822312484503552
        :: treeNodeStoreStmt "usr_s_3" "usr_node_3"
        :: treeSiblingStoreStmt "usr_s_3"
             (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 64)])
        :: .Let ["usr_node_4"] (.some treeNodeHashExpr)
        :: forsTreeBody.drop 23)) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+19) (treeSelectorLetStmt "usr_s_3" 2 (.Var "ret_2")) co s
      = .ok (treeAfterSel3 s) from
    exec_tree_selector_let (n := n+1) usrS3Id 2
      (hmid := eval_var (n := n+12)))]
  rw [exec_block_cons_ok (h := show
    exec (n+18) (treeNodeAdrsStmt 1 4 1 1020847100762815390390123822312484503552)
        co (treeAfterSel3 s)
      = .ok (treeAfterNode4Adrs s) from
    exec_tree_node_adrs_mstore (n := n) (treeAfterSel3 s) 1 4 1
      1020847100762815390390123822312484503552)]
  rw [exec_block_cons_ok (h := show
    exec (n+17) (treeNodeStoreStmt "usr_s_3" "usr_node_3") co (treeAfterNode4Adrs s)
      = .ok (treeAfterNode4Store s) from
    exec_tree_node_store (n := n+7) (treeAfterNode4Adrs s) usrS3Id usrNode3Id)]
  rw [exec_block_cons_ok (h := show
    exec (n+16) (treeSiblingStoreStmt "usr_s_3"
        (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 64)]))
        co (treeAfterNode4Store s)
      = .ok (treeAfterSibling4 s) from
    exec_tree_sibling_store (n := n+6) usrS3Id
      (hoff := eval_tree_add_var_lit (n := n+2)))]
  rw [exec_block_cons_ok (h := show
    exec (n+15) (.Let ["usr_node_4"] (.some treeNodeHashExpr)) co (treeAfterSibling4 s)
      = .ok (treeAfterNode4 s) from
    exec_tree_node_hash_let (n := n+5) (treeAfterSibling4 s) usrNode4Id)]

/-! ## Node level 5 + the root store (statements 23–27) -/

def usrS4Id : Identifier := "usr_s_4"
def rootPtrId : Identifier := "usr_rootPtr"

theorem eval_tree_or_var_lit {n co} {s : EvmYul.Yul.State} {x : Identifier}
    {b : UInt256} :
    eval (n+6) (.Call (Sum.inl .OR) [.Var x, .Lit b]) co s
      = .ok (s, s[x]!.lor b) :=
  eval_binop2 (n := n) (f := UInt256.lor)
    (hprim := primCall_or (n := n+4) (s := s) s[x]! b)
    (he₁ := eval_var (n := n+1)) (he₂ := eval_lit (n := n+3))

/-- `mstore(e₁, e₂)` where the value `e₂` threads state (the root store's
    keccak) and the offset `e₁` is pure in the *post-`e₂`* state. -/
theorem exec_mstore_thread {n co} {s s' : EvmYul.Yul.State} {a v : UInt256}
    {e₁ e₂ : Expr}
    (he₂ : eval (n+4) e₂ co s = .ok (s', v))
    (he₁ : eval (n+2) e₁ co s' = .ok (s', a)) :
    exec (n+6) (.ExprStmtCall (.Call (Sum.inl .MSTORE) [e₁, e₂])) co s
      = .ok (s'.setMachineState (s'.toMachineState.mstore a v)) := by
  rw [exec_exprstmt_prim (n := n+5)]
  show execPrimCall (n+5) .MSTORE [] (reverse' (evalArgs (n+5) [e₂, e₁] co s)) = _
  rw [evalArgs_cons_ok (n := n+4) (h := he₂), evalTail_cons_ok (n := n+3),
    evalArgs_cons_ok (n := n+2) (h := he₁),
    evalTail_cons_ok (n := n+1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  rw [execPrimCall_ok (h := primCall_mstore (n := n+4) s' a v), multifill_nil_vars]

/-- State after `let usr_s_4 := …` (statement 23; the mid operand is `ret`). -/
def treeAfterSel4 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_s_4"
    ((((UInt256.shiftLeft s[dCursorId]! (UInt256.ofNat 1)).land
        (UInt256.ofNat 31).lnot).land s[retId]!).land s[retId]!)

/-- State after the level-5 ADRS store `mstore(0x3a0, or(usr_t, <C5>))`
    (statement 24). -/
def treeAfterNode5Adrs (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterSel4 s).setMachineState ((treeAfterSel4 s).toMachineState.mstore
    (UInt256.ofNat 0x3a0)
    ((treeAfterSel4 s)[usrTId]!.lor
      (UInt256.ofNat 1020847100762815390390123822316779470848)))

/-- State after the level-5 node swap store (statement 25). -/
def treeAfterNode5Store (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode5Adrs s).setMachineState ((treeAfterNode5Adrs s).toMachineState.mstore
    ((UInt256.ofNat 0x3c0).xor (treeAfterNode5Adrs s)[usrS4Id]!)
    (treeAfterNode5Adrs s)[usrNode4Id]!)

/-- State after the level-5 sibling swap store (statement 26). -/
def treeAfterSibling5 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterNode5Store s).setMachineState ((treeAfterNode5Store s).toMachineState.mstore
    ((UInt256.ofNat 0x3e0).xor (treeAfterNode5Store s)[usrS4Id]!)
    (treeMaskedCalldataWord (treeAfterNode5Store s)
      ((treeAfterNode5Store s)[treePtrId]!.add (UInt256.ofNat 80))))

/-- The tree-root word the iteration stores at `usr_rootPtr` (computed from the
    state entering the root store). -/
def treeRootWord (s : EvmYul.Yul.State) : UInt256 :=
  ((s.toMachineState.keccak256 (UInt256.ofNat 0x380) (UInt256.ofNat 128)).1).land
    (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot

/-- State after the root keccak (`activeWords` bumped, memory unchanged). -/
def treeAfterRootKeccak (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.setMachineState (s.toMachineState.keccak256 (UInt256.ofNat 0x380)
    (UInt256.ofNat 128)).2

/-- State after `mstore(usr_rootPtr, and(keccak256(0x380, 128), not(0xff…ff)))`. -/
def treeAfterRootStore (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treeAfterRootKeccak s).setMachineState ((treeAfterRootKeccak s).toMachineState.mstore
    (treeAfterRootKeccak s)[rootPtrId]! (treeRootWord s))

/-- The root store statement (27): the keccak value threads state, then the
    `usr_rootPtr` offset is read in the post-keccak state. -/
theorem exec_tree_root_store {n co} (s : EvmYul.Yul.State) :
    exec (n+12) (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Var "usr_rootPtr", treeNodeHashExpr])) co s
      = .ok (treeAfterRootStore s) :=
  exec_mstore_thread (n := n+6)
    (he₂ := eval_masked_keccak (n := n) (UInt256.ofNat 0x380) (UInt256.ofNat 128)
      (UInt256.ofNat 0xffffffffffffffffffffffffffffffff))
    (he₁ := eval_var (n := n+7))

/-- State after the whole level-5 block including the root store. -/
def treeAfterNode5 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  treeAfterRootStore (treeAfterSibling5 s)

/-- **Node level 5 + root store execution.** Body statements 23–27. -/
theorem exec_tree_body_node5 (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+20) (.Block (forsTreeBody.drop 23)) co s
      = exec (n+15) (.Block (forsTreeBody.drop 28)) co (treeAfterNode5 s) := by
  show exec (n+20)
      (.Block (treeSelectorLetStmt "usr_s_4" 1 (.Var "ret")
        :: .ExprStmtCall (.Call (Sum.inl .MSTORE)
             [.Lit (UInt256.ofNat 0x3a0),
              .Call (Sum.inl .OR)
                [.Var "usr_t",
                 .Lit (UInt256.ofNat 1020847100762815390390123822316779470848)]])
        :: treeNodeStoreStmt "usr_s_4" "usr_node_4"
        :: treeSiblingStoreStmt "usr_s_4"
             (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 80)])
        :: .ExprStmtCall (.Call (Sum.inl .MSTORE)
             [.Var "usr_rootPtr", treeNodeHashExpr])
        :: forsTreeBody.drop 28)) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+19) (treeSelectorLetStmt "usr_s_4" 1 (.Var "ret")) co s
      = .ok (treeAfterSel4 s) from
    exec_tree_selector_let (n := n+1) usrS4Id 1
      (hmid := eval_var (n := n+12)))]
  rw [exec_block_cons_ok (h := show
    exec (n+18) (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Lit (UInt256.ofNat 0x3a0),
         .Call (Sum.inl .OR)
           [.Var "usr_t",
            .Lit (UInt256.ofNat 1020847100762815390390123822316779470848)]]))
        co (treeAfterSel4 s)
      = .ok (treeAfterNode5Adrs s) from
    exec_mstore_lit (n := n+12) (he := eval_tree_or_var_lit (n := n+10)))]
  rw [exec_block_cons_ok (h := show
    exec (n+17) (treeNodeStoreStmt "usr_s_4" "usr_node_4") co (treeAfterNode5Adrs s)
      = .ok (treeAfterNode5Store s) from
    exec_tree_node_store (n := n+7) (treeAfterNode5Adrs s) usrS4Id usrNode4Id)]
  rw [exec_block_cons_ok (h := show
    exec (n+16) (treeSiblingStoreStmt "usr_s_4"
        (.Call (Sum.inl .ADD) [.Var "usr_treePtr", .Lit (UInt256.ofNat 80)]))
        co (treeAfterNode5Store s)
      = .ok (treeAfterSibling5 s) from
    exec_tree_sibling_store (n := n+6) usrS4Id
      (hoff := eval_tree_add_var_lit (n := n+2)))]
  rw [exec_block_cons_ok (h := show
    exec (n+15) (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Var "usr_rootPtr", treeNodeHashExpr])) co (treeAfterSibling5 s)
      = .ok (treeAfterNode5 s) from
    exec_tree_root_store (n := n+3) (treeAfterSibling5 s))]

/-! ## One full iteration -/

/-- The state after one complete loop-body iteration. -/
def treeIterState (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  treeAfterNode5 (treeAfterNode4 (treeAfterNode3 (treeAfterNode2 (treeAfterNode1
    (treeAfterLeafHash s)))))

/-- **One full loop-body iteration**: leaf prefix + five node levels + root
    store, generically in fuel — the `hbody` input for `loop_step` (A4). -/
theorem exec_tree_body_iter (n : Nat) (co : Option YulContract)
    (ss : SharedState .Yul) (vs : VarStore) :
    exec (n+43) (.Block forsTreeBody) co (.Ok ss vs)
      = .ok (treeIterState (.Ok ss vs)) := by
  rw [exec_tree_body_leaf_prefix (n+30) co ss vs,
    exec_tree_body_node1 (n+20) co,
    exec_tree_body_node2 (n+15) co,
    exec_tree_body_node3 (n+10) co,
    exec_tree_body_node4 (n+5) co,
    exec_tree_body_node5 n co,
    show forsTreeBody.drop 28 = [] from rfl]
  exact exec_block_nil (n := n+14)

/-- One iteration of an `.Ok` state is `.Ok` (the shape `loop_step`'s `hbody`
    pattern-matches on). -/
theorem treeIterState_ok (ss : SharedState .Yul) (vs : VarStore) :
    ∃ ss' vs', treeIterState (.Ok ss vs) = .Ok ss' vs' := ⟨_, _, rfl⟩

/-! ## The loop condition and the post block -/

/-- The loop condition `lt(usr_t, 25)` evaluates to the comparison word (pure). -/
theorem eval_tree_cond {n co} {s : EvmYul.Yul.State} :
    eval (n+6) forsTreeCond co s = .ok (s, s[usrTId]!.lt (UInt256.ofNat 25)) :=
  eval_binop2 (n := n) (f := UInt256.lt)
    (hprim := primCall_lt (n := n+4) (s := s) s[usrTId]! (UInt256.ofNat 25))
    (he₁ := eval_var (n := n+1)) (he₂ := eval_lit (n := n+3))

/-- Post statement 1: `usr_t := add(usr_t, 1)`. -/
def treePost1 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  s.insert "usr_t" (s[usrTId]!.add (UInt256.ofNat 1))

/-- Post statement 2: `usr_treePtr := add(usr_treePtr, ret_2)`. -/
def treePost2 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treePost1 s).insert "usr_treePtr"
    ((treePost1 s)[treePtrId]!.add (treePost1 s)[ret2Id]!)

/-- Post statement 3: `usr_rootPtr := add(usr_rootPtr, ret)`. -/
def treePost3 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treePost2 s).insert "usr_rootPtr"
    ((treePost2 s)[rootPtrId]!.add (treePost2 s)[retId]!)

/-- Post statement 4: `usr_tLeafBase := add(usr_tLeafBase, ret)`. -/
def treePost4 (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treePost3 s).insert "usr_tLeafBase"
    ((treePost3 s)[tLeafBaseId]!.add (treePost3 s)[retId]!)

/-- State after the whole post block (incl. `usr_dCursor := shr(5, usr_dCursor)`). -/
def treePostState (s : EvmYul.Yul.State) : EvmYul.Yul.State :=
  (treePost4 s).insert "usr_dCursor"
    (UInt256.shiftRight (treePost4 s)[dCursorId]! (UInt256.ofNat 5))

/-- **Post-block execution** — the `hpost` input for `loop_step` (A4). -/
theorem exec_tree_post (n : Nat) (co : Option YulContract)
    (s : EvmYul.Yul.State) :
    exec (n+11) (.Block forsTreePost) co s = .ok (treePostState s) := by
  show exec (n+11)
      (.Block (.Let ["usr_t"] (.some (.Call (Sum.inl .ADD)
            [.Var "usr_t", .Lit (UInt256.ofNat 1)]))
        :: .Let ["usr_treePtr"] (.some (.Call (Sum.inl .ADD)
            [.Var "usr_treePtr", .Var "ret_2"]))
        :: .Let ["usr_rootPtr"] (.some (.Call (Sum.inl .ADD)
            [.Var "usr_rootPtr", .Var "ret"]))
        :: .Let ["usr_tLeafBase"] (.some (.Call (Sum.inl .ADD)
            [.Var "usr_tLeafBase", .Var "ret"]))
        :: .Let ["usr_dCursor"] (.some (.Call (Sum.inl .SHR)
            [.Lit (UInt256.ofNat 5), .Var "usr_dCursor"]))
        :: [])) co s = _
  rw [exec_block_cons_ok (h := show
    exec (n+10) (.Let ["usr_t"] (.some (.Call (Sum.inl .ADD)
        [.Var "usr_t", .Lit (UInt256.ofNat 1)]))) co s
      = .ok (treePost1 s) from
    exec_let_binop (n := n+4)
      (hprim := primCall_add (n := n+8) (s := s) s[usrTId]! (UInt256.ofNat 1))
      (he₁ := eval_var (n := n+5)) (he₂ := eval_lit (n := n+7)))]
  rw [exec_block_cons_ok (h := show
    exec (n+9) (.Let ["usr_treePtr"] (.some (.Call (Sum.inl .ADD)
        [.Var "usr_treePtr", .Var "ret_2"]))) co (treePost1 s)
      = .ok (treePost2 s) from
    exec_let_binop (n := n+3)
      (hprim := primCall_add (n := n+7) (s := treePost1 s)
        (treePost1 s)[treePtrId]! (treePost1 s)[ret2Id]!)
      (he₁ := eval_var (n := n+4)) (he₂ := eval_var (n := n+6)))]
  rw [exec_block_cons_ok (h := show
    exec (n+8) (.Let ["usr_rootPtr"] (.some (.Call (Sum.inl .ADD)
        [.Var "usr_rootPtr", .Var "ret"]))) co (treePost2 s)
      = .ok (treePost3 s) from
    exec_let_binop (n := n+2)
      (hprim := primCall_add (n := n+6) (s := treePost2 s)
        (treePost2 s)[rootPtrId]! (treePost2 s)[retId]!)
      (he₁ := eval_var (n := n+3)) (he₂ := eval_var (n := n+5)))]
  rw [exec_block_cons_ok (h := show
    exec (n+7) (.Let ["usr_tLeafBase"] (.some (.Call (Sum.inl .ADD)
        [.Var "usr_tLeafBase", .Var "ret"]))) co (treePost3 s)
      = .ok (treePost4 s) from
    exec_let_binop (n := n+1)
      (hprim := primCall_add (n := n+5) (s := treePost3 s)
        (treePost3 s)[tLeafBaseId]! (treePost3 s)[retId]!)
      (he₁ := eval_var (n := n+2)) (he₂ := eval_var (n := n+4)))]
  rw [exec_block_cons_ok (h := show
    exec (n+6) (.Let ["usr_dCursor"] (.some (.Call (Sum.inl .SHR)
        [.Lit (UInt256.ofNat 5), .Var "usr_dCursor"]))) co (treePost4 s)
      = .ok (treePostState s) from
    exec_let_binop (n := n)
      (hprim := primCall_shr (n := n+4) (s := treePost4 s)
        (UInt256.ofNat 5) (treePost4 s)[dCursorId]!)
      (he₁ := eval_lit (n := n+1)) (he₂ := eval_var (n := n+3)))]
  exact exec_block_nil (n := n+5)

end NiceTry.Fors.Bridge
