import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp
import NiceTry.Fors.Bridge.InterpOps

/-!
# Expression evaluation — argument threading & builtin-call composition (WS-1 brick 1)

`eval` of a builtin call `OP(e₁, …)` evaluates the arguments (in reverse, via
`evalArgs`/`evalTail`/`cons'`), flips them back (`reverse'`), and applies the op
(`evalPrimCall` → `head' (primCall …)`). This file gives:

* one-step lemmas for the argument plumbing (`evalArgs_cons_ok`, `evalTail_cons_ok`,
  `eval_call_prim`);
* the **composition lemmas** `eval_unop1` / `eval_binop2`: given each argument's
  evaluation (state-preserving) and the op's `primCall` result, the whole call
  evaluates to the op applied to the argument values.

These turn the leaf `primCall` lemmas in `InterpOps.lean` into evaluation of the
nested expressions the contract actually uses (e.g. `and(calldataload(x), not(C))`).
The arguments may themselves be `eval_binop2`/`eval_unop1` results, so nesting
composes. Fuel: each nesting level costs a fixed offset (`+2` per argument depth),
discharged by instantiating the parametric `n`.

State-preserving form: the contract's expression operands are pure reads
(`calldataload`, arithmetic, `keccak256`), so `eval` returns the *same* `State`.
That keeps the threading first-order; a state-changing variant can be added if a
future operand mutates state mid-expression (none currently do).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 1000000

/-- `evalArgs` head step: evaluate the first argument, continue with `evalTail`. -/
theorem evalArgs_cons_ok {n arg args co s s' v}
    (h : eval n arg co s = .ok (s', v)) :
    evalArgs (n+1) (arg :: args) co s = evalTail n args co (.ok (s', v)) := by
  conv_lhs => rw [evalArgs]; rw [h]

/-- `evalTail` success step: prepend the just-evaluated value, recurse on the rest. -/
theorem evalTail_cons_ok {n args co s v} :
    evalTail (n+1) args co (.ok (s, v)) = cons' v (evalArgs n args co s) := by
  conv_lhs => rw [evalTail]

/-- One-step unfold of a primitive (builtin) call expression. -/
theorem eval_call_prim {n prim args co s} :
    eval (n+1) (.Call (Sum.inl prim) args) co s
      = evalPrimCall n prim (reverse' (evalArgs n args.reverse co s)) := by
  conv_lhs => rw [eval]

/-- **Unary builtin call.** Given the argument evaluates to `v` (state-preserving)
    and `OP` on `[v]` yields `[f v]`, the call evaluates to `f v`. -/
theorem eval_unop1 {n co} {s : EvmYul.Yul.State} {e : Expr} {v : UInt256}
    {OP : PrimOp} {f : UInt256 → UInt256}
    (hprim : primCall (n+3) s OP [v] = .ok (s, [f v]))
    (he : eval (n+2) e co s = .ok (s, v)) :
    eval (n+4) (.Call (Sum.inl OP) [e]) co s = .ok (s, f v) := by
  rw [eval_call_prim]
  show evalPrimCall (n+3) OP (reverse' (evalArgs (n+3) [e] co s)) = _
  rw [evalArgs_cons_ok he, evalTail_cons_ok, evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    evalPrimCall, hprim, head', List.head!]

/-- **Binary builtin call.** Given each argument evaluates (state-preserving) and
    `OP` on `[v₁, v₂]` yields `[f v₁ v₂]`, the call evaluates to `f v₁ v₂`. Note the
    second operand `e₂` is evaluated first (the interpreter reverses args), hence
    its higher fuel offset; for pure operands the order is observationally inert. -/
theorem eval_binop2 {n co} {s : EvmYul.Yul.State} {e₁ e₂ : Expr} {v₁ v₂ : UInt256}
    {OP : PrimOp} {f : UInt256 → UInt256 → UInt256}
    (hprim : primCall (n+5) s OP [v₁, v₂] = .ok (s, [f v₁ v₂]))
    (he₁ : eval (n+2) e₁ co s = .ok (s, v₁))
    (he₂ : eval (n+4) e₂ co s = .ok (s, v₂)) :
    eval (n+6) (.Call (Sum.inl OP) [e₁, e₂]) co s = .ok (s, f v₁ v₂) := by
  rw [eval_call_prim]
  show evalPrimCall (n+5) OP (reverse' (evalArgs (n+5) [e₂, e₁] co s)) = _
  rw [evalArgs_cons_ok he₂, evalTail_cons_ok, evalArgs_cons_ok he₁, evalTail_cons_ok, evalArgs_nil]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, evalPrimCall, hprim, head', List.head!]

/-- Regression / usage: a nested pure expression `and(a, not(b))` evaluates
    compositionally via `eval_binop2 ∘ eval_unop1 ∘ eval_lit` and the `InterpOps`
    leaves. Demonstrates that nesting composes by instantiating the fuel offset. -/
example (s : EvmYul.Yul.State) (a b : UInt256) (co : Option YulContract) :
    eval 6 (.Call (Sum.inl .AND) [.Lit a, .Call (Sum.inl .NOT) [.Lit b]]) co s
      = .ok (s, a.land b.lnot) :=
  eval_binop2 (n := 0) (primCall_and a b.lnot) eval_lit
    (eval_unop1 (n := 0) (primCall_not b) eval_lit)

end NiceTry.Fors.Bridge
