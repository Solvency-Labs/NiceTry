import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp
import NiceTry.Fors.Bridge.InterpOps
import NiceTry.Fors.Bridge.InterpState

/-!
# Expression evaluation — argument threading & builtin-call composition (WS-1 brick 1)

`eval` of a builtin call `OP(e₁, …)` evaluates the arguments (in reverse, via
`evalArgs`/`evalTail`/`cons'`), flips them back (`reverse'`), and applies the op
(`evalPrimCall` → `head' (primCall …)`). This file gives:

* one-step lemmas for the argument plumbing (`evalArgs_cons_ok`, `evalTail_cons_ok`,
  `eval_call_prim`);
* the **composition lemmas** `eval_unop1` / `eval_binop2`: given each argument's
  evaluation (state-preserving) and the op's `primCall` result, the whole call
  evaluates to the op applied to the argument values;
* `eval_nullop0`, for zero-argument builtins (`calldatasize`, `callvalue`);
* the state-threading variants `eval_unop1_thread` / `eval_binop2_thread`, for
  expression opcodes such as `mload` and `keccak256` that update machine state.

These turn the leaf `primCall` lemmas in `InterpOps.lean` into evaluation of the
nested expressions the contract actually uses (e.g. `and(calldataload(x), not(C))`).
The arguments may themselves be `eval_binop2`/`eval_unop1` results, so nesting
composes. Fuel: each nesting level costs a fixed offset (`+2` per argument depth),
discharged by instantiating the parametric `n`.

Most expression operands are pure reads (`calldataload`, arithmetic), so the
state-preserving lemmas keep common traces compact. The thread variants handle
the non-mutating arguments to stateful expression opcodes without hiding the
machine-state update.
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

/-- **Nullary builtin call.** Given `OP()` yields one result word, the call
    expression evaluates to that word. Used for `calldatasize()` / `callvalue()`. -/
theorem eval_nullop0 {n co} {s s' : EvmYul.Yul.State} {out : UInt256} {OP : PrimOp}
    (hprim : primCall (n+1) s OP [] = .ok (s', [out])) :
    eval (n+2) (.Call (Sum.inl OP) []) co s = .ok (s', out) := by
  rw [eval_call_prim]
  show evalPrimCall (n+1) OP (reverse' (evalArgs (n+1) [] co s)) = _
  rw [evalArgs_nil]
  simp only [reverse', List.reverse_nil, evalPrimCall, hprim, head', List.head!]

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

/-- **Unary builtin call, state-threading form.** The argument evaluates first,
    then the primitive call runs in the argument's resulting state. This covers
    `mload(a)`, whose result includes an updated active-word count. -/
theorem eval_unop1_thread {n co} {s₀ s₁ s₂ : EvmYul.Yul.State} {e : Expr}
    {v out : UInt256} {OP : PrimOp}
    (hprim : primCall (n+3) s₁ OP [v] = .ok (s₂, [out]))
    (he : eval (n+2) e co s₀ = .ok (s₁, v)) :
    eval (n+4) (.Call (Sum.inl OP) [e]) co s₀ = .ok (s₂, out) := by
  rw [eval_call_prim]
  show evalPrimCall (n+3) OP (reverse' (evalArgs (n+3) [e] co s₀)) = _
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

/-- **Binary builtin call, state-threading form.** The interpreter evaluates
    `e₂` first, then `e₁`, reverses the collected values, and runs the primitive
    in the resulting state. This is the form needed for stateful expression
    opcodes such as `keccak256(a, b)`. -/
theorem eval_binop2_thread {n co} {s₀ s₁ s₂ s₃ : EvmYul.Yul.State}
    {e₁ e₂ : Expr} {v₁ v₂ out : UInt256} {OP : PrimOp}
    (hprim : primCall (n+5) s₁ OP [v₁, v₂] = .ok (s₃, [out]))
    (he₁ : eval (n+2) e₁ co s₂ = .ok (s₁, v₁))
    (he₂ : eval (n+4) e₂ co s₀ = .ok (s₂, v₂)) :
    eval (n+6) (.Call (Sum.inl OP) [e₁, e₂]) co s₀ = .ok (s₃, out) := by
  rw [eval_call_prim]
  show evalPrimCall (n+5) OP (reverse' (evalArgs (n+5) [e₂, e₁] co s₀)) = _
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

/-- Regression / usage: nullary evaluation for `calldatasize()`. -/
example (s : EvmYul.Yul.State) (co : Option YulContract) :
    eval 2 (.Call (Sum.inl .CALLDATASIZE) []) co s
      = .ok (s, UInt256.ofNat s.executionEnv.calldata.size) :=
  eval_nullop0 (n := 0) (primCall_calldatasize (n := 0) s)

/-- Regression / usage: nullary evaluation for `callvalue()`. -/
example (s : EvmYul.Yul.State) (co : Option YulContract) :
    eval 2 (.Call (Sum.inl .CALLVALUE) []) co s
      = .ok (s, s.executionEnv.weiValue) :=
  eval_nullop0 (n := 0) (primCall_callvalue (n := 0) s)

/-- Regression / usage: state-threading unary evaluation for `mload(a)`. -/
example (s : EvmYul.Yul.State) (a : UInt256) (co : Option YulContract) :
    eval 4 (.Call (Sum.inl .MLOAD) [.Lit a]) co s
      = let (v, mState') := s.toMachineState.mload a
        .ok (s.setMachineState mState', v) :=
  eval_unop1_thread (n := 0) (primCall_mload s a) eval_lit

/-- Regression / usage: state-threading binary evaluation for `keccak256(a, b)`. -/
example (s : EvmYul.Yul.State) (a b : UInt256) (co : Option YulContract) :
    eval 6 (.Call (Sum.inl .KECCAK256) [.Lit a, .Lit b]) co s
      = .ok (s.setMachineState (s.toMachineState.keccak256 a b).2,
             (s.toMachineState.keccak256 a b).1) :=
  eval_binop2_thread (n := 0) (primCall_keccak256 s a b) eval_lit eval_lit

end NiceTry.Fors.Bridge
