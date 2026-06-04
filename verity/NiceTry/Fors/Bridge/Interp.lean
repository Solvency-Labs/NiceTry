import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

/-!
# Interpreter step lemmas (WS-1/2/3 foundation)

EVMYulLean's `exec` is a fuel-recursive function inside a 7-way `mutual` block
(`EvmYul/Yul/Interpreter.lean`). It is **reducible by symbolic unfolding** (not
`partial`), but `#eval`/`native_decide` cannot run it (opaque FFI keccak/memory —
see `EvmFfiSpec.lean`), so all execution reasoning is symbolic.

This file gives the reusable one-step reductions of `exec` for control flow. Each
is stated in **case-split form keyed on the sub-result** (`eval … = .ok/.error`)
rather than with a `match` in the conclusion — because the def's compiled `match`
does not definitionally equal a freshly-written one, but reduces fine once the
scrutinee is a concrete `.ok`/`.error`. This case-split form is also exactly what
a forward symbolic execution has in hand at each step.

Proof recipe (used throughout): `conv_lhs => rw [exec]` unfolds one fuel layer;
`rw [h]` substitutes the concrete sub-result so the `match` reduces.

These cover `Block` / `If` / `Leave` / `Break` / `Continue` / out-of-fuel. The
expression/`Switch`/`Call`/`For` steps (needed to reach `h_len`/`h_guard` and the
tree loop) build on top and land in follow-on files.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

variable {n : Nat} {co : Option YulContract} {s : EvmYul.Yul.State}

/-- Fuel exhausted: any statement fails with `OutOfFuel`. -/
@[simp] theorem exec_zero_fuel (stmt : Stmt) :
    exec 0 stmt co s = .error .OutOfFuel := by
  conv_lhs => rw [exec]

/-- Empty block is a no-op. -/
@[simp] theorem exec_block_nil :
    exec (n+1) (.Block []) co s = .ok s := by
  conv_lhs => rw [exec]

/-- Sequencing, success branch: run the head, then continue with the tail on the
    resulting state. -/
theorem exec_block_cons_ok {st sts s₁}
    (h : exec n st co s = .ok s₁) :
    exec (n+1) (.Block (st :: sts)) co s = exec n (.Block sts) co s₁ := by
  conv_lhs => rw [exec]
  rw [h]

/-- Sequencing, error branch: a failing head short-circuits the block. -/
theorem exec_block_cons_err {st sts e}
    (h : exec n st co s = .error e) :
    exec (n+1) (.Block (st :: sts)) co s = .error e := by
  conv_lhs => rw [exec]
  rw [h]

/-- `leave` returns from the current function (sets the `Leave` checkpoint). -/
@[simp] theorem exec_leave :
    exec (n+1) .Leave co s = .ok (🚪 s) := by
  conv_lhs => rw [exec]

/-- `break` out of the enclosing loop. -/
@[simp] theorem exec_break :
    exec (n+1) .Break co s = .ok (💔 s) := by
  conv_lhs => rw [exec]

/-- `continue` to the next loop iteration. -/
@[simp] theorem exec_continue :
    exec (n+1) .Continue co s = .ok (🔁 s) := by
  conv_lhs => rw [exec]

/-! ## Expression evaluation — base cases

Literals and variables are one-step. Builtin calls (`.Call (.inl prim) args`) route
through `evalArgs` + `primCall` and get a per-builtin lemma in the follow-on file
(`mstore`/`calldataload`/`eq`/`shr`/`add`/… each need their `primCall` semantics). -/

/-- A literal evaluates to itself, state unchanged. -/
@[simp] theorem eval_lit {val} :
    eval (n+1) (.Lit val) co s = .ok (s, val) := by
  conv_lhs => rw [eval]

/-- A variable reads its binding from the state. -/
@[simp] theorem eval_var {id} :
    eval (n+1) (.Var id) co s = .ok (s, s[id]!) := by
  conv_lhs => rw [eval]

/-- Argument evaluation, empty list. -/
@[simp] theorem evalArgs_nil :
    evalArgs (n+1) [] co s = .ok (s, []) := by
  conv_lhs => rw [evalArgs]

/-! ## Control flow (continued) -/

/-- `if`, error branch: a failing condition short-circuits. -/
theorem exec_if_err {cond body e}
    (h : eval n cond co s = .error e) :
    exec (n+1) (.If cond body) co s = .error e := by
  conv_lhs => rw [exec]
  rw [h]

/-- `if`, taken branch: condition evaluates to a non-zero word. -/
theorem exec_if_true {cond body s' c}
    (h : eval n cond co s = .ok (s', c)) (hc : c ≠ ⟨0⟩) :
    exec (n+1) (.If cond body) co s = exec n (.Block body) co s' := by
  conv_lhs => rw [exec]
  rw [h]; simp [hc]

/-- `if`, skipped branch: condition evaluates to zero, state passes through. -/
theorem exec_if_false {cond body s'}
    (h : eval n cond co s = .ok (s', ⟨0⟩)) :
    exec (n+1) (.If cond body) co s = .ok s' := by
  conv_lhs => rw [exec]
  rw [h]; simp

end NiceTry.Fors.Bridge
