import EvmYul.Yul.Interpreter

/-!
# Interpreter fuel-monotonicity — foundation

**General EVMYulLean property (not FORS-specific) — PR-ready for upstream.**

`evmRun` runs the contract at `fuel = 100000`, but the dispatcher trace is proved at
small fixed fuels (`exec 7/9/13`). Without monotonicity the fragments don't compose
up to the real run. This file lays the verified foundation for the unlock:

    exec n stmt co s ≠ OutOfFuel → exec (n+1) stmt co s = exec n stmt co s   (and analogues)

What's proved here, `sorry`-free:
* the `fuel = 0 = OutOfFuel` base facts for every fuel-matching function;
* `primCall` is **fuel-stable for pure ops** (`unfold primCall; rfl`) — fuel only
  matters in the CALL family, which the pure FORS contract never executes;
* the combined predicate `MonoAt` and its **base case** `monoAt_zero`;
* `exec_block_cons_mono` — the **validated recursive mechanic** (the hard case):
  `by_cases` on the head result, contradiction via `rw [exec, hhead]`, conv-target
  the LHS, lift the head with the IH, recurse on the tail with the IH. Every other
  recursive case (`If`/`Switch`/`Let`-call/`For`→`loop`/`call`/…) follows this same
  template.

## Remaining (the focused completion — see PICKUP.md)
The full `∀ n, MonoAt n` by induction on `n`: discharge every case of every mutual
function using the template above. `primCall`'s pure ops are `rfl`; only the CALL
family needs `callDispatcher`-mono (skippable for the pure contract). The mechanic
being proven here means this is a mechanical (if large) grind, not a research risk.
-/

namespace EvmYul.Yul.FuelMono

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 2000000

/-- The out-of-fuel result. -/
abbrev OOF {α} : Except Yul.Exception α := .error .OutOfFuel

/-! ### `fuel = 0` ⇒ `OutOfFuel` (the functions that match fuel first) -/

theorem exec_zero (stmt co s) : exec 0 stmt co s = OOF := by rw [exec]
theorem eval_zero (e co s) : eval 0 e co s = OOF := by rw [eval]
theorem evalArgs_zero (a co s) : evalArgs 0 a co s = OOF := by rw [evalArgs]
theorem loop_zero (c p b co s) : loop 0 c p b co s = OOF := by rw [loop]
theorem call_zero (a f co s) : call 0 a f co s = OOF := by rw [call]
/-- `execSwitchCases` matches the case-list first: `[]` is fuel-independent, a
    non-empty list is `OutOfFuel` at fuel `0`. -/
theorem switch_zero_cons (co s v stmts cs) :
    execSwitchCases 0 co s ((v, stmts) :: cs) = OOF := by rw [execSwitchCases]
theorem switch_nil (n co s) : execSwitchCases n co s [] = .ok [] := by rw [execSwitchCases]

/-! ### `primCall` is fuel-stable for pure ops (fuel only matters in the CALL family) -/

theorem primCall_add_stable (n s args) :
    primCall (n+1) s .ADD args = primCall (n+2) s .ADD args := by unfold primCall; rfl
theorem primCall_mstore_stable (n s args) :
    primCall (n+1) s .MSTORE args = primCall (n+2) s .MSTORE args := by unfold primCall; rfl
theorem primCall_keccak_stable (n s args) :
    primCall (n+1) s .KECCAK256 args = primCall (n+2) s .KECCAK256 args := by unfold primCall; rfl

/-! ### The combined monotonicity predicate + base case -/

/-- Monotonicity holds simultaneously for the core fuel-recursive functions at
    fuel `n` (the combined induction's invariant). -/
structure MonoAt (n : Nat) : Prop where
  exec : ∀ stmt co s, exec n stmt co s ≠ OOF → exec (n+1) stmt co s = exec n stmt co s
  eval : ∀ e co s, eval n e co s ≠ OOF → eval (n+1) e co s = eval n e co s
  evalArgs : ∀ a co s, evalArgs n a co s ≠ OOF → evalArgs (n+1) a co s = evalArgs n a co s
  loop : ∀ c p b co s, loop n c p b co s ≠ OOF → loop (n+1) c p b co s = loop n c p b co s
  switch : ∀ co s cs, execSwitchCases n co s cs ≠ OOF →
            execSwitchCases (n+1) co s cs = execSwitchCases n co s cs
  call : ∀ a f co s, call n a f co s ≠ OOF → call (n+1) a f co s = call n a f co s

theorem monoAt_zero : MonoAt 0 where
  exec := fun _ _ _ h => absurd (exec_zero ..) h
  eval := fun _ _ _ h => absurd (eval_zero ..) h
  evalArgs := fun _ _ _ h => absurd (evalArgs_zero ..) h
  loop := fun _ _ _ _ _ h => absurd (loop_zero ..) h
  switch := fun _ _ cs h => by
    cases cs with
    | nil => rw [switch_nil, switch_nil]
    | cons c cs' => cases c with | mk v stmts => exact absurd (switch_zero_cons ..) h
  call := fun _ _ _ _ h => absurd (call_zero ..) h

/-! ### The recursive mechanic, validated on the `Block`-cons case

This is the template every recursive case follows in the full induction: split on
whether the first sub-result is `OutOfFuel` (if so, the whole is `OutOfFuel`,
contradicting the hypothesis), otherwise lift each sub-result with the IH. -/

theorem exec_block_cons_mono (n co)
    (ih : ∀ (st : Stmt) (s : EvmYul.Yul.State),
            exec n st co s ≠ OOF → exec (n+1) st co s = exec n st co s)
    (st sts s) (hne : exec (n+1) (.Block (st :: sts)) co s ≠ OOF) :
    exec (n+2) (.Block (st :: sts)) co s = exec (n+1) (.Block (st :: sts)) co s := by
  by_cases hhead : exec n st co s = OOF
  · exfalso; apply hne; rw [exec, hhead]
  · conv_lhs => rw [exec]
    conv_rhs => rw [exec]
    rw [ih st s hhead]
    cases hst : exec n st co s with
    | error e => rfl
    | ok s₁ =>
        have htail : exec n (.Block sts) co s₁ ≠ OOF := by
          intro hc; apply hne; rw [exec, hst]; simpa using hc
        exact ih (.Block sts) s₁ htail

end EvmYul.Yul.FuelMono
