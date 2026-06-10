import EvmYul.Yul.Interpreter

/-!
# Interpreter fuel-monotonicity — foundation

**General EVMYulLean property (not FORS-specific) — PR-ready for upstream.**

`evmRun` runs the contract at `fuel = 100000`, but the dispatcher trace is proved at
small fixed fuels (`exec 7/9/13`). Without monotonicity the fragments don't compose
up to the real run. This file builds the verified foundation for the unlock:

    exec n stmt co s ≠ OutOfFuel → exec (n+1) stmt co s = exec n stmt co s   (and analogues)

What's proved here, `sorry`-free, axiom-clean:
* the `fuel = 0 = OutOfFuel` base facts;
* `primCall` is **fuel-stable for pure ops** (`unfold; rfl`) — fuel only matters in the
  CALL family, which the pure FORS contract never executes;
* the **combined invariant** `MonoAt` over *all* mutual functions, and its **base case**
  `monoAt_zero`;
* `exec_block_cons_mono` — the **validated recursive mechanic** (the hard case);
  every recursive case of the inductive step follows this template.

## Remaining (the focused completion — see PICKUP.md)
`monoAt_succ : MonoAt n → MonoAt (n+1)` (each conjunct via the template / the wrappers
from the core functions), then `fuel_mono : ∀ n, MonoAt n` by `Nat.rec`. The
conjuncts are **individually committable** `*_mono_step` lemmas (each takes `MonoAt n`
as a hypothesis), so the completion is incremental, not all-or-nothing.
-/

namespace EvmYul.Yul.FuelMono

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 2000000

/-- The out-of-fuel result. -/
abbrev OOF {α} : Except Yul.Exception α := .error .OutOfFuel

/-! ### `fuel = 0` base facts -/

theorem exec_zero (st co s) : exec 0 st co s = OOF := by rw [exec]
theorem eval_zero (e co s) : eval 0 e co s = OOF := by rw [eval]
theorem evalArgs_zero (a co s) : evalArgs 0 a co s = OOF := by rw [evalArgs]
theorem loop_zero (c p b co s) : loop 0 c p b co s = OOF := by rw [loop]
theorem call_zero (a f co s) : call 0 a f co s = OOF := by rw [call]
theorem callDispatcher_zero (co s) : callDispatcher 0 co s = OOF := by rw [callDispatcher]
theorem primCall_zero (s p a) : primCall 0 s p a = OOF := by unfold primCall; rfl
theorem switch_zero_cons (co s v stmts cs) :
    execSwitchCases 0 co s ((v, stmts) :: cs) = OOF := by rw [execSwitchCases]
theorem switch_nil (n co s) : execSwitchCases n co s [] = .ok [] := by rw [execSwitchCases]

/-! ### `primCall` fuel-stability for pure ops (fuel only matters in the CALL family) -/

theorem primCall_add_stable (n s args) :
    primCall (n+1) s .ADD args = primCall (n+2) s .ADD args := by unfold primCall; rfl
theorem primCall_mstore_stable (n s args) :
    primCall (n+1) s .MSTORE args = primCall (n+2) s .MSTORE args := by unfold primCall; rfl
theorem primCall_keccak_stable (n s args) :
    primCall (n+1) s .KECCAK256 args = primCall (n+2) s .KECCAK256 args := by unfold primCall; rfl

/-! ### The combined monotonicity invariant (all mutual functions) -/

structure MonoAt (n : Nat) : Prop where
  exec : ∀ st co s, exec n st co s ≠ OOF → exec (n+1) st co s = exec n st co s
  eval : ∀ e co s, eval n e co s ≠ OOF → eval (n+1) e co s = eval n e co s
  evalArgs : ∀ a co s, evalArgs n a co s ≠ OOF → evalArgs (n+1) a co s = evalArgs n a co s
  evalTail : ∀ a co x, evalTail n a co x ≠ OOF → evalTail (n+1) a co x = evalTail n a co x
  evalPrimCall : ∀ p x, evalPrimCall n p x ≠ OOF → evalPrimCall (n+1) p x = evalPrimCall n p x
  evalCall : ∀ f co x, evalCall n f co x ≠ OOF → evalCall (n+1) f co x = evalCall n f co x
  execPrimCall : ∀ p vs x, execPrimCall n p vs x ≠ OOF → execPrimCall (n+1) p vs x = execPrimCall n p vs x
  execCall : ∀ f vs co x, execCall n f vs co x ≠ OOF → execCall (n+1) f vs co x = execCall n f vs co x
  call : ∀ a f co s, call n a f co s ≠ OOF → call (n+1) a f co s = call n a f co s
  callDispatcher : ∀ co s, callDispatcher n co s ≠ OOF → callDispatcher (n+1) co s = callDispatcher n co s
  switch : ∀ co s cs, execSwitchCases n co s cs ≠ OOF →
            execSwitchCases (n+1) co s cs = execSwitchCases n co s cs
  loop : ∀ c p b co s, loop n c p b co s ≠ OOF → loop (n+1) c p b co s = loop n c p b co s
  primCall : ∀ s p a, primCall n s p a ≠ OOF → primCall (n+1) s p a = primCall n s p a

/-! ### Base case -/

theorem monoAt_zero : MonoAt 0 where
  exec := fun _ _ _ h => absurd (exec_zero ..) h
  eval := fun _ _ _ h => absurd (eval_zero ..) h
  evalArgs := fun _ _ _ h => absurd (evalArgs_zero ..) h
  evalTail := fun a co x h => by
    cases x with
    | error e => rw [evalTail, evalTail]
    | ok v => exact absurd (by rw [evalTail]) h
  evalPrimCall := fun p x h => by
    cases x with
    | error e => rw [evalPrimCall, evalPrimCall]
    | ok v => exact absurd (by rw [evalPrimCall]; rw [primCall_zero]; rfl) h
  evalCall := fun f co x h => by
    cases x with
    | error e => rw [evalCall, evalCall]
    | ok v => exact absurd (by rw [evalCall]) h
  execPrimCall := fun p vs x h => by
    cases x with
    | error e => rw [execPrimCall, execPrimCall]
    | ok v => exact absurd (by rw [execPrimCall]; rw [primCall_zero]; rfl) h
  execCall := fun f vs co x h => by
    cases x with
    | error e => rw [execCall, execCall]
    | ok v => exact absurd (by rw [execCall]) h
  call := fun _ _ _ _ h => absurd (call_zero ..) h
  callDispatcher := fun _ _ h => absurd (callDispatcher_zero ..) h
  switch := fun _ _ cs h => by
    cases cs with
    | nil => rw [switch_nil, switch_nil]
    | cons c cs' => cases c with | mk v stmts => exact absurd (switch_zero_cons ..) h
  loop := fun _ _ _ _ _ h => absurd (loop_zero ..) h
  primCall := fun _ _ _ h => absurd (primCall_zero ..) h

/-! ### The recursive mechanic, validated on the `Block`-cons case

The template every recursive case follows in `monoAt_succ`: split on whether the
first sub-result is `OutOfFuel` (if so the whole is, contradicting the hypothesis),
otherwise lift each sub-result with the IH. -/

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

/-! ### Inductive step — the wrapper conjuncts

`evalPrimCall`/`execPrimCall` call `primCall` at the *same* fuel, so they take the
same-level `primCall` step `hpc`; `evalCall`/`execCall`/`evalTail` decrement fuel and
use the IH (`h.call`/`h.evalArgs`). All preserve `OutOfFuel`. -/

theorem head'_oof : head' (OOF : Except Yul.Exception (EvmYul.Yul.State × List Literal)) = OOF := rfl
theorem multifill'_oof (vs) :
    multifill' vs (OOF : Except Yul.Exception (EvmYul.Yul.State × List Literal)) = OOF := rfl
theorem cons'_oof (a : Literal) :
    cons' a (OOF : Except Yul.Exception (EvmYul.Yul.State × List Literal)) = OOF := rfl

theorem evalPrimCall_mono_step {n}
    (hpc : ∀ s p a, primCall (n+1) s p a ≠ OOF → primCall (n+2) s p a = primCall (n+1) s p a)
    (p x) (hne : evalPrimCall (n+1) p x ≠ OOF) :
    evalPrimCall (n+2) p x = evalPrimCall (n+1) p x := by
  cases x with
  | error e => rw [evalPrimCall, evalPrimCall]
  | ok v =>
    obtain ⟨s, args⟩ := v
    have hp : primCall (n+1) s p args ≠ OOF := fun hc => hne (by rw [evalPrimCall, hc, head'_oof])
    rw [evalPrimCall, evalPrimCall, hpc s p args hp]

theorem execPrimCall_mono_step {n}
    (hpc : ∀ s p a, primCall (n+1) s p a ≠ OOF → primCall (n+2) s p a = primCall (n+1) s p a)
    (p vs x) (hne : execPrimCall (n+1) p vs x ≠ OOF) :
    execPrimCall (n+2) p vs x = execPrimCall (n+1) p vs x := by
  cases x with
  | error e => rw [execPrimCall, execPrimCall]
  | ok v =>
    obtain ⟨s, args⟩ := v
    have hp : primCall (n+1) s p args ≠ OOF := fun hc => hne (by rw [execPrimCall, hc, multifill'_oof])
    rw [execPrimCall, execPrimCall, hpc s p args hp]

theorem evalCall_mono_step {n} (h : MonoAt n) (f co x) (hne : evalCall (n+1) f co x ≠ OOF) :
    evalCall (n+2) f co x = evalCall (n+1) f co x := by
  cases x with
  | error e => rw [evalCall, evalCall]
  | ok v =>
    obtain ⟨s, args⟩ := v
    have hc : call n args f co s ≠ OOF := fun hcc => hne (by rw [evalCall, hcc, head'_oof])
    rw [evalCall, evalCall, h.call args f co s hc]

theorem execCall_mono_step {n} (h : MonoAt n) (f vs co x) (hne : execCall (n+1) f vs co x ≠ OOF) :
    execCall (n+2) f vs co x = execCall (n+1) f vs co x := by
  cases x with
  | error e => rw [execCall, execCall]
  | ok v =>
    obtain ⟨s, args⟩ := v
    have hc : call n args f co s ≠ OOF := fun hcc => hne (by rw [execCall, hcc, multifill'_oof])
    rw [execCall, execCall, h.call args f co s hc]

theorem evalTail_mono_step {n} (h : MonoAt n) (a co x) (hne : evalTail (n+1) a co x ≠ OOF) :
    evalTail (n+2) a co x = evalTail (n+1) a co x := by
  cases x with
  | error e => rw [evalTail, evalTail]
  | ok v =>
    obtain ⟨s, arg⟩ := v
    have ha : evalArgs n a co s ≠ OOF := fun haa => hne (by rw [evalTail, haa, cons'_oof])
    rw [evalTail, evalTail, h.evalArgs a co s ha]

end EvmYul.Yul.FuelMono
