import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp

/-!
# `for`-loop step lemmas — foundation for the FORS tree-loop induction

`fun_recover`'s 25-tree climb is a Yul `for { } lt(usr_t,25) { post } { body }`,
which EVMYulLean runs via `loop` (`Interpreter.lean:621`). `loop` evaluates the
condition on `👌s`, exits to `s₁✏️⟦s⟧?` if it's `0`, else runs `body`, then `post`
on `🧟s₂`, then re-execs the `.For` and overwrites. (The `s₂` checkpoint match —
`OutOfFuel`/`Break`/`Leave`/`Continue` — degenerates to the `_` arm for the
straight-line FORS body, which is a normal `.Ok` state.)

These one-step reductions are the induction's per-iteration scaffolding:
* `exec_for` — `.For` dispatches to `loop`;
* `loop_exit` — condition `0` ⇒ terminate;
* `loop_step` — one iteration (cond ≠ 0, body to a normal `.Ok`): run body, post,
  recurse via `.For`;
* `loop_cond_err` — condition error short-circuits.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 1000000

variable {n : Nat} {cond : Expr} {post body : List Stmt} {co : Option YulContract}
  {s : EvmYul.Yul.State}

/-- A `for` statement dispatches to `loop` (one fuel layer). -/
theorem exec_for : exec (n+1) (.For cond post body) co s = loop n cond post body co s := by
  conv_lhs => rw [exec]

/-- Loop terminates when the condition evaluates to `0`. -/
theorem loop_exit {s₁} (h : eval n cond co (👌 s) = .ok (s₁, ⟨0⟩)) :
    loop (n+2) cond post body co s = .ok (s₁✏️⟦s⟧?) := by
  conv_lhs => rw [loop]
  rw [h]; simp

/-- A failing condition short-circuits the loop. -/
theorem loop_cond_err {e} (h : eval n cond co (👌 s) = .error e) :
    loop (n+2) cond post body co s = .error e := by
  conv_lhs => rw [loop]
  rw [h]

/-- One loop iteration: condition non-zero, `body` runs to a normal `.Ok` state,
    then `post` runs and the loop re-executes (via `.For`). -/
theorem loop_step {s₁ x ss₂ vs₂ s₃ s₅}
    (hcond : eval n cond co (👌 s) = .ok (s₁, x)) (hx : x ≠ ⟨0⟩)
    (hbody : exec n (.Block body) co s₁ = .ok (.Ok ss₂ vs₂))
    (hpost : exec n (.Block post) co (🧟 (.Ok ss₂ vs₂)) = .ok s₃)
    (hfor : exec n (.For cond post body) co (s₃✏️⟦s⟧?) = .ok s₅) :
    loop (n+2) cond post body co s = .ok (s₅✏️⟦s⟧?) := by
  rw [loop]
  simp only [hcond, hbody, hpost, hfor, if_neg hx]

end NiceTry.Fors.Bridge
