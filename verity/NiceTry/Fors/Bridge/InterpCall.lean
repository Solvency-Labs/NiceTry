import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp

/-!
# Interpreter step lemmas — user calls & `switch` (WS-1 brick 3)

The dispatcher's control structure: `switch shr(224, calldataload(0)) case … { … }`
and `let ret := fun_recover(…)`. This file reduces both.

* **User-function call** (`exec_let_call` / `exec_exprstmt_call` → `execCall_ok` →
  `call_ok`): a `let v := f(args)` / bare `f(args)` enters `f`'s body. `call_ok`
  fires once the contract is found in the account map (`hfind` — guaranteed by the
  fixed `runForsCalldata`, see `EvmRun.lean`) and the function is looked up (`hlook`).
* **`switch`** (`exec_switch_ok` + `execSwitchCases_*` + `foldr_switch_*`): EVMYulLean
  evaluates the scrutinee, then **eagerly runs every case body** (`execSwitchCases`)
  recording each result, runs the default, and `foldr`-selects the branch whose case
  value equals the scrutinee. The `foldr_switch_*` helpers perform that selection.

Recipe as elsewhere: `conv_lhs => rw [exec/call/execSwitchCases]` then `rw`/`simp`
the concrete sub-results.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 800000

variable {n : Nat} {co : Option YulContract} {s : EvmYul.Yul.State}

/-! ## Entering a user function -/

/-- `let v… := f(args)` — evaluate args, then `execCall` into `f`. -/
theorem exec_let_call {vars fn args} :
    exec (n+1) (.Let vars (.some (.Call (Sum.inr fn) args))) co s
      = execCall n fn vars co (reverse' (evalArgs n args.reverse co s)) := by
  conv_lhs => rw [exec]

/-- bare `f(args)` statement (coarity 0) — evaluate args, then `execCall` with no vars. -/
theorem exec_exprstmt_call {fn args} :
    exec (n+1) (.ExprStmtCall (.Call (Sum.inr fn) args)) co s
      = execCall n fn [] co (reverse' (evalArgs n args.reverse co s)) := by
  conv_lhs => rw [exec]

theorem execCall_ok {fn vars args} :
    execCall (n+1) fn vars co (.ok (s, args)) = multifill' vars (call n args fn co s) := by
  conv_lhs => rw [execCall]

theorem execCall_err {fn vars e} :
    execCall (n+1) fn vars co (.error e) = .error e := by
  conv_lhs => rw [execCall]

/-- `call` into a user function: contract found (`hfind`), function looked up
    (`hlook`), body runs to `s₂`. Returns the restored caller state + the function's
    return values read out of `s₂`. -/
theorem call_ok {args fn yc f s₂}
    (hfind : s.sharedState.accountMap.find? s.executionEnv.codeOwner = some yc)
    (hlook : (co.getD yc.code).functions.lookup fn = some f)
    (hbody : exec n (.Block f.body) co (👌 s.initcall f.params args) = .ok s₂) :
    call (n+1) args (some fn) co s
      = .ok ((s₂.reviveJump.overwrite? s).setStore s, f.rets.map s₂.lookup!) := by
  conv_lhs => rw [call]
  rw [hfind]; simp only [hlook]; rw [hbody]

/-! ## `switch` -/

/-- `switch`, fully resolved: scrutinee `= c`, all case bodies run to `branches`,
    default runs to `s₂`; the result is the `foldr` selection by `c`. -/
theorem exec_switch_ok {cond cases' default' s₁ c branches s₂}
    (hcond : eval n cond co s = .ok (s₁, c))
    (hcases : execSwitchCases n co s₁ cases' = .ok branches)
    (hdef : exec n (.Block default') co s₁ = .ok s₂) :
    exec (n+1) (.Switch cond cases' default') co s
      = List.foldr (fun (vs : EvmYul.Literal × Except Yul.Exception EvmYul.Yul.State) acc =>
                      if vs.1 = c then vs.2 else acc) (.ok s₂) branches := by
  conv_lhs => rw [exec]
  simp only [hcond, hcases, hdef]

theorem execSwitchCases_nil : execSwitchCases n co s [] = .ok [] := by
  conv_lhs => rw [execSwitchCases]

/-- A case body that halts (`return`/`revert` ⇒ `YulHalt`) is recorded as a branch. -/
theorem execSwitchCases_cons_halt {val stmts cases' s₂ v rest}
    (hbody : exec n (.Block stmts) co s = .error (.YulHalt s₂ v))
    (hrest : execSwitchCases n co s cases' = .ok rest) :
    execSwitchCases (n+1) co s ((val, stmts) :: cases')
      = .ok ((val, .error (.YulHalt s₂ v)) :: rest) := by
  conv_lhs => rw [execSwitchCases]
  rw [hbody, hrest]

/-- A case body that completes normally is recorded as a branch. -/
theorem execSwitchCases_cons_ok {val stmts cases' s₂ rest}
    (hbody : exec n (.Block stmts) co s = .ok s₂)
    (hrest : execSwitchCases n co s cases' = .ok rest) :
    execSwitchCases (n+1) co s ((val, stmts) :: cases')
      = .ok ((val, .ok s₂) :: rest) := by
  conv_lhs => rw [execSwitchCases]
  rw [hbody, hrest]

/-! ## `foldr` case selection -/

/-- Matching head case wins (its recorded result is returned). -/
theorem foldr_switch_cons_match {c : EvmYul.Literal}
    {init : Except Yul.Exception EvmYul.Yul.State}
    (vs : EvmYul.Literal × Except Yul.Exception EvmYul.Yul.State)
    (branches : List (EvmYul.Literal × Except Yul.Exception EvmYul.Yul.State))
    (h : vs.1 = c) :
    List.foldr (fun w acc => if w.1 = c then w.2 else acc) init (vs :: branches) = vs.2 := by
  simp [List.foldr_cons, h]

/-- Non-matching head case is skipped. -/
theorem foldr_switch_cons_nomatch {c : EvmYul.Literal}
    {init : Except Yul.Exception EvmYul.Yul.State}
    (vs : EvmYul.Literal × Except Yul.Exception EvmYul.Yul.State)
    (branches : List (EvmYul.Literal × Except Yul.Exception EvmYul.Yul.State))
    (h : vs.1 ≠ c) :
    List.foldr (fun w acc => if w.1 = c then w.2 else acc) init (vs :: branches)
      = List.foldr (fun w acc => if w.1 = c then w.2 else acc) init branches := by
  simp [List.foldr_cons, h]

end NiceTry.Fors.Bridge
