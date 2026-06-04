import EvmYul.Yul.Interpreter
import NiceTry.Fors.Bridge.Interp

/-!
# Builtin (`primCall`) step lemmas — pure stack ops

`primCall` (`EvmYul/Yul/Interpreter.lean`) special-cases the CALL family and routes
every other op to EVMYulLean's shared single-opcode semantics `step`. For the pure
stack ops the contract uses, `step` is `dispatchBinary .Yul f = Yul.execBinOp f`
(resp. `execUnOp`), with `execBinOp f s [a,b] = .ok (s, f a b)`.

Each lemma here reduces `primCall (n+1) s OP args` to its result word, given fully
evaluated literal arguments. Recipe: `unfold primCall; simp [<step OP> = …]`, where
the inner `step` equation is `unfold step; rfl` (the `dbg_trace`/`Id.run do` in
`step` reduce away under `rfl`; blind `simp [step]` instead times out).

Covered: `add sub lt gt slt and or xor shl shr byte eq` (binary) and
`iszero not` (unary) — the arithmetic/logic ops in `forsDispatcher` + `fun_recover`.
Stateful ops (`calldataload`, `mstore`, `keccak256`, `return`/`revert`) thread the
machine state and land in a follow-on file.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

set_option maxHeartbeats 1000000

variable {n : Nat} {s : EvmYul.Yul.State} (a b : UInt256)

/-- Binary builtin: `primCall` of a pure binop on two literals = `f a b`. The
    `step` reduction is supplied inline so `simp` never unfolds `step` itself. -/
theorem primCall_add : primCall (n+1) s .ADD [a, b] = .ok (s, [a.add b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.ADD .none s [a, b] = .ok (s, a.add b) from by
    unfold step; rfl]

theorem primCall_sub : primCall (n+1) s .SUB [a, b] = .ok (s, [a.sub b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.SUB .none s [a, b] = .ok (s, a.sub b) from by
    unfold step; rfl]

theorem primCall_lt : primCall (n+1) s .LT [a, b] = .ok (s, [a.lt b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.LT .none s [a, b] = .ok (s, a.lt b) from by
    unfold step; rfl]

theorem primCall_gt : primCall (n+1) s .GT [a, b] = .ok (s, [a.gt b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.GT .none s [a, b] = .ok (s, a.gt b) from by
    unfold step; rfl]

theorem primCall_slt : primCall (n+1) s .SLT [a, b] = .ok (s, [a.slt b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.SLT .none s [a, b] = .ok (s, a.slt b) from by
    unfold step; rfl]

theorem primCall_and : primCall (n+1) s .AND [a, b] = .ok (s, [a.land b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.AND .none s [a, b] = .ok (s, a.land b) from by
    unfold step; rfl]

theorem primCall_or : primCall (n+1) s .OR [a, b] = .ok (s, [a.lor b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.OR .none s [a, b] = .ok (s, a.lor b) from by
    unfold step; rfl]

theorem primCall_xor : primCall (n+1) s .XOR [a, b] = .ok (s, [a.xor b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.XOR .none s [a, b] = .ok (s, a.xor b) from by
    unfold step; rfl]

/-- `shl(a, b)` shifts `b` left by `a` (EVM operand order; `step` uses `flip`). -/
theorem primCall_shl : primCall (n+1) s .SHL [a, b] = .ok (s, [UInt256.shiftLeft b a]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.SHL .none s [a, b] = .ok (s, UInt256.shiftLeft b a) from by
    unfold step; rfl]

/-- `shr(a, b)` shifts `b` right by `a`. -/
theorem primCall_shr : primCall (n+1) s .SHR [a, b] = .ok (s, [UInt256.shiftRight b a]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.SHR .none s [a, b] = .ok (s, UInt256.shiftRight b a) from by
    unfold step; rfl]

theorem primCall_byte : primCall (n+1) s .BYTE [a, b] = .ok (s, [a.byteAt b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.BYTE .none s [a, b] = .ok (s, a.byteAt b) from by
    unfold step; rfl]

theorem primCall_eq : primCall (n+1) s .EQ [a, b] = .ok (s, [a.eq b]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.EQ .none s [a, b] = .ok (s, a.eq b) from by
    unfold step; rfl]

/-- Unary builtin: `iszero`. -/
theorem primCall_iszero : primCall (n+1) s .ISZERO [a] = .ok (s, [a.isZero]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.ISZERO .none s [a] = .ok (s, a.isZero) from by
    unfold step; rfl]

/-- Unary builtin: bitwise `not`. -/
theorem primCall_not : primCall (n+1) s .NOT [a] = .ok (s, [a.lnot]) := by
  unfold primCall
  simp [show step (τ := .Yul) Operation.NOT .none s [a] = .ok (s, a.lnot) from by
    unfold step; rfl]

end NiceTry.Fors.Bridge
