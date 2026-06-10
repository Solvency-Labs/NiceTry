import NiceTry.Fors.Bridge.InterpEval
import NiceTry.Fors.Bridge.InterpState
import NiceTry.Fors.Bridge.InterpKeccak

/-!
# Masked-keccak evaluation — the eval core for every `fun_recover` hash

Every hash in `fun_recover` is `and(keccak256(off, len), not(0xff…ff))`. This file
assembles the interpreter eval-chain for that expression once, reusably:

* `eval_keccak` — `keccak256(off, len)` evaluates to `(MachineState.keccak256 off len).1`
  in the post-keccak state (keccak bumps `activeWords`, not memory; see
  `keccak256_memory`);
* `eval_not_mask` — `not(maskLit)` evaluates to `maskLit.lnot` (state-preserving);
* `eval_masked_keccak` — the full `and(keccak256 …, not …)` ⇒ the keccak value masked
  by `maskLit.lnot`.

Composed with `keccak256_value` + `uint256_kec_mask_toNat` + the proved `AddressShape`
shape lemmas, this turns each loop-body hash into its model value
(`leafHash`/`climbLevel`/…).
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

variable {n : Nat} {co : Option YulContract} {s : EvmYul.Yul.State}

/-- `keccak256(off, len)` — value + the post-keccak state. -/
theorem eval_keccak (off len : UInt256) :
    eval (n+6) (.Call (Sum.inl .KECCAK256) [.Lit off, .Lit len]) co s
      = .ok (s.setMachineState (s.toMachineState.keccak256 off len).2,
             (s.toMachineState.keccak256 off len).1) :=
  eval_binop2_thread (n := n) (primCall_keccak256 (n := n+4) s off len) (eval_lit) (eval_lit)

/-- `not(maskLit)` — state-preserving. -/
theorem eval_not_mask (maskLit : UInt256) :
    eval (n+4) (.Call (Sum.inl .NOT) [.Lit maskLit]) co s = .ok (s, maskLit.lnot) :=
  eval_unop1 (n := n) (primCall_not maskLit) (eval_lit)

/-- The full `and(keccak256(off, len), not maskLit)` — the masked keccak value, in the
    post-keccak state. The eval core for every leaf/node/roots/address hash. -/
theorem eval_masked_keccak (off len maskLit : UInt256) :
    eval (n+10) (.Call (Sum.inl .AND)
      [.Call (Sum.inl .KECCAK256) [.Lit off, .Lit len], .Call (Sum.inl .NOT) [.Lit maskLit]]) co s
    = .ok (s.setMachineState (s.toMachineState.keccak256 off len).2,
           ((s.toMachineState.keccak256 off len).1).land maskLit.lnot) :=
  eval_binop2_thread (n := n+4)
    (primCall_and (n := n+8) (s := s.setMachineState (s.toMachineState.keccak256 off len).2)
      (s.toMachineState.keccak256 off len).1 maskLit.lnot)
    (eval_keccak off len) (eval_not_mask maskLit)

end NiceTry.Fors.Bridge
