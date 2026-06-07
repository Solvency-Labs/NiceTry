import NiceTry.Fors.Bridge.ClassAConst

/-!
# Class-A `fun_recover` stepping

Concrete interpreter facts for the good-length `fun_recover` path after
`constant_FORS_SIG_LEN()` has returned `expr = SigLen`.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 800000

def recoverAfterRetZero (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterExprConst raw digest).insert "ret" (UInt256.ofNat 0)

def recoverAfterRetWord (raw : RawSig) (digest : Digest) : EvmYul.Yul.State :=
  (recoverAfterRetZero raw digest).insert "ret" (UInt256.ofNat 0x20)

theorem recoverAfterRetWord_lookup_ret
    (raw : RawSig) (digest : Digest) :
    EvmYul.Yul.State.lookup! "ret" (recoverAfterRetWord raw digest) =
      UInt256.ofNat 0x20 := by
  rfl

/-- Continue `fun_recover` after `expr := constant_FORS_SIG_LEN()` through
    `ret := 0; ret := 0x20`, leaving execution at `forsFunRecover.body.drop 4`. -/
theorem exec_recover_ret_init_after_expr
    (raw : RawSig) (digest : Digest) :
    exec 45 (.Block (forsFunRecover.body.drop 2)) (some forsVerifierRuntime)
        (recoverAfterExprConst raw digest) =
      exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
        (recoverAfterRetWord raw digest) := by
  change exec 45
      (.Block (.Let ["ret"] (.some (.Lit (UInt256.ofNat 0))) ::
        forsFunRecover.body.drop 3))
      (some forsVerifierRuntime) (recoverAfterExprConst raw digest) =
    exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
      (recoverAfterRetWord raw digest)
  rw [exec_block_cons_ok
    (n := 44) (co := some forsVerifierRuntime)
    (s := recoverAfterExprConst raw digest)
    (st := .Let ["ret"] (.some (.Lit (UInt256.ofNat 0))))
    (sts := forsFunRecover.body.drop 3)
    (s₁ := recoverAfterRetZero raw digest)
    (h := by
      simpa [recoverAfterRetZero] using
        (exec_let_lit (n := 43) (co := some forsVerifierRuntime)
          (s := recoverAfterExprConst raw digest)
          (vars := ["ret"]) (lit := UInt256.ofNat 0)))]
  change exec 44
      (.Block (.Let ["ret"] (.some (.Lit (UInt256.ofNat 0x20))) ::
        forsFunRecover.body.drop 4))
      (some forsVerifierRuntime) (recoverAfterRetZero raw digest) =
    exec 43 (.Block (forsFunRecover.body.drop 4)) (some forsVerifierRuntime)
      (recoverAfterRetWord raw digest)
  rw [exec_block_cons_ok
    (n := 43) (co := some forsVerifierRuntime)
    (s := recoverAfterRetZero raw digest)
    (st := .Let ["ret"] (.some (.Lit (UInt256.ofNat 0x20))))
    (sts := forsFunRecover.body.drop 4)
    (s₁ := recoverAfterRetWord raw digest)
    (h := by
      simpa [recoverAfterRetWord] using
        (exec_let_lit (n := 42) (co := some forsVerifierRuntime)
          (s := recoverAfterRetZero raw digest)
          (vars := ["ret"]) (lit := UInt256.ofNat 0x20)))]

end NiceTry.Fors.Bridge
