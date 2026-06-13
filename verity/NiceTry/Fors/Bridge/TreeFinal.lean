import NiceTry.Fors.Bridge.TreeLoop

/-!
# M4: post-loop assembly — the roots buffer as one concatenation

`tree_loop_run` leaves the 25 root slots `[0x40 + 32j, 0x40 + 32(j+1))`
individually characterized; the roots-compression keccak reads them as one
window. This file folds the per-slot extracts into the
`concatData (List.ofFn …)` form `roots_derivation_eq_from_buffer` consumes.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast
open NiceTry.Fors

set_option maxHeartbeats 2000000

theorem concatData_append (l₁ l₂ : List ByteArray) :
    concatData (l₁ ++ l₂) = concatData l₁ ++ concatData l₂ := by
  induction l₁ with
  | nil => simp [concatData]
  | cons w ws ih =>
    show w.data ++ concatData (ws ++ l₂) = w.data ++ concatData ws ++ concatData l₂
    rw [ih, Array.append_assoc]

/-- Folding `k` adjacent 32-byte slot extracts into one window extract. -/
theorem extract_slots_concat (M : MachineState) (rootsW : Nat → UInt256)
    (hslots : ∀ j, j < 25 →
      M.memory.data.extract (0x40 + 32 * j) (0x40 + 32 * j + 32)
        = (rootsW j).toByteArray.data)
    (hsize : 0x360 ≤ M.memory.size) :
    ∀ k, k ≤ 25 →
      M.memory.data.extract 0x40 (0x40 + 32 * k)
        = concatData ((List.ofFn (fun i : Fin k => rootsW i.val)).map
            UInt256.toByteArray) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [concatData]
  | succ k ih =>
    intro hk
    have hmd : M.memory.data.size = M.memory.size := rfl
    rw [extract_split M.memory.data 0x40 (0x40 + 32 * k) (0x40 + 32 * (k + 1))
        (by omega) (by omega) (by omega),
      ih (by omega),
      show 0x40 + 32 * (k + 1) = (0x40 + 32 * k) + 32 from by omega,
      hslots k (by omega),
      show (List.ofFn (fun i : Fin (k + 1) => rootsW i.val))
          = (List.ofFn (fun i : Fin k => rootsW i.val)) ++ [rootsW k] from by
        rw [List.ofFn_succ_last]
        rfl,
      List.map_append, concatData_append]
    rfl

/-- The full roots window in the handoff's `concatData (List.ofFn …)` form. -/
theorem roots_buffer_concat (M : MachineState) (rootsW : Nat → UInt256)
    (hslots : ∀ j, j < 25 →
      M.memory.data.extract (0x40 + 32 * j) (0x40 + 32 * j + 32)
        = (rootsW j).toByteArray.data)
    (hsize : 0x360 ≤ M.memory.size) :
    M.memory.data.extract RootBufferStart RootsHashLen
      = concatData ((List.ofFn (fun i : TreeIndex => rootsW i.val)).map
          UInt256.toByteArray) := by
  have h := extract_slots_concat M rootsW hslots hsize 25 (by omega)
  unfold RootBufferStart RootsHashLen K
  show M.memory.data.extract 0x40 864 = _
  rw [show (864 : Nat) = 0x40 + 32 * 25 from by omega]
  exact h


/-! ## Word decode: `fromByteArrayBigEndian ∘ toByteArray = toNat` -/

theorem fromBytes'_lt : ∀ l : List UInt8, fromBytes' l < 2 ^ (8 * l.length) := by
  intro l
  induction l with
  | nil => simp [fromBytes']
  | cons b bs ih =>
    show b.toFin.val + 2 ^ 8 * fromBytes' bs < _
    have hb : b.toFin.val < 256 := b.toFin.isLt
    rw [show 8 * (b :: bs).length = 8 * bs.length + 8 from by
      simp [List.length_cons]; ring, pow_add]
    have h2 : (0 : Nat) < 2 ^ (8 * bs.length) := Nat.pow_pos (by norm_num)
    nlinarith [ih]

theorem byteArray_toList_loop_spec (bs : ByteArray) :
    ∀ k i r, bs.size - i = k →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have hbd : bs.data.size = bs.size := rfl
  intro k
  induction k with
  | zero =>
    intro i r hk
    rw [ByteArray.toList.loop.eq_def, if_neg (by omega),
      List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega),
      List.append_nil]
  | succ k ih =>
    intro i r hk
    have hi : i < bs.data.size := by omega
    have hstep := ih (i + 1) (bs.get! i :: r)
      (show bs.size - (i + 1) = k by omega)
    rw [ByteArray.toList.loop.eq_def, if_pos (show i < bs.size by omega), hstep,
      List.reverse_cons, List.append_assoc]
    congr 1
    rw [List.drop_eq_getElem_cons (l := bs.data.toList) (i := i)
      (by rw [Array.length_toList]; exact hi)]
    show bs.get! i :: List.drop (i + 1) bs.data.toList
        = bs.data.toList[i]'(by rw [Array.length_toList]; exact hi)
          :: List.drop (i + 1) bs.data.toList
    rw [Array.getElem_toList,
      show bs.get! i = bs.data[i]'hi from getElem!_pos bs.data i hi]

theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  show ByteArray.toList.loop b 0 [] = b.data.toList
  rw [byteArray_toList_loop_spec b b.size 0 [] (by omega)]
  simp

/-- Big-endian decode of a stored word is its value. -/
theorem fromBE_toByteArray (v : UInt256) :
    fromByteArrayBigEndian v.toByteArray = v.toNat := by
  have hlen : v.toByteArray.data.toList.reverse.length = 32 := by
    rw [List.length_reverse]
    show v.toByteArray.data.toList.length = 32
    rw [Array.length_toList]
    exact uint256_toByteArray_size v
  have hlt : fromBytes' v.toByteArray.data.toList.reverse < UInt256.size := by
    have h := fromBytes'_lt v.toByteArray.data.toList.reverse
    rw [hlen] at h
    have : UInt256.size = 2 ^ 256 := by decide
    omega
  have hr := congrArg UInt256.toNat (uint256_toByteArray_roundtrip v)
  have key : fromBytes' v.toByteArray.data.toList.reverse = v.toNat := by
    rw [show (uInt256OfByteArray v.toByteArray).toNat
        = fromBytes' v.toByteArray.data.toList.reverse from
      uint256_ofNat_toNat_of_lt _ hlt] at hr
    exact hr
  unfold fromByteArrayBigEndian fromBytesBigEndian Function.comp
  show fromBytes' (v.toByteArray.toList).reverse = v.toNat
  rw [byteArray_toList_eq]
  exact key

/-! ## The 160-bit masked address keccak -/

theorem mask160_value :
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)
      = UInt256.ofNat (2 ^ 160 - 1) := by decide

theorem masked160_keccak_toNat (m : MachineState) (off len : UInt256) :
    (((m.keccak256 off len).1).land
        ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub
          (UInt256.ofNat 1))).toNat
      = (fromByteArrayBigEndian
          (ffi.KEC (m.memory.readWithPadding off.toNat len.toNat)))
          &&& Lower160Mask := by
  rw [mask160_value, keccak256_value, uint256_land_toNat,
    uint256_ofNat_toNat_of_lt _ (ffi_kec_lt _),
    uint256_ofNat_toNat_of_lt (2 ^ 160 - 1) (by decide)]
  rfl

/-- `and(keccak256(<lit>, <lit>), sub(shl(160, 1), 1))` — the address mask. -/
theorem eval_masked160_keccak {n co} {s : EvmYul.Yul.State} (off len : UInt256) :
    eval (n+12) (.Call (Sum.inl .AND)
      [.Call (Sum.inl .KECCAK256) [.Lit off, .Lit len],
       .Call (Sum.inl .SUB)
         [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat 160), .Lit (UInt256.ofNat 1)],
          .Lit (UInt256.ofNat 1)]]) co s
    = .ok (s.setMachineState (s.toMachineState.keccak256 off len).2,
           ((s.toMachineState.keccak256 off len).1).land
             ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub
               (UInt256.ofNat 1))) :=
  eval_binop2_thread (n := n+6)
    (hprim := primCall_and (n := n+10)
      (s := s.setMachineState (s.toMachineState.keccak256 off len).2)
      (s.toMachineState.keccak256 off len).1
      ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub
        (UInt256.ofNat 1)))
    (he₁ := eval_keccak (n := n+2) off len)
    (he₂ := eval_binop2 (n := n+4) (f := UInt256.sub)
      (hprim := primCall_sub (n := n+8)
        (s := s) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1))
      (he₁ := eval_binop2 (n := n) (f := fun a b => UInt256.shiftLeft b a)
        (hprim := primCall_shl (n := n+4) (s := s) (UInt256.ofNat 160)
          (UInt256.ofNat 1))
        (he₁ := eval_lit (n := n+1)) (he₂ := eval_lit (n := n+3)))
      (he₂ := eval_lit (n := n+7)))

/-- `shl(130, 1)` is the roots-ADRS word. -/
theorem shl130_value :
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130)).toNat
      = ForsRootsAdrsWord := by decide

theorem eval_shl130 {n co} {s : EvmYul.Yul.State} :
    eval (n+6) (.Call (Sum.inl .SHL)
      [.Lit (UInt256.ofNat 130), .Lit (UInt256.ofNat 1)]) co s
    = .ok (s, UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130)) :=
  eval_binop2 (n := n) (f := fun a b => UInt256.shiftLeft b a)
    (hprim := primCall_shl (n := n+4) (s := s) (UInt256.ofNat 130) (UInt256.ofNat 1))
    (he₁ := eval_lit (n := n+1)) (he₂ := eval_lit (n := n+3))

/-- `return(<lit>, <var>)` — the `YulHalt` exit with the return window. -/
theorem exec_return_stmt {n co} {s : EvmYul.Yul.State} {a : UInt256}
    {x : Identifier} :
    exec (n+6) (.ExprStmtCall (.Call (Sum.inl .RETURN) [.Lit a, .Var x])) co s
      = .error (.YulHalt
          (s.setMachineState (s.toMachineState.evmReturn a s[x]!)) ⟨1⟩) := by
  rw [exec_exprstmt_prim (n := n+5)]
  show execPrimCall (n+5) .RETURN [] (reverse' (evalArgs (n+5) [.Var x, .Lit a] co s)) = _
  rw [evalArgs_cons_ok (n := n+4) (h := eval_var (n := n+3)),
    evalTail_cons_ok (n := n+3),
    evalArgs_cons_ok (n := n+2) (h := eval_lit (n := n+1)),
    evalTail_cons_ok (n := n+1), evalArgs_nil (n := n)]
  simp only [cons', reverse', List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append]
  exact execPrimCall_err (h := primCall_return (n := n+4) s a s[x]!)


/-! ## The post-loop trace: roots compression, address, return -/

set_option maxHeartbeats 4000000 in
/-- **The post-loop suffix** (`fun_recover` statements 33–36): from the loop
    exit (`ret = 0x20`, `pkSeed` at `0x00`, the 25 root slots populated), the
    block halts via `RETURN` with `H_return` decoding to
    `addressFromRoot pkSeed (compressRoots pkSeed roots)`. -/
theorem post_loop_trace (n : Nat) (co : Option YulContract)
    (sf : SharedState .Yul) (vf : EvmYul.Yul.VarStore)
    (pk : UInt256) (rootsW : Nat → UInt256)
    (hret : (EvmYul.Yul.State.Ok sf vf)[retId]! = UInt256.ofNat 32)
    (hpk0 : (EvmYul.Yul.State.Ok sf vf).toMachineState.memory.data.extract 0 32 = pk.toByteArray.data)
    (hslots : ∀ j, j < 25 →
      (EvmYul.Yul.State.Ok sf vf).toMachineState.memory.data.extract (0x40 + 32 * j) (0x40 + 32 * j + 32)
        = (rootsW j).toByteArray.data)
    (hsize : 0x400 ≤ (EvmYul.Yul.State.Ok sf vf).toMachineState.memory.size) :
    ∃ S : EvmYul.Yul.State,
      exec (n + 18) (.Block (forsFunRecover.body.drop 33)) co (.Ok sf vf)
        = .error (.YulHalt S ⟨1⟩)
      ∧ fromByteArrayBigEndian S.sharedState.H_return
        = addressFromRoot pk.toNat
            (compressRoots pk.toNat (fun i : TreeIndex => (rootsW i.val).toNat))
      ∧ addressFromRoot pk.toNat
          (compressRoots pk.toNat (fun i : TreeIndex => (rootsW i.val).toNat)) < 2 ^ 160 := by
  have h32 : (UInt256.ofNat 32).toNat = 32 := uint256_ofNat_toNat_of_lt _ (by decide)
  have h0 : (UInt256.ofNat 0).toNat = 0 := uint256_ofNat_toNat_of_lt _ (by decide)
  have h864 : (UInt256.ofNat 864).toNat = 864 := uint256_ofNat_toNat_of_lt _ (by decide)
  have h64 : (UInt256.ofNat 64).toNat = 64 := uint256_ofNat_toNat_of_lt _ (by decide)
  have hret' := hret
  rw [show retId = "ret" from rfl] at hret'
  -- statement 33: mstore(ret, shl(130, 1))
  have e33 : exec (n + 17)
      (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Var "ret", .Call (Sum.inl .SHL)
          [.Lit (UInt256.ofNat 130), .Lit (UInt256.ofNat 1)]])) co (.Ok sf vf)
      = .ok (.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf) := by
    have h := exec_mstore_expr (n := n + 11) (co := co) (s := .Ok sf vf)
      (he₁ := eval_var (n := n + 12) (id := "ret"))
      (he₂ := eval_shl130 (n := n + 9))
    rw [hret'] at h
    exact h
  -- statement 34: mstore(ret, and(keccak256(0, 864), not(0xff…ff)))
  have hv34 : eval (n + 12) (.Var "ret") co
      ((EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).setMachineState
        ((EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).toMachineState.keccak256
          (UInt256.ofNat 0) (UInt256.ofNat 864)).2)
      = .ok (((EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).setMachineState
          ((EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).toMachineState.keccak256
            (UInt256.ofNat 0) (UInt256.ofNat 864)).2), UInt256.ofNat 32) := by
    have h := eval_var (n := n + 11) (co := co) (id := "ret")
      (s := (EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).setMachineState
        ((EvmYul.Yul.State.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf).toMachineState.keccak256
          (UInt256.ofNat 0) (UInt256.ofNat 864)).2)
    rw [ok_set_getElem, state_getElem_shared_irrel { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } sf vf, hret'] at h
    exact h
  have e34 : exec (n + 16)
      (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Var "ret", .Call (Sum.inl .AND)
          [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 864)],
           .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]])) co (.Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf)
      = .ok (.Ok { sf with toMachineState := (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) } vf) := by
    have h := exec_mstore_thread (n := n + 10) (co := co) (s := .Ok { sf with toMachineState := (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) } vf)
      (he₂ := eval_masked_keccak (n := n + 4) (UInt256.ofNat 0) (UInt256.ofNat 864)
        (UInt256.ofNat 0xffffffffffffffffffffffffffffffff))
      (he₁ := hv34)
    exact h
  -- statement 35: mstore(0, and(keccak256(0, 64), sub(shl(160, 1), 1)))
  have e35 : exec (n + 15)
      (.ExprStmtCall (.Call (Sum.inl .MSTORE)
        [.Lit (UInt256.ofNat 0), .Call (Sum.inl .AND)
          [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 64)],
           .Call (Sum.inl .SUB)
             [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat 160), .Lit (UInt256.ofNat 1)],
              .Lit (UInt256.ofNat 1)]]])) co (.Ok { sf with toMachineState := (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) } vf)
      = .ok (.Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))) } vf) := by
    have h := exec_mstore_thread (n := n + 9) (co := co) (s := .Ok { sf with toMachineState := (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) } vf)
      (he₂ := eval_masked160_keccak (n := n + 1) (UInt256.ofNat 0) (UInt256.ofNat 64))
      (he₁ := eval_lit (n := n + 10) (val := UInt256.ofNat 0))
    exact h
  -- statement 36: return(0, ret) halts
  have e36 : exec (n + 14)
      (.ExprStmtCall (.Call (Sum.inl .RETURN) [.Lit (UInt256.ofNat 0), .Var "ret"]))
      co (.Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))) } vf)
      = .error (.YulHalt (.Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).evmReturn (UInt256.ofNat 0) (UInt256.ofNat 32) } vf) ⟨1⟩) := by
    have h := exec_return_stmt (n := n + 8) (co := co) (s := .Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))) } vf)
      (a := UInt256.ofNat 0) (x := "ret")
    rw [state_getElem_shared_irrel { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))) } sf vf, hret'] at h
    exact h
  -- assemble the block
  refine ⟨.Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).evmReturn (UInt256.ofNat 0) (UInt256.ofNat 32) } vf, ?_, ?_⟩
  · show exec (n + 18)
      (.Block ((.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Var "ret", .Call (Sum.inl .SHL)
            [.Lit (UInt256.ofNat 130), .Lit (UInt256.ofNat 1)]]))
        :: (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Var "ret", .Call (Sum.inl .AND)
            [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 864)],
             .Call (Sum.inl .NOT) [.Lit (UInt256.ofNat 0xffffffffffffffffffffffffffffffff)]]]))
        :: (.ExprStmtCall (.Call (Sum.inl .MSTORE)
          [.Lit (UInt256.ofNat 0), .Call (Sum.inl .AND)
            [.Call (Sum.inl .KECCAK256) [.Lit (UInt256.ofNat 0), .Lit (UInt256.ofNat 64)],
             .Call (Sum.inl .SUB)
               [.Call (Sum.inl .SHL) [.Lit (UInt256.ofNat 160), .Lit (UInt256.ofNat 1)],
                .Lit (UInt256.ofNat 1)]]]))
        :: (.ExprStmtCall (.Call (Sum.inl .RETURN)
            [.Lit (UInt256.ofNat 0), .Var "ret"]))
        :: [])) co (.Ok sf vf)
      = .error (.YulHalt (.Ok { sf with toMachineState := (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).evmReturn (UInt256.ofNat 0) (UInt256.ofNat 32) } vf) ⟨1⟩)
    rw [exec_block_cons_ok (h := e33), exec_block_cons_ok (h := e34),
      exec_block_cons_ok (h := e35)]
    exact exec_block_cons_err (h := e36)
  · -- the value: H_return decodes to the address
    have hM0 : (EvmYul.Yul.State.Ok sf vf).toMachineState = sf.toMachineState := rfl
    rw [hM0] at hpk0 hslots hsize
    -- sizes along the way
    have hsz1 : (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).memory.size = sf.toMachineState.memory.size :=
      mstore_memory_size sf.toMachineState (UInt256.ofNat 32)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130)) (by rw [h32]; omega)
    have hK1m : ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.memory = (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).memory := keccak256_memory _ _ _
    have hsz2 : (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).memory.size = ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.memory.size :=
      by
        have hb2 : (UInt256.ofNat 32).toNat + 32 ≤ ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.memory.size := by
          rw [h32, hK1m, hsz1]
          omega
        exact mstore_memory_size ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2 (UInt256.ofNat 32)
          ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot) hb2
    have hK2m : ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.memory = (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).memory := keccak256_memory _ _ _
    have hsz3 : (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).memory.size = ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.memory.size :=
      by
        have hb3 : (UInt256.ofNat 0).toNat + 32 ≤ ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.memory.size := by
          rw [h0, hK2m, hsz2, hK1m, hsz1]
          omega
        exact mstore_memory_size ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2 (UInt256.ofNat 0)
          ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1))) hb3
    -- (a) the roots word is compressRoots
    have hroots : ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat
        = compressRoots pk.toNat (fun i : TreeIndex => (rootsW i.val).toNat) := by
      have hmask := masked_keccak_toNat (sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))) (UInt256.ofNat 0) (UInt256.ofNat 864)
      rw [h0, h864] at hmask
      rw [hmask]
      have hd := roots_derivation_eq_from_buffer sf.toMachineState
        (UInt256.ofNat 32) pk (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))
        (fun i : TreeIndex => rootsW i.val)
        (by rw [h32]; rfl) shl130_value
        (by unfold RootsHashLen K; omega)
        hpk0
        (roots_buffer_concat sf.toMachineState rootsW hslots (by omega))
      show fromByteArrayBigEndian
          (ffi.KEC ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).memory.readWithPadding 0 864)) &&& NMaskWord = _
      rw [show (864 : Nat) = RootsHashLen from by unfold RootsHashLen K; omega]
      exact hd
    -- (b) the address word
    have haddr : ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1))).toNat
        = addressFromRoot pk.toNat ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot).toNat := by
      have hmask := masked160_keccak_toNat (((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)) (UInt256.ofNat 0) (UInt256.ofNat 64)
      rw [h0, h64] at hmask
      rw [hmask]
      have hpkK1 : ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.memory.data.extract 0 32 = pk.toByteArray.data := by
        rw [hK1m, mstore_extract_below' _ _ _ _ _ (by rw [h32]; omega) (by rw [h32])]
        exact hpk0
      have hd := address_derivation_eq_overwrite ((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2
        (UInt256.ofNat 32) pk ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)
        (by rw [h32]) (by rw [hK1m, hsz1]; omega) hpkK1
      exact hd
    -- (c) H_return = the address word's bytes
    apply And.intro
    show fromByteArrayBigEndian
        ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).evmReturn (UInt256.ofNat 0) (UInt256.ofNat 32)).H_return = _
    have hHr : ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).evmReturn (UInt256.ofNat 0) (UInt256.ofNat 32)).H_return
        = (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).memory.readWithPadding 0 32 := by
      show (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).memory.readWithPadding (UInt256.ofNat 0).toNat
          (UInt256.ofNat 32).toNat = _
      rw [h0, h32]
    have hslot0 : (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).memory.data.extract 0 32 = ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1))).toByteArray.data := by
      have h := mstore_extract_self' ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2 (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))
        (by rw [h0]; omega)
      rw [h0] at h
      exact h
    have hread : (((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).2.mstore (UInt256.ofNat 0) ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1)))).memory.readWithPadding 0 32 = ((((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).2.mstore (UInt256.ofNat 32) ((((sf.toMachineState.mstore (UInt256.ofNat 32) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 130))).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 864)).1).land (UInt256.ofNat 0xffffffffffffffffffffffffffffffff).lnot)).keccak256 (UInt256.ofNat 0) (UInt256.ofNat 64)).1).land ((UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).sub (UInt256.ofNat 1))).toByteArray := by
      apply ByteArray.ext
      rw [readWithPadding_prefix _ 32
          (by rw [hsz3, hK2m, hsz2, hK1m, hsz1]; omega)
          (by rw [hsz3, hK2m, hsz2, hK1m, hsz1]; omega) (by decide),
        ByteArray.data_extract]
      exact hslot0
    rw [hHr, hread, fromBE_toByteArray, haddr, hroots]
    rw [← hroots, ← haddr, uint256_land_toNat, mask160_value,
      uint256_ofNat_toNat_of_lt (2 ^ 160 - 1) (by decide)]
    exact lt_of_le_of_lt Nat.and_le_right (by decide)


end NiceTry.Fors.Bridge
