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

end NiceTry.Fors.Bridge
