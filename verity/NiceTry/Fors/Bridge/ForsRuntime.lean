import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

/-!
# `ForsVerifier.sol` as an EVMYulLean `YulContract` (route i, execution core)

`forsVerifierRuntime` is the deployed contract transcribed from its solc optimized
Yul IR (`forge inspect … irOptimized`) into EVMYulLean's elaboration DSL.
Transcription rules applied (see `/tmp/normalize_yul.pl`): strip `/* */` + `///`
comments, `memoryguard(x) → x`, rename `usr$foo → usr_foo` (DSL identifiers).

**Status: WIP.** The dispatcher is transcribed faithfully and elaborates. The two
helper functions (`constant_FORS_SIG_LEN`, `fun_recover`) are **stubs** for now —
`fun_recover`'s body (the FORS tree `for`-loop) is the next chunk. Do NOT build
`evmRun` on this until `fun_recover` is the real body.
-/

namespace NiceTry.Fors.Bridge

open EvmYul EvmYul.Yul EvmYul.Yul.Ast

/-- The runtime dispatcher, transcribed verbatim from the deployed object
    (selector `switch` → `recover` + 4 constant getters). -/
def forsDispatcher : Stmt := <s
{
  mstore(64, 0x80)
  if iszero(lt(calldatasize(), 4))
  {
    switch shr(224, calldataload(0))
    case 0x1aad75c5 {
      if callvalue() { revert(0, 0) }
      if slt(add(calldatasize(), not(3)), 64) { revert(0, 0) }
      let offset := calldataload(4)
      if gt(offset, 0xffffffffffffffff) { revert(0, 0) }
      if iszero(slt(add(offset, 35), calldatasize())) { revert(0, 0) }
      let length := calldataload(add(4, offset))
      if gt(length, 0xffffffffffffffff) { revert(0, 0) }
      if gt(add(add(offset, length), 36), calldatasize()) { revert(0, 0) }
      let ret := fun_recover(add(offset, 36), length, calldataload(36))
      let memPos := mload(64)
      mstore(memPos, and(ret, sub(shl(160, 1), 1)))
      return(memPos, 0x20)
    }
    case 0x27e9933f {
      if callvalue() { revert(0, 0) }
      if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
      let ret_1 := constant_FORS_SIG_LEN()
      let memPos_1 := mload(64)
      mstore(memPos_1, ret_1)
      return(memPos_1, 32)
    }
    case 0xa932492f {
      if callvalue() { revert(0, 0) }
      if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
      let memPos_2 := mload(64)
      mstore(memPos_2, 0x1a)
      return(memPos_2, 32)
    }
    case 0xc9e525df {
      if callvalue() { revert(0, 0) }
      if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
      let memPos_3 := mload(64)
      mstore(memPos_3, 0x10)
      return(memPos_3, 32)
    }
    case 0xf446c1d0 {
      if callvalue() { revert(0, 0) }
      if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
      let memPos_4 := mload(64)
      mstore(memPos_4, 0x05)
      return(memPos_4, 32)
    }
  }
  revert(0, 0)
}
>

/-- WIP stub — `SIG_LEN = 2448`. The real solc body computes this with overflow
    checks; faithful transcription pending. -/
def forsConstSigLen : FunctionDefinition := <f
  function constant_FORS_SIG_LEN() -> ret { ret := 2448 }
>

/-- WIP stub — the real body (FORS tree `for`-loop, ~60 lines) is the next chunk. -/
def forsFunRecover : FunctionDefinition := <f
  function fun_recover(var_sig_offset, var_sig_length, var_digest) -> var { var := 0 }
>

/-- The deployed `ForsVerifier` runtime as a `YulContract`. (functions WIP.) -/
def forsVerifierRuntime : YulContract :=
  { dispatcher := forsDispatcher
    functions :=
      (∅ : Finmap (fun (_ : YulFunctionName) ↦ FunctionDefinition))
        |>.insert "constant_FORS_SIG_LEN" forsConstSigLen
        |>.insert "fun_recover" forsFunRecover }

end NiceTry.Fors.Bridge
