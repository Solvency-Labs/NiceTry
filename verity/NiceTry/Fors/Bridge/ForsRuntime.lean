import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

/-!
# `ForsVerifier.sol` as an EVMYulLean `YulContract` (route i, execution core)

`forsVerifierRuntime` is the contract runtime transcribed from its solc
optimized Yul IR (`forge inspect … irOptimized`) into EVMYulLean's elaboration
DSL.
Transcription rules applied: strip comments, reduce `memoryguard(x)` to `x`, and
rename `usr$foo` to `usr_foo` for the DSL identifier grammar. The pinned source,
optimized-IR, and Lean-runtime hashes are checked by
`scripts/audit-fors-verifier.sh`.

**Status: reviewed transcription complete.** Dispatcher + both helper functions
(`constant_FORS_SIG_LEN`, `fun_recover` — incl. the FORS tree `for`-loop) are
transcribed from the optimized IR and elaborate to a `YulContract`. The
transcription is a documented review boundary, not a kernel-proved compiler
translation; see `VERIFICATION_REPORT.md`.
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

/-- `constant_FORS_SIG_LEN` — faithful transcription from solc optimized IR (= 2448). -/
def forsConstSigLen : FunctionDefinition := <f
            function constant_FORS_SIG_LEN() -> ret
            {

                let ret_1 :=  0

                let ret_2 :=  0

                ret_2 :=  96

                let product :=  0

                product := 2400
                let _1 :=  0

                _1 :=  0

                ret_1 :=  product

                let sum :=  0

                sum := add(32,  product)

                if gt(32, sum)
                {
                    mstore( 0,  shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert( 0,  0x24)
                }
                let sum_1 := add( product,  48)
                if gt(sum, sum_1)
                {
                    mstore( 0,  shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert( 0,  0x24)
                }

                ret := sum_1
            }

>

/-- `fun_recover` — faithful transcription of the deployed inline-asm recover
    (Hmsg, forced-zero guard, FORS tree for-loop, roots compression, address). -/
def forsFunRecover : FunctionDefinition := <f
            function fun_recover(var_sig_offset, var_sig_length, var_digest) -> var
            {

                var :=  0

                let expr := constant_FORS_SIG_LEN()

                let ret :=  0

                ret :=  0x20

                let ret_1 :=  0

                let ret_2 :=  0

                ret_2 :=  96

                let product :=  0

                product := 2400
                let _1 :=  0

                _1 :=  0

                ret_1 :=  product

                let sum :=  0

                sum := add( ret,  product)

                if gt( ret,  sum)
                {
                    mstore( 0,  shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert( 0,  0x24)
                }

                let ret_3 :=  0

                ret_3 :=  ret_2

                if  iszero(eq(var_sig_length, expr))

                {

                    var :=  0

                    leave
                }

                let usr_pkSeed := and(calldataload(add(var_sig_offset,  0x10)),  not(0xffffffffffffffffffffffffffffffff))

                mstore( 0,  usr_pkSeed)
                mstore( ret,  and(calldataload(var_sig_offset),  not(0xffffffffffffffffffffffffffffffff)))

                mstore(0x40, var_digest)
                mstore( ret_2,  not(2))

                mstore( 128,  and(calldataload(add(add(var_sig_offset,  product),  ret)),  not(0xffffffffffffffffffffffffffffffff)))

                let usr_dVal := keccak256( 0,  0xa0)
                if and(shr( 125,  usr_dVal),  31)

                {
                    mstore( 0, 0)

                    return( 0,  ret)
                }

                mstore(0x380, usr_pkSeed)
                let usr_t :=  0

                let usr_treePtr := add(var_sig_offset,  ret)

                let usr_rootPtr := 0x40
                let usr_tLeafBase :=  0

                let usr_dCursor := usr_dVal
                for { }
                lt(usr_t,  25)

                {
                    usr_t := add(usr_t,  1)

                    usr_treePtr := add(usr_treePtr,  ret_2)

                    usr_rootPtr := add(usr_rootPtr,  ret)

                    usr_tLeafBase := add(usr_tLeafBase,  ret)

                    usr_dCursor := shr( 0x05,  usr_dCursor)
                }
                {
                    mstore(0x3a0, or(shl(128,  3),  or(usr_tLeafBase, and(usr_dCursor,  31))))

                    mstore(0x3c0, and(calldataload(usr_treePtr),  not(0xffffffffffffffffffffffffffffffff)))

                    let usr_node := and(keccak256(0x380,  ret_2),  not(0xffffffffffffffffffffffffffffffff))

                    let usr_s := and(shl( 0x05,  usr_dCursor),  ret)

                    mstore(0x3a0, or(or(shl(4, usr_t), and(shr( 1,  usr_dCursor), 15)), 0x0300000000000000000000000100000000))
                    mstore(xor(0x3c0, usr_s), usr_node)
                    mstore(xor(0x3e0, usr_s), and(calldataload(add(usr_treePtr,  0x10)),  not(0xffffffffffffffffffffffffffffffff)))

                    let usr_node_1 := and(keccak256(0x380,  128),  not(0xffffffffffffffffffffffffffffffff))

                    let usr_s_1 := and(and(and(shl(4, usr_dCursor), not(31)), 480),  ret)

                    mstore(0x3a0, or(or(shl(3, usr_t), and(shr(2, usr_dCursor), 7)), 0x0300000000000000000000000200000000))
                    mstore(xor(0x3c0, usr_s_1), usr_node_1)
                    mstore(xor(0x3e0, usr_s_1), and(calldataload(add(usr_treePtr,  ret)),  not(0xffffffffffffffffffffffffffffffff)))

                    let usr_node_2 := and(keccak256(0x380,  128),  not(0xffffffffffffffffffffffffffffffff))

                    let usr_s_2 := and(and(and(shl(3, usr_dCursor), not(31)), 224),  ret)

                    mstore(0x3a0, or(or(shl(2, usr_t), and(shr(3, usr_dCursor), 3)), 0x0300000000000000000000000300000000))
                    mstore(xor(0x3c0, usr_s_2), usr_node_2)
                    mstore(xor(0x3e0, usr_s_2), and(calldataload(add(usr_treePtr, 48)),  not(0xffffffffffffffffffffffffffffffff)))

                    let usr_node_3 := and(keccak256(0x380,  128),  not(0xffffffffffffffffffffffffffffffff))

                    let usr_s_3 := and(and(and(shl(2, usr_dCursor), not(31)),  ret_2),  ret)

                    mstore(0x3a0, or(or(shl( 1,  usr_t), and(shr(4, usr_dCursor),  1)),  0x0300000000000000000000000400000000))
                    mstore(xor(0x3c0, usr_s_3), usr_node_3)
                    mstore(xor(0x3e0, usr_s_3), and(calldataload(add(usr_treePtr, 0x40)),  not(0xffffffffffffffffffffffffffffffff)))

                    let usr_node_4 := and(keccak256(0x380,  128),  not(0xffffffffffffffffffffffffffffffff))

                    let usr_s_4 := and(and(and(shl( 1,  usr_dCursor), not(31)),  ret), ret)

                    mstore(0x3a0, or(usr_t, 0x0300000000000000000000000500000000))
                    mstore(xor(0x3c0, usr_s_4), usr_node_4)
                    mstore(xor(0x3e0, usr_s_4), and(calldataload(add(usr_treePtr, 80)),  not(0xffffffffffffffffffffffffffffffff)))

                    mstore(usr_rootPtr, and(keccak256(0x380,  128),  not(0xffffffffffffffffffffffffffffffff)))
                }

                mstore( ret,  shl(130,  1))

                mstore( ret,  and(keccak256( 0,  864),  not(0xffffffffffffffffffffffffffffffff)))

                mstore( 0,  and(keccak256( 0,  0x40),  sub(shl(160, 1), 1)))

                return( 0,  ret)
            }
>

def forsVerifierRuntime : YulContract :=
  { dispatcher := forsDispatcher
    functions :=
      (∅ : Finmap (fun (_ : YulFunctionName) ↦ FunctionDefinition))
        |>.insert "constant_FORS_SIG_LEN" forsConstSigLen
        |>.insert "fun_recover" forsFunRecover }

end NiceTry.Fors.Bridge
