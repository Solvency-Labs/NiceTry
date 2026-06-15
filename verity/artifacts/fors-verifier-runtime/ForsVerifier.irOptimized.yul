/// @use-src 0:"src/Interfaces/ISignatureVerifier.sol", 1:"src/Verifiers/ForsVerifier.sol"
object "ForsVerifier_240" {
    code {
        {
            /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
            let _1 := memoryguard(0x80)
            mstore(64, _1)
            if callvalue() { revert(0, 0) }
            let _2 := datasize("ForsVerifier_240_deployed")
            codecopy(_1, dataoffset("ForsVerifier_240_deployed"), _2)
            return(_1, _2)
        }
    }
    /// @use-src 1:"src/Verifiers/ForsVerifier.sol"
    object "ForsVerifier_240_deployed" {
        code {
            {
                /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
                mstore(64, memoryguard(0x80))
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
                        let ret_1 := /** @src 1:5780:5792  "FORS_SIG_LEN" */ constant_FORS_SIG_LEN()
                        /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
                        let memPos_1 := mload(64)
                        mstore(memPos_1, ret_1)
                        return(memPos_1, 32)
                    }
                    case 0xa932492f {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                        let memPos_2 := mload(64)
                        mstore(memPos_2, /** @src 1:3239:3241  "26" */ 0x1a)
                        /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
                        return(memPos_2, 32)
                    }
                    case 0xc9e525df {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                        let memPos_3 := mload(64)
                        mstore(memPos_3, /** @src 1:3899:3901  "16" */ 0x10)
                        /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
                        return(memPos_3, 32)
                    }
                    case 0xf446c1d0 {
                        if callvalue() { revert(0, 0) }
                        if slt(add(calldatasize(), not(3)), 0) { revert(0, 0) }
                        let memPos_4 := mload(64)
                        mstore(memPos_4, /** @src 1:3325:3326  "5" */ 0x05)
                        /// @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..."
                        return(memPos_4, 32)
                    }
                }
                revert(0, 0)
            }
            /// @src 1:4114:4212  "uint256 constant FORS_SIG_LEN = FORS_R_LEN + FORS_PKSEED_LEN + FORS_SECTION_LEN + FORS_COUNTER_LEN"
            function constant_FORS_SIG_LEN() -> ret
            {
                /// @src 1:4177:4193  "FORS_SECTION_LEN"
                let ret_1 := /** @src -1:-1:-1 */ 0
                /// @src 1:4050:4063  "FORS_TREE_LEN"
                let ret_2 := /** @src -1:-1:-1 */ 0
                /// @src 1:3975:3991  "16 + FORS_A * 16"
                ret_2 := /** @src 1:3938:3940  "16" */ 96
                /// @src 1:4035:4063  "(FORS_K - 1) * FORS_TREE_LEN"
                let product := /** @src -1:-1:-1 */ 0
                /// @src 1:3325:3326  "5"
                product := 2400
                let _1 := /** @src -1:-1:-1 */ 0
                /// @src 1:3325:3326  "5"
                _1 := /** @src -1:-1:-1 */ 0
                /// @src 1:4035:4063  "(FORS_K - 1) * FORS_TREE_LEN"
                ret_1 := /** @src 1:3325:3326  "5" */ product
                /// @src 1:4146:4193  "FORS_R_LEN + FORS_PKSEED_LEN + FORS_SECTION_LEN"
                let sum := /** @src -1:-1:-1 */ 0
                /// @src 1:3938:3940  "16"
                sum := add(32, /** @src 1:3325:3326  "5" */ product)
                /// @src 1:3938:3940  "16"
                if gt(32, sum)
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 1:3938:3940  "16" */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 1:3938:3940  "16" */ 0x24)
                }
                let sum_1 := add(/** @src 1:3325:3326  "5" */ product, /** @src 1:3938:3940  "16" */ 48)
                if gt(sum, sum_1)
                {
                    mstore(/** @src -1:-1:-1 */ 0, /** @src 1:3938:3940  "16" */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src -1:-1:-1 */ 0, /** @src 1:3938:3940  "16" */ 0x24)
                }
                /// @src 1:4146:4212  "FORS_R_LEN + FORS_PKSEED_LEN + FORS_SECTION_LEN + FORS_COUNTER_LEN"
                ret := sum_1
            }
            /// @ast-id 239 @src 1:5838:12807  "function recover(bytes calldata sig, bytes32 digest) external pure override returns (address) {..."
            function fun_recover(var_sig_offset, var_sig_length, var_digest) -> var
            {
                /// @src 1:5923:5930  "address"
                var := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:6263:6275  "FORS_SIG_LEN"
                let expr := constant_FORS_SIG_LEN()
                /// @src 1:6381:6400  "FORS_SECTION_OFFSET"
                let ret := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:4371:4407  "FORS_PKSEED_OFFSET + FORS_PKSEED_LEN"
                ret := /** @src 1:5117:5119  "32" */ 0x20
                /// @src 1:4476:4492  "FORS_SECTION_LEN"
                let ret_1 := /** @src -1:-1:-1 */ 0
                /// @src 1:4050:4063  "FORS_TREE_LEN"
                let ret_2 := /** @src -1:-1:-1 */ 0
                /// @src 1:3975:3991  "16 + FORS_A * 16"
                ret_2 := /** @src 1:3938:3940  "16" */ 96
                /// @src 1:4035:4063  "(FORS_K - 1) * FORS_TREE_LEN"
                let product := /** @src -1:-1:-1 */ 0
                /// @src 1:3325:3326  "5"
                product := 2400
                let _1 := /** @src -1:-1:-1 */ 0
                /// @src 1:3325:3326  "5"
                _1 := /** @src -1:-1:-1 */ 0
                /// @src 1:4035:4063  "(FORS_K - 1) * FORS_TREE_LEN"
                ret_1 := /** @src 1:3325:3326  "5" */ product
                /// @src 1:4454:4492  "FORS_SECTION_OFFSET + FORS_SECTION_LEN"
                let sum := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:3938:3940  "16"
                sum := add(/** @src 1:5117:5119  "32" */ ret, /** @src 1:3325:3326  "5" */ product)
                /// @src 1:3938:3940  "16"
                if gt(/** @src 1:5117:5119  "32" */ ret, /** @src 1:3938:3940  "16" */ sum)
                {
                    mstore(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:3938:3940  "16" */ shl(224, 0x4e487b71))
                    mstore(4, 0x11)
                    revert(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:3938:3940  "16" */ 0x24)
                }
                /// @src 1:6481:6494  "FORS_TREE_LEN"
                let ret_3 := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:3975:3991  "16 + FORS_A * 16"
                ret_3 := /** @src 1:3938:3940  "16" */ ret_2
                /// @src 1:6900:6945  "if (sig.length != SIG_LEN_) return address(0)"
                if /** @src 1:6904:6926  "sig.length != SIG_LEN_" */ iszero(eq(var_sig_length, expr))
                /// @src 1:6900:6945  "if (sig.length != SIG_LEN_) return address(0)"
                {
                    /// @src 1:6928:6945  "return address(0)"
                    var := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                    /// @src 1:6928:6945  "return address(0)"
                    leave
                }
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                let usr$pkSeed := and(calldataload(add(var_sig_offset, /** @src 1:3899:3901  "16" */ 0x10)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$pkSeed)
                mstore(/** @src 1:5117:5119  "32" */ ret, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ and(calldataload(var_sig_offset), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(0x40, var_digest)
                mstore(/** @src 1:3938:3940  "16" */ ret_2, /** @src 1:5240:5306  "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD" */ not(2))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(/** @src 1:3325:3326  "5" */ 128, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ and(calldataload(add(add(var_sig_offset, /** @src 1:3325:3326  "5" */ product), /** @src 1:5117:5119  "32" */ ret)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                let usr$dVal := keccak256(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ 0xa0)
                if and(shr(/** @src 1:3325:3326  "5" */ 125, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$dVal), /** @src 1:3239:3241  "26" */ 31)
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                {
                    mstore(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, 0)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    return(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:5117:5119  "32" */ ret)
                }
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(0x380, usr$pkSeed)
                let usr$t := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                let usr$treePtr := add(var_sig_offset, /** @src 1:5117:5119  "32" */ ret)
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                let usr$rootPtr := 0x40
                let usr$tLeafBase := /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                let usr$dCursor := usr$dVal
                for { }
                lt(usr$t, /** @src 1:3239:3241  "26" */ 25)
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                {
                    usr$t := add(usr$t, /** @src 1:3325:3326  "5" */ 1)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    usr$treePtr := add(usr$treePtr, /** @src 1:3938:3940  "16" */ ret_2)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    usr$rootPtr := add(usr$rootPtr, /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    usr$tLeafBase := add(usr$tLeafBase, /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    usr$dCursor := shr(/** @src 1:3325:3326  "5" */ 0x05, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$dCursor)
                }
                {
                    mstore(0x3a0, or(shl(128, /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 3), /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ or(usr$tLeafBase, and(usr$dCursor, /** @src 1:3239:3241  "26" */ 31))))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3c0, and(calldataload(usr$treePtr), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$node := and(keccak256(0x380, /** @src 1:3938:3940  "16" */ ret_2), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$s := and(shl(/** @src 1:3325:3326  "5" */ 0x05, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$dCursor), /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3a0, or(or(shl(4, usr$t), and(shr(/** @src 1:3325:3326  "5" */ 1, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$dCursor), 15)), 0x0300000000000000000000000100000000))
                    mstore(xor(0x3c0, usr$s), usr$node)
                    mstore(xor(0x3e0, usr$s), and(calldataload(add(usr$treePtr, /** @src 1:3899:3901  "16" */ 0x10)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$node_1 := and(keccak256(0x380, /** @src 1:3325:3326  "5" */ 128), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$s_1 := and(and(and(shl(4, usr$dCursor), not(31)), 480), /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3a0, or(or(shl(3, usr$t), and(shr(2, usr$dCursor), 7)), 0x0300000000000000000000000200000000))
                    mstore(xor(0x3c0, usr$s_1), usr$node_1)
                    mstore(xor(0x3e0, usr$s_1), and(calldataload(add(usr$treePtr, /** @src 1:5117:5119  "32" */ ret)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$node_2 := and(keccak256(0x380, /** @src 1:3325:3326  "5" */ 128), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$s_2 := and(and(and(shl(3, usr$dCursor), not(31)), 224), /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3a0, or(or(shl(2, usr$t), and(shr(3, usr$dCursor), 3)), 0x0300000000000000000000000300000000))
                    mstore(xor(0x3c0, usr$s_2), usr$node_2)
                    mstore(xor(0x3e0, usr$s_2), and(calldataload(add(usr$treePtr, 48)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$node_3 := and(keccak256(0x380, /** @src 1:3325:3326  "5" */ 128), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$s_3 := and(and(and(shl(2, usr$dCursor), not(31)), /** @src 1:3938:3940  "16" */ ret_2), /** @src 1:5117:5119  "32" */ ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3a0, or(or(shl(/** @src 1:3325:3326  "5" */ 1, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$t), and(shr(4, usr$dCursor), /** @src 1:3325:3326  "5" */ 1)), /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ 0x0300000000000000000000000400000000))
                    mstore(xor(0x3c0, usr$s_3), usr$node_3)
                    mstore(xor(0x3e0, usr$s_3), and(calldataload(add(usr$treePtr, 0x40)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$node_4 := and(keccak256(0x380, /** @src 1:3325:3326  "5" */ 128), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    let usr$s_4 := and(and(and(shl(/** @src 1:3325:3326  "5" */ 1, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ usr$dCursor), not(31)), /** @src 1:5117:5119  "32" */ ret), ret)
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(0x3a0, or(usr$t, 0x0300000000000000000000000500000000))
                    mstore(xor(0x3c0, usr$s_4), usr$node_4)
                    mstore(xor(0x3e0, usr$s_4), and(calldataload(add(usr$treePtr, 80)), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                    /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                    mstore(usr$rootPtr, and(keccak256(0x380, /** @src 1:3325:3326  "5" */ 128), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                }
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(/** @src 1:5117:5119  "32" */ ret, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ shl(130, /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 1))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(/** @src 1:5117:5119  "32" */ ret, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ and(keccak256(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:3325:3326  "5" */ 864), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ not(0xffffffffffffffffffffffffffffffff)))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                mstore(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ and(keccak256(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:6956:12801  "assembly (\"memory-safe\") {..." */ 0x40), /** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ sub(shl(160, 1), 1)))
                /// @src 1:6956:12801  "assembly (\"memory-safe\") {..."
                return(/** @src 1:5527:12809  "contract ForsVerifier is ISignatureVerifier {..." */ 0, /** @src 1:5117:5119  "32" */ ret)
            }
        }
        data ".metadata" hex"a2646970667358221220b025656c5ffb71c940c16f707dacbd0917f63d0fd53e10d2e0128bf4b9340fa864736f6c634300081e0033"
    }
}

