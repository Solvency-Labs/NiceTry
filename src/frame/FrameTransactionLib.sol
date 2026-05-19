// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

/// @notice Constants from the draft EIP-8141 frame transaction interface.
/// @dev The opcode adapter is deliberately not implemented in Solidity here.
///      Current solc inline assembly does not expose custom draft opcodes, so
///      production deployment needs a frame-aware runtime/proxy layer.
library FrameTransactionLib {
    uint256 internal constant TXPARAM_SIG_HASH = 0x08;
    uint256 internal constant TXPARAM_FRAME_COUNT = 0x09;
    uint256 internal constant TXPARAM_CURRENT_FRAME = 0x0A;

    uint256 internal constant FRAMEPARAM_TARGET = 0x00;
    uint256 internal constant FRAMEPARAM_MODE = 0x02;
    uint256 internal constant FRAMEPARAM_FLAGS = 0x03;
    uint256 internal constant FRAMEPARAM_DATA_LENGTH = 0x04;
    uint256 internal constant FRAMEPARAM_ATOMIC_BATCH = 0x07;
    uint256 internal constant FRAMEPARAM_VALUE = 0x08;

    uint256 internal constant APPROVE_EXECUTION_AND_PAYMENT = 0x03;
}
