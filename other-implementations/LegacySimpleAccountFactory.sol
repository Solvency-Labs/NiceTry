// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {SimpleAccount_ECDSA} from "./ecdsa/SimpleAccount_ECDSA.sol";
import {SimpleAccount_WOTS} from "./wots/SimpleAccount_WOTS.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";
import {IWotsCVerifier} from "./wots/IWotsCVerifier.sol";
import {LibClone} from "solady/utils/LibClone.sol";

/// @title LegacySimpleAccountFactory
/// @notice Legacy ECDSA/WOTS multimode factory retained for tests and comparison.
///
///         Modes:
///           0 = ECDSA
///           1 = WOTS+C
contract LegacySimpleAccountFactory {
    IEntryPoint public immutable ENTRY_POINT;
    IWotsCVerifier public immutable WOTS_VERIFIER;

    address public immutable ECDSA_IMPL;
    address public immutable WOTS_IMPL;

    event AccountCreated(address indexed account, address indexed owner, uint256 salt);

    constructor(IEntryPoint _entryPoint, IWotsCVerifier _wotsVerifier) {
        ENTRY_POINT = _entryPoint;
        WOTS_VERIFIER = _wotsVerifier;
        ECDSA_IMPL = address(new SimpleAccount_ECDSA(_entryPoint));
        WOTS_IMPL = address(new SimpleAccount_WOTS(_entryPoint, _wotsVerifier));
    }

    function createAccount(address owner, uint256 salt, uint8 mode) external returns (address accountAddr) {
        address impl = _implFor(mode);
        bytes32 fullSalt = _salt(owner, salt);

        address predicted = LibClone.predictDeterministicAddress(impl, fullSalt, address(this));
        if (predicted.code.length > 0) return predicted;

        accountAddr = LibClone.cloneDeterministic(impl, fullSalt);
        if (mode == 0) {
            SimpleAccount_ECDSA(payable(accountAddr)).initialize(owner);
        } else if (mode == 1) {
            SimpleAccount_WOTS(payable(accountAddr)).initialize(owner);
        } else {
            revert("LegacySimpleAccountFactory: invalid mode");
        }

        emit AccountCreated(accountAddr, owner, salt);
    }

    function getAddress(address owner, uint256 salt, uint8 mode) public view returns (address) {
        address impl = _implFor(mode);
        return LibClone.predictDeterministicAddress(impl, _salt(owner, salt), address(this));
    }

    function _implFor(uint8 mode) internal view returns (address) {
        if (mode == 0) return ECDSA_IMPL;
        if (mode == 1) return WOTS_IMPL;
        revert("LegacySimpleAccountFactory: invalid mode");
    }

    function _salt(address owner, uint256 salt) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(owner, salt));
    }
}
