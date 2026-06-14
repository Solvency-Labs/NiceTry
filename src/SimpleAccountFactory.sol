// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {SimpleAccount} from "./SimpleAccount.sol";
import {ISignatureVerifier} from "./Interfaces/ISignatureVerifier.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";
import {LibClone} from "solady/utils/LibClone.sol";

/// @title SimpleAccountFactory
/// @notice Deploys FORS-backed accounts as EIP-1167 minimal proxies pointing at
///         a single implementation contract.
contract SimpleAccountFactory {
    IEntryPoint public immutable ENTRY_POINT;
    ISignatureVerifier public immutable VERIFIER;
    address public immutable ACCOUNT_IMPL;

    event AccountCreated(address indexed account, address indexed owner, uint256 salt);

    constructor(IEntryPoint _entryPoint, ISignatureVerifier _verifier) {
        ENTRY_POINT = _entryPoint;
        VERIFIER = _verifier;
        ACCOUNT_IMPL = address(new SimpleAccount(_entryPoint, _verifier));
    }

    function createAccount(address owner, uint256 salt) external returns (address accountAddr) {
        bytes32 fullSalt = _salt(owner, salt);

        address predicted = LibClone.predictDeterministicAddress(ACCOUNT_IMPL, fullSalt, address(this));
        if (predicted.code.length > 0) return predicted;

        accountAddr = LibClone.cloneDeterministic(ACCOUNT_IMPL, fullSalt);
        SimpleAccount(payable(accountAddr)).initialize(owner);

        emit AccountCreated(accountAddr, owner, salt);
    }

    function getAddress(address owner, uint256 salt) public view returns (address) {
        return LibClone.predictDeterministicAddress(ACCOUNT_IMPL, _salt(owner, salt), address(this));
    }

    function _salt(address owner, uint256 salt) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(owner, salt));
    }
}
