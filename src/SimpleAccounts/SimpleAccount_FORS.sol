// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {BaseAccount} from "account-abstraction/core/BaseAccount.sol";
import {SIG_VALIDATION_SUCCESS, SIG_VALIDATION_FAILED} from "account-abstraction/core/Helpers.sol";
import {Exec} from "account-abstraction/utils/Exec.sol";
import {TokenCallbackHandler} from "account-abstraction/accounts/callback/TokenCallbackHandler.sol";
import {PackedUserOperation} from "account-abstraction/interfaces/PackedUserOperation.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";
import {Initializable} from "@openzeppelin/contracts/proxy/utils/Initializable.sol";
import {IForsVerifier} from "../Interfaces/IForsVerifier.sol";
import {FORS_SIG_LEN} from "../Verifiers/ForsVerifier.sol";

/// @title SimpleAccount_FORS
/// @notice ERC-4337 smart account using standalone FORS as the primary signer.
///
///         userOp.signature = [FORS_SIG_LEN bytes FORS blob]
///         userOp.callData  = [... any call ...][20 bytes nextOwner]
contract SimpleAccount_FORS is BaseAccount, TokenCallbackHandler, Initializable {
    address public owner;
    IEntryPoint public immutable ENTRY_POINT;
    IForsVerifier public immutable VERIFIER;

    event ForsAccountInitialized(IEntryPoint indexed entryPoint, address indexed owner, address indexed verifier);
    event OwnerRotated(address indexed previousOwner, address indexed newOwner);

    constructor(IEntryPoint _entryPoint, IForsVerifier _verifier) {
        ENTRY_POINT = _entryPoint;
        VERIFIER = _verifier;
        owner = address(this);
        _disableInitializers();
    }

    /// @inheritdoc BaseAccount
    function entryPoint() public view virtual override returns (IEntryPoint) {
        return ENTRY_POINT;
    }

    /// @dev Called once by the factory after clone deployment.
    function initialize(address _owner) public virtual initializer {
        require(_owner != address(0), "ForsAccount: zero owner");
        owner = _owner;
        emit ForsAccountInitialized(entryPoint(), _owner, address(VERIFIER));
    }

    /// @inheritdoc BaseAccount
    function _validateSignature(PackedUserOperation calldata userOp, bytes32 userOpHash)
        internal
        virtual
        override
        returns (uint256 validationData)
    {
        require(userOp.callData.length >= 24, "ForsAccount: missing next owner"); // 4 selector + 20

        if (userOp.signature.length != FORS_SIG_LEN) {
            return SIG_VALIDATION_FAILED;
        }

        address nextOwner = address(bytes20(userOp.callData[userOp.callData.length - 20:]));
        address recovered = VERIFIER.recover(userOp.signature, userOpHash);

        if (recovered == address(0) || recovered != owner) {
            return SIG_VALIDATION_FAILED;
        }

        _rotateOwner(nextOwner);
        return SIG_VALIDATION_SUCCESS;
    }

    function _payPrefund(uint256 missingAccountFunds) internal virtual override {
        if (missingAccountFunds > 0) {
            (bool ok,) = payable(msg.sender).call{value: missingAccountFunds}("");
            require(ok, "ForsAccount: prefund failed");
        }
    }

    function _requireFromEntryPoint() internal view override {
        require(msg.sender == address(entryPoint()), "ForsAccount: not from EntryPoint");
    }

    function _requireFromEntryPointOrSelf() internal view {
        require(
            msg.sender == address(entryPoint()) || msg.sender == address(this),
            "ForsAccount: not from EntryPoint or account"
        );
    }

    /// @inheritdoc BaseAccount
    function execute(address target, uint256 value, bytes calldata data) external override {
        _requireForExecute();

        bool ok = Exec.call(target, value, data, gasleft());
        if (!ok) {
            Exec.revertWithReturnData();
        }
    }

    /// @notice Backward-compatible batch ABI kept for existing callers.
    ///         The upstream BaseAccount batch ABI is executeBatch(Call[]).
    function executeBatch(address[] calldata targets, uint256[] calldata values, bytes[] calldata datas) external {
        _requireForExecute();
        require(targets.length == values.length && values.length == datas.length, "ForsAccount: length mismatch");

        for (uint256 i = 0; i < targets.length; i++) {
            bool ok = Exec.call(targets[i], values[i], datas[i], gasleft());
            if (!ok) {
                if (targets.length == 1) {
                    Exec.revertWithReturnData();
                } else {
                    revert ExecuteError(i, Exec.getReturnData(0));
                }
            }
        }
    }

    function _rotateOwner(address nextOwner) internal {
        require(nextOwner != address(0), "ForsAccount: zero next owner");
        address previous = owner;
        owner = nextOwner;
        emit OwnerRotated(previous, nextOwner);
    }

    /// @notice Check this account's deposit in the EntryPoint.
    function getDeposit() public view virtual returns (uint256) {
        return entryPoint().balanceOf(address(this));
    }

    /// @notice Deposit more funds for this account in the EntryPoint.
    function addDeposit() public payable {
        _requireFromEntryPointOrSelf();
        entryPoint().depositTo{value: msg.value}(address(this));
    }

    /// @notice Withdraw funds from this account's EntryPoint deposit.
    function withdrawDepositTo(address payable withdrawAddress, uint256 amount) public virtual {
        _requireFromEntryPointOrSelf();
        entryPoint().withdrawTo(withdrawAddress, amount);
    }

    receive() external payable {}
}
