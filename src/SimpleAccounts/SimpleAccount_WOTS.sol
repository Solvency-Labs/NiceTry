// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {BaseAccount} from "account-abstraction/core/BaseAccount.sol";
import {SIG_VALIDATION_SUCCESS, SIG_VALIDATION_FAILED} from "account-abstraction/core/Helpers.sol";
import {Exec} from "account-abstraction/utils/Exec.sol";
import {TokenCallbackHandler} from "account-abstraction/accounts/callback/TokenCallbackHandler.sol";
import {PackedUserOperation} from "account-abstraction/interfaces/PackedUserOperation.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";
import {Initializable} from "@openzeppelin/contracts/proxy/utils/Initializable.sol";
import {IWotsCVerifier} from "../Interfaces/IWotsCVerifier.sol";
import {WOTS_BLOB_LEN} from "../Verifiers/WotsCVerifier.sol";

/// @title SimpleAccount_WOTS
/// @notice ERC-4337 smart account with WOTS+C post-quantum signatures,
///         automatic main-signer rotation on every UserOp, and a pool of
///         pre-committed spare keys.
///
///         userOp.signature = [WOTS_BLOB_LEN bytes WOTS+C blob]
///         userOp.callData  = [... any call ...][20 bytes nextOwner]
contract SimpleAccount_WOTS is BaseAccount, TokenCallbackHandler, Initializable {
    // Spare-key state machine. Once tombstoned, an address can never be
    // re-registered; this avoids accidental reuse of leaked one-time keys.
    uint8 internal constant SPARE_NONE = 0;
    uint8 internal constant SPARE_ACTIVE = 1;
    uint8 internal constant SPARE_TOMBSTONE = 2;

    address public owner;
    IEntryPoint public immutable ENTRY_POINT;
    IWotsCVerifier public immutable VERIFIER;

    // Value is one of SPARE_NONE / SPARE_ACTIVE / SPARE_TOMBSTONE.
    mapping(address => uint8) public spareKeys;
    uint256 public spareKeyCount;

    event WotsAccountInitialized(IEntryPoint indexed entryPoint, address indexed owner, address indexed verifier);
    event OwnerRotated(address indexed previousOwner, address indexed newOwner);
    event SpareKeyAdded(address indexed key);
    event SpareKeyRemoved(address indexed key);
    event SpareKeyReplaced(address indexed oldKey, address indexed newKey);
    event SpareKeyConsumed(address indexed key);

    modifier onlyEntryPoint() {
        _requireFromEntryPoint();
        _;
    }

    constructor(IEntryPoint _entryPoint, IWotsCVerifier _verifier) {
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
        require(_owner != address(0), "WotsAccount: zero owner");
        owner = _owner;
        emit WotsAccountInitialized(entryPoint(), _owner, address(VERIFIER));
    }

    /// @inheritdoc BaseAccount
    function _validateSignature(PackedUserOperation calldata userOp, bytes32 userOpHash)
        internal
        virtual
        override
        returns (uint256 validationData)
    {
        require(userOp.signature.length == WOTS_BLOB_LEN, "WotsAccount: bad sig length");
        require(userOp.callData.length >= 24, "WotsAccount: missing next owner"); // 4 selector + 20 min

        address nextOwner = address(bytes20(userOp.callData[userOp.callData.length - 20:]));
        address recovered = VERIFIER.wrecover(userOp.signature, userOpHash);

        if (recovered == address(0)) {
            return SIG_VALIDATION_FAILED;
        }

        if (recovered == owner) {
            _rotateOwner(nextOwner);
            return SIG_VALIDATION_SUCCESS;
        }

        if (spareKeys[recovered] == SPARE_ACTIVE) {
            spareKeys[recovered] = SPARE_TOMBSTONE;
            unchecked {
                spareKeyCount--;
            }
            emit SpareKeyConsumed(recovered);
            _rotateOwner(nextOwner);
            return SIG_VALIDATION_SUCCESS;
        }

        return SIG_VALIDATION_FAILED;
    }

    function _payPrefund(uint256 missingAccountFunds) internal virtual override {
        if (missingAccountFunds > 0) {
            (bool ok,) = payable(msg.sender).call{value: missingAccountFunds}("");
            require(ok, "WotsAccount: prefund failed");
        }
    }

    function _requireFromEntryPoint() internal view override {
        require(msg.sender == address(entryPoint()), "WotsAccount: not from EntryPoint");
    }

    function _requireFromEntryPointOrSelf() internal view {
        require(
            msg.sender == address(entryPoint()) || msg.sender == address(this),
            "WotsAccount: not from EntryPoint or account"
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
        require(targets.length == values.length && values.length == datas.length, "WotsAccount: length mismatch");

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
        require(nextOwner != address(0), "WotsAccount: zero next owner");
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

    // =========================================================================
    // Spare-key pool management
    // =========================================================================

    /// @notice Add, remove, or replace a spare key.
    ///           - oldKey == 0, newKey != 0: add `newKey` (must be NONE)
    ///           - oldKey != 0, newKey == 0: tombstone `oldKey` (must be ACTIVE)
    ///           - oldKey != 0, newKey != 0: tombstone `oldKey`, add `newKey`
    ///           - both zero: reverts
    ///         Tombstoned and consumed addresses can never be re-added.
    function rotateSpareKey(address oldKey, address newKey) external onlyEntryPoint {
        require(oldKey != newKey, "WotsAccount: same address");
        require(newKey != owner, "WotsAccount: owner cannot be spare");

        if (oldKey != address(0)) {
            require(spareKeys[oldKey] == SPARE_ACTIVE, "WotsAccount: old not active");
            spareKeys[oldKey] = SPARE_TOMBSTONE;
        }

        if (newKey != address(0)) {
            require(spareKeys[newKey] == SPARE_NONE, "WotsAccount: new already touched");
            spareKeys[newKey] = SPARE_ACTIVE;
        }

        if (oldKey == address(0)) {
            unchecked {
                spareKeyCount++;
            }
            emit SpareKeyAdded(newKey);
        } else if (newKey == address(0)) {
            unchecked {
                spareKeyCount--;
            }
            emit SpareKeyRemoved(oldKey);
        } else {
            emit SpareKeyReplaced(oldKey, newKey);
        }
    }

    receive() external payable {}
}
