// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Test.sol";
import "../../../other-implementations/ecdsa/SimpleAccount_ECDSA.sol";
import {LegacySimpleAccountFactory} from "../../../other-implementations/LegacySimpleAccountFactory.sol";
import {IWotsCVerifier} from "../../../other-implementations/wots/IWotsCVerifier.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";
import {PackedUserOperation} from "account-abstraction/interfaces/PackedUserOperation.sol";
import {MessageHashUtils} from "@openzeppelin/contracts/utils/cryptography/MessageHashUtils.sol";
import {Initializable} from "@openzeppelin/contracts/proxy/utils/Initializable.sol";
import {EntryPointLib} from "kernel/sdk/TestBase/erc4337Util.sol";

contract RevertingTarget {
    error Boom();

    function boom() external pure {
        revert Boom();
    }
}

contract SimpleAccountECDSATest is Test {
    LegacySimpleAccountFactory factory;
    SimpleAccount_ECDSA account;
    IEntryPoint entryPoint;

    uint256 ownerPk0 = 0xA11CE;
    uint256 ownerPk1 = 0xB0B;
    uint256 ownerPk2 = 0xCAFE;
    uint256 ownerPk3 = 0xDEAD;

    address owner0;
    address owner1;
    address owner2;
    address owner3;

    address recipient = makeAddr("recipient");

    address constant ENTRYPOINT = 0x0000000071727De22E5E9d8BAf0edAc6f37da032;

    function setUp() public {
        owner0 = vm.addr(ownerPk0);
        owner1 = vm.addr(ownerPk1);
        owner2 = vm.addr(ownerPk2);
        owner3 = vm.addr(ownerPk3);

        entryPoint = IEntryPoint(ENTRYPOINT);
        vm.etch(ENTRYPOINT, hex"00");

        // ECDSA path doesn't use the WOTS verifier, so we pass a dummy address.
        factory = new LegacySimpleAccountFactory(entryPoint, IWotsCVerifier(address(0)));

        address accountAddr = factory.createAccount(owner0, 0, 0);
        account = SimpleAccount_ECDSA(payable(accountAddr));

        vm.deal(address(account), 100 ether);
    }

    // =========================================================================
    // Factory Tests
    // =========================================================================

    function test_FactoryDeploysAccount() public view {
        assertEq(account.owner(), owner0);
        assertEq(address(account.entryPoint()), ENTRYPOINT);
    }

    function test_FactoryDeterministicAddress() public view {
        address predicted = factory.getAddress(owner0, 0, 0);
        assertEq(predicted, address(account));
    }

    function test_FactoryDifferentSaltGivesDifferentAddress() public view {
        address addr0 = factory.getAddress(owner0, 0, 0);
        address addr1 = factory.getAddress(owner0, 1, 0);
        assertTrue(addr0 != addr1);
    }

    function test_FactoryDifferentOwnerGivesDifferentAddress() public {
        address addr1 = factory.getAddress(owner0, 0, 0);
        address addr2 = factory.getAddress(makeAddr("other"), 0, 0);
        assertTrue(addr1 != addr2);
    }

    function test_FactoryReturnsSameAddressIfAlreadyDeployed() public {
        address first = factory.createAccount(owner0, 0, 0);
        address second = factory.createAccount(owner0, 0, 0);
        assertEq(first, second);
    }

    function test_CannotReinitialize() public {
        vm.expectRevert(Initializable.InvalidInitialization.selector);
        account.initialize(makeAddr("attacker"));
    }

    // =========================================================================
    // Validation + Rotation Tests
    // =========================================================================

    function test_ValidateUserOpValidRotatesOwner() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(ownerPk0, userOpHash);

        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        uint256 validationData = account.validateUserOp(userOp, userOpHash, 0);

        assertEq(validationData, 0);
        assertEq(account.owner(), owner1);
    }

    function test_ValidateUserOpInvalidDoesNotRotate() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(0xBAD, userOpHash);

        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        uint256 validationData = account.validateUserOp(userOp, userOpHash, 0);

        assertEq(validationData, 1);
        assertEq(account.owner(), owner0); // unchanged
    }

    function test_ValidateUserOpRevertsOnBadCalldataLength() public {
        bytes memory callData = hex"aabbcc"; // < 24 bytes
        bytes memory sig = _sign(ownerPk0, keccak256("op-0"));

        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        vm.expectRevert("SimpleAccount: missing next owner");
        account.validateUserOp(userOp, keccak256("op-0"), 0);
    }

    function test_ValidateUserOpRevertsIfNotEntryPoint() public {
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(ownerPk0, keccak256("op-0"));
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(makeAddr("random"));
        vm.expectRevert("SimpleAccount: not from EntryPoint");
        account.validateUserOp(userOp, keccak256("op-0"), 0);
    }

    function test_ValidateUserOpRevertsOnZeroNextOwner() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", address(0));
        bytes memory sig = _sign(ownerPk0, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        vm.expectRevert("SimpleAccount: zero next owner");
        account.validateUserOp(userOp, userOpHash, 0);
    }

    function test_ValidateUserOpPaysPrefund() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(ownerPk0, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        uint256 prefund = 0.1 ether;
        uint256 epBalBefore = ENTRYPOINT.balance;

        vm.prank(ENTRYPOINT);
        account.validateUserOp(userOp, userOpHash, prefund);

        assertEq(ENTRYPOINT.balance, epBalBefore + prefund);
    }

    function test_ValidateUserOpRevertsIfPrefundTransferFails() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(ownerPk0, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        vm.expectRevert("SimpleAccount: prefund failed");
        account.validateUserOp(userOp, userOpHash, address(account).balance + 1);

        assertEq(account.owner(), owner0);
    }

    function test_ValidateUserOpEmitsRotation() public {
        bytes32 userOpHash = keccak256("op-0");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner1);
        bytes memory sig = _sign(ownerPk0, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        vm.expectEmit(true, true, false, false);
        emit SimpleAccount_ECDSA.OwnerRotated(owner0, owner1);
        account.validateUserOp(userOp, userOpHash, 0);
    }

    // =========================================================================
    // Execute Tests (no rotation — ECDSA now rotates in validateUserOp)
    // =========================================================================

    function test_ExecuteSendsETH() public {
        vm.prank(ENTRYPOINT);
        account.execute(recipient, 1 ether, "");
        assertEq(recipient.balance, 1 ether);
    }

    function test_OwnerCannotExecuteDirectly() public {
        vm.prank(owner0);
        vm.expectRevert("SimpleAccount: not from EntryPoint");
        account.execute(recipient, 0, "");
    }

    function test_OwnerCannotWithdrawDepositDirectly() public {
        vm.prank(owner0);
        vm.expectRevert("SimpleAccount: not from EntryPoint or account");
        account.withdrawDepositTo(payable(recipient), 0);
    }

    function test_OwnerCannotAddDepositDirectly() public {
        vm.prank(owner0);
        vm.expectRevert("SimpleAccount: not from EntryPoint or account");
        account.addDeposit();
    }

    function test_ExecuteDoesNotRotate() public {
        vm.prank(ENTRYPOINT);
        account.execute(recipient, 0, "");
        assertEq(account.owner(), owner0); // still the initial owner
    }

    function test_ExecuteRevertsIfNotEntryPoint() public {
        vm.prank(makeAddr("random"));
        vm.expectRevert("SimpleAccount: not from EntryPoint");
        account.execute(recipient, 0, "");
    }

    function test_ExecuteBubblesTargetRevert() public {
        RevertingTarget target = new RevertingTarget();

        vm.prank(ENTRYPOINT);
        vm.expectRevert(RevertingTarget.Boom.selector);
        account.execute(address(target), 0, abi.encodeCall(RevertingTarget.boom, ()));
    }

    function test_ExecuteBatch() public {
        address recipient2 = makeAddr("recipient2");

        address[] memory targets = new address[](2);
        targets[0] = recipient;
        targets[1] = recipient2;

        uint256[] memory values = new uint256[](2);
        values[0] = 1 ether;
        values[1] = 2 ether;

        bytes[] memory datas = new bytes[](2);
        datas[0] = "";
        datas[1] = "";

        vm.prank(ENTRYPOINT);
        account.executeBatch(targets, values, datas);

        assertEq(recipient.balance, 1 ether);
        assertEq(recipient2.balance, 2 ether);
    }

    function test_ExecuteBatchRevertsOnLengthMismatch() public {
        address[] memory targets = new address[](2);
        uint256[] memory values = new uint256[](1);
        bytes[] memory datas = new bytes[](2);

        vm.prank(ENTRYPOINT);
        vm.expectRevert("SimpleAccount: length mismatch");
        account.executeBatch(targets, values, datas);
    }

    // =========================================================================
    // Multi-Transaction Rotation Chain
    // =========================================================================

    /// @dev 3 sequential UserOps: owner0 -> owner1 -> owner2 -> owner3
    function test_MultiTxRotationChain() public {
        _validateAndRotate(ownerPk0, owner1, keccak256("op-0"));
        assertEq(account.owner(), owner1);

        _validateAndRotate(ownerPk1, owner2, keccak256("op-1"));
        assertEq(account.owner(), owner2);

        _validateAndRotate(ownerPk2, owner3, keccak256("op-2"));
        assertEq(account.owner(), owner3);
    }

    /// @dev After rotation, the old owner's signature must be rejected.
    function test_OldOwnerRejectedAfterRotation() public {
        _validateAndRotate(ownerPk0, owner1, keccak256("op-0"));
        assertEq(account.owner(), owner1);

        // owner0 tries to sign again — should fail and not rotate
        bytes32 userOpHash = keccak256("sneaky");
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", owner2);
        bytes memory oldSig = _sign(ownerPk0, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, oldSig);

        vm.prank(ENTRYPOINT);
        uint256 validationData = account.validateUserOp(userOp, userOpHash, 0);

        assertEq(validationData, 1);
        assertEq(account.owner(), owner1); // unchanged
    }

    /// @dev Rotating to self (same owner) should work.
    function test_RotateToSelf() public {
        _validateAndRotate(ownerPk0, owner0, keccak256("op-0"));
        assertEq(account.owner(), owner0);
    }

    // =========================================================================
    // Receive ETH
    // =========================================================================

    function test_ReceiveETH() public {
        uint256 balBefore = address(account).balance;
        vm.deal(makeAddr("sender"), 1 ether);
        vm.prank(makeAddr("sender"));
        (bool ok,) = address(account).call{value: 1 ether}("");
        assertTrue(ok);
        assertEq(address(account).balance, balBefore + 1 ether);
    }

    // =========================================================================
    // Helpers
    // =========================================================================

    /// @dev Build execute calldata with nextOwner appended as last 20 bytes
    function _buildExecuteCalldata(address to, uint256 value, bytes memory data, address nextOwner)
        internal
        view
        returns (bytes memory)
    {
        return abi.encodePacked(abi.encodeWithSelector(account.execute.selector, to, value, data), bytes20(nextOwner));
    }

    function _sign(uint256 pk, bytes32 userOpHash) internal pure returns (bytes memory) {
        bytes32 ethHash = MessageHashUtils.toEthSignedMessageHash(userOpHash);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, ethHash);
        return abi.encodePacked(r, s, v);
    }

    function _buildUserOp(bytes memory callData, bytes memory signature)
        internal
        view
        returns (PackedUserOperation memory)
    {
        return PackedUserOperation({
            sender: address(account),
            nonce: 0,
            initCode: "",
            callData: callData,
            accountGasLimits: bytes32(0),
            preVerificationGas: 0,
            gasFees: bytes32(0),
            paymasterAndData: "",
            signature: signature
        });
    }

    /// @dev Sign and validate a userOp from the current signer pk, rotating to nextOwner.
    function _validateAndRotate(uint256 signerPk, address nextOwner, bytes32 userOpHash) internal {
        bytes memory callData = _buildExecuteCalldata(recipient, 0, "", nextOwner);
        bytes memory sig = _sign(signerPk, userOpHash);
        PackedUserOperation memory userOp = _buildUserOp(callData, sig);

        vm.prank(ENTRYPOINT);
        uint256 validationData = account.validateUserOp(userOp, userOpHash, 0);
        assertEq(validationData, 0);
    }
}

contract SimpleAccountECDSAEntryPointExecutionTest is Test {
    IEntryPoint entryPoint;
    LegacySimpleAccountFactory factory;
    SimpleAccount_ECDSA account;

    uint256 ownerPk0 = 0xA11CE;
    address owner0;
    address owner1;

    function setUp() public {
        owner0 = vm.addr(ownerPk0);
        owner1 = vm.addr(0xB0B);

        entryPoint = IEntryPoint(EntryPointLib.deploy());
        factory = new LegacySimpleAccountFactory(entryPoint, IWotsCVerifier(address(0)));

        address accountAddr = factory.createAccount(owner0, 0, 0);
        account = SimpleAccount_ECDSA(payable(accountAddr));
        vm.deal(accountAddr, 10 ether);
    }

    function test_HandleOpsExecutionRevertStillRotatesOwner() public {
        RevertingTarget target = new RevertingTarget();
        bytes memory callData = abi.encodePacked(
            abi.encodeWithSelector(
                account.execute.selector, address(target), uint256(0), abi.encodeCall(RevertingTarget.boom, ())
            ),
            bytes20(owner1)
        );

        PackedUserOperation memory op = PackedUserOperation({
            sender: address(account),
            nonce: 0,
            initCode: "",
            callData: callData,
            accountGasLimits: bytes32(abi.encodePacked(uint128(1_000_000), uint128(1_000_000))),
            preVerificationGas: 100_000,
            gasFees: bytes32(abi.encodePacked(uint128(1), uint128(1))),
            paymasterAndData: "",
            signature: ""
        });

        bytes32 userOpHash = entryPoint.getUserOpHash(op);
        op.signature = _sign(ownerPk0, userOpHash);

        PackedUserOperation[] memory ops = new PackedUserOperation[](1);
        ops[0] = op;

        entryPoint.handleOps(ops, payable(makeAddr("beneficiary")));

        assertEq(account.owner(), owner1);
    }

    function _sign(uint256 pk, bytes32 userOpHash) internal pure returns (bytes memory) {
        bytes32 ethHash = MessageHashUtils.toEthSignedMessageHash(userOpHash);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(pk, ethHash);
        return abi.encodePacked(r, s, v);
    }
}
