// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import "forge-std/Script.sol";
import "../src/SimpleAccountFactory.sol";
import "../src/Verifiers/ForsVerifier.sol";
import {ISignatureVerifier} from "../src/Interfaces/ISignatureVerifier.sol";
import {IEntryPoint} from "account-abstraction/interfaces/IEntryPoint.sol";

contract Deploy is Script {
    address constant ENTRYPOINT_V07 = 0x0000000071727De22E5E9d8BAf0edAc6f37da032;

    function run() external {
        address owner = 0xf83EE532e16f2998358f93a19DE6d7F6E7d146a4;
        vm.startBroadcast(owner);

        ForsVerifier forsVerifier = new ForsVerifier();

        SimpleAccountFactory factory =
            new SimpleAccountFactory(IEntryPoint(ENTRYPOINT_V07), ISignatureVerifier(address(forsVerifier)));

        console.log("ForsVerifier  deployed at:  ", address(forsVerifier));
        console.log("Factory       deployed at:  ", address(factory));
        console.log("Account implementation at: ", factory.ACCOUNT_IMPL());
        console.log("EntryPoint:                 ", ENTRYPOINT_V07);

        vm.stopBroadcast();
    }
}

