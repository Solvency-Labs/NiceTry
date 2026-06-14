// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

interface ISignatureVerifier {
    /// @notice Verify a signature blob and recover the address that signed it.
    /// @param sig The signature blob. The concrete verifier defines the layout.
    /// @param digest The 32-byte message digest being verified.
    /// @return signer The recovered signer address, or address(0) on failure.
    function recover(bytes calldata sig, bytes32 digest) external view returns (address signer);
}
