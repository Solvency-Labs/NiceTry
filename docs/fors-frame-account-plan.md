# FORS Frame Account Plan

## Current Slice

Implement a FORS-only EIP-8141 frame account as a separate account from the ERC-4337
`SimpleAccount`.

The VERIFY frame:

1. reads the frame transaction signature hash;
2. verifies the existing FORS signature against the current `owner`;
3. checks that the immediately next frame is a `SENDER` frame targeting this account;
4. checks that the next frame calls `rotateOwner(address)` with zero value;
5. rejects that rotation frame if it is part of an atomic batch.

The rotation itself is a dedicated `SENDER` frame. This keeps the signer rotation
outside later execution failures.

This first Solidity slice implements the account logic and leaves the actual
EIP-8141 opcode bridge as an adapter/runtime task. Current solc inline assembly
does not compile the draft custom opcodes directly.

## Opcode Adapter

Add a frame-aware runtime or proxy layer that supplies these hooks to the account
logic:

- transaction signature hash;
- frame count;
- current frame index;
- frame mode, target, value, atomic flag, calldata length, and calldata words;
- `APPROVE` with execution-and-payment scope after successful VERIFY validation.

The adapter must preserve the account address as `address(this)` for storage and
for the `rotateOwner(address)` target check.

## Later Execute Helper

Add an optional `execute(address target, uint256 value, bytes calldata data)` helper
after the rotation path is proven against a frame-transaction devnet/client.

That helper should be `onlySelf`, callable only by a later `SENDER` frame from the
account, and it must not weaken the current invariant: the VERIFY frame should still
require the immediately following frame to be `rotateOwner(address)`, and execution
must happen only in subsequent non-atomic frames.

The helper is ergonomic only. A frame transaction can already execute a user action
by adding later `SENDER` frames that target downstream contracts directly.
