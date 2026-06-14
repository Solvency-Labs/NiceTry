# Frame Rotation Validation

The frame account treats signer rotation as part of validation. A verification
frame is accepted only if the immediately following frame is the dedicated
rotation frame for the same account.

Validation first checks the FORS signature against the current `owner`. If the
signature is valid, the account inspects the next frame and requires that it:

- uses `SENDER` mode;
- targets the account itself;
- sends `0` value;
- is not an atomic batch frame;
- has calldata exactly matching `rotateOwner(address)`; and
- passes a nonzero next owner address.

This means the transaction cannot be approved unless the next scheduled action
is a self-call that rotates the signer. Any user call must come after that
rotation frame.

Because of this constraint, this account is not a standalone paymaster/sponsor
account. A paymaster-style verification frame must be able to approve payment
for another sender under its own payment policy. This account's validation path
is instead bound to its own signer rotation flow: every successful verification
requires the next frame to rotate this account's owner. It may still self-pay
when used as the transaction sender, but it is not suitable as a generic payer
for other accounts.
