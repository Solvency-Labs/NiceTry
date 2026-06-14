import NiceTry.Fors.Bridge.Phase4
import NiceTry.Fors.Proofs.Basic

/-!
# FORS verifier audit

Run with:

```bash
lake env lean NiceTry/Fors/Bridge/Audit.lean
```

This file is intentionally not a Lake root, so ordinary builds stay quiet while
reviewers retain a stable command for checking the exported theorem and its
assumptions.
-/

#check NiceTry.Fors.Bridge.phase4_forsRefines
#check NiceTry.Fors.Proofs.Basic.legit_raw_signature_recovers_expected_address

#print axioms NiceTry.Fors.Bridge.phase4_forsRefines
#print axioms NiceTry.Fors.Bridge.dispatcher_routes_to_recover
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_size
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_get!
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_eq_empty
#print axioms NiceTry.Fors.Bridge.uint256_toByteArray_size
#print axioms NiceTry.Fors.Bridge.uint256_toByteArray_roundtrip
#print axioms NiceTry.Fors.Bridge.ffi_kec_lt
#print axioms NiceTry.Fors.Proofs.Basic.legit_raw_signature_recovers_expected_address
