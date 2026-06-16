import NiceTry.Fors.Bridge.ReviewSurface

/-!
# FORS verifier audit

Run with:

```bash
lake env lean NiceTry/Fors/Bridge/Audit.lean
```

This file gives reviewers a stable command for checking the simplified review
surface and the assumptions below it.
-/

#check NiceTry.Fors.Bridge.pinned_yul_is_checked_runtime
#check NiceTry.Fors.Bridge.checked_runtime_matches_recover_model
#check NiceTry.Fors.Bridge.pinned_yul_runtime_matches_recover_model
#check NiceTry.Fors.Bridge.legitimate_fors_signature_recovers_expected_address

#check NiceTry.Fors.Bridge.phase4_forsRefines
#check NiceTry.Fors.Bridge.parse_pinned_fors_runtime
#check NiceTry.Fors.Bridge.pinned_optimized_yul_refines
#check NiceTry.Fors.Proofs.Basic.legit_raw_signature_recovers_expected_address

#print axioms NiceTry.Fors.Bridge.pinned_yul_is_checked_runtime
#print axioms NiceTry.Fors.Bridge.checked_runtime_matches_recover_model
#print axioms NiceTry.Fors.Bridge.pinned_yul_runtime_matches_recover_model
#print axioms NiceTry.Fors.Bridge.legitimate_fors_signature_recovers_expected_address

#print axioms NiceTry.Fors.Bridge.phase4_forsRefines
#print axioms NiceTry.Fors.Bridge.parse_pinned_fors_runtime
#print axioms NiceTry.Fors.Bridge.pinned_optimized_yul_refines
#print axioms NiceTry.Fors.Bridge.dispatcher_routes_to_recover
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_size
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_get!
#print axioms NiceTry.Fors.Bridge.ffi_zeroes_eq_empty
#print axioms NiceTry.Fors.Bridge.uint256_toByteArray_size
#print axioms NiceTry.Fors.Bridge.uint256_toByteArray_roundtrip
#print axioms NiceTry.Fors.Bridge.ffi_kec_lt
#print axioms NiceTry.Fors.Proofs.Basic.legit_raw_signature_recovers_expected_address
