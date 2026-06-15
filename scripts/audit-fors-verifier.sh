#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="src/Verifiers/ForsVerifier.sol"
RUNTIME="verity/NiceTry/Fors/Bridge/ForsRuntime.lean"
PINNED_IR="verity/artifacts/fors-verifier-runtime/ForsVerifier.irOptimized.yul"

EXPECTED_SOURCE_SHA256="aa6d44b994bdb5877863dd0400252649b03b48116f3da432bf4d932031436faf"
EXPECTED_RUNTIME_SHA256="7cd94b5cbbd6bea3a3b022438691ef1bf47ad92f72b3a7d08584f8edfb342a0b"
EXPECTED_IR_SHA256="531d8dd32a84ec56961bd4f220fce1466c533e40019e0729b97c6b328de21691"
EXPECTED_DEPLOYED_CODEHASH="0x41345cf3e55d977f792efdfee943698c695c544d01d28dc0a9412eb7e3fca113"

sha256_file() {
  openssl dgst -sha256 "$1" | awk '{print $NF}'
}

check_hash() {
  local label="$1"
  local expected="$2"
  local actual="$3"

  if [[ "$actual" != "$expected" ]]; then
    printf '%s hash mismatch\nexpected: %s\nactual:   %s\n' \
      "$label" "$expected" "$actual" >&2
    exit 1
  fi
  printf '%s: %s\n' "$label" "$actual"
}

cd "$ROOT"

check_hash "Solidity source" "$EXPECTED_SOURCE_SHA256" "$(sha256_file "$SOURCE")"
check_hash "Lean runtime" "$EXPECTED_RUNTIME_SHA256" "$(sha256_file "$RUNTIME")"
check_hash "Pinned solc optimized IR" "$EXPECTED_IR_SHA256" \
  "$(sha256_file "$PINNED_IR")"

regenerated_ir="$(mktemp)"
trap 'rm -f "$regenerated_ir"' EXIT
forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier irOptimized \
  > "$regenerated_ir"
if ! cmp -s "$PINNED_IR" "$regenerated_ir"; then
  printf 'Pinned optimized Yul differs from regenerated solc output:\n' >&2
  diff -u "$PINNED_IR" "$regenerated_ir" >&2 || true
  exit 1
fi
printf 'Pinned optimized Yul: byte-for-byte match\n'

check_hash "Regenerated solc optimized IR" "$EXPECTED_IR_SHA256" \
  "$(sha256_file "$regenerated_ir")"
check_hash "compiled deployed runtime codehash" "$EXPECTED_DEPLOYED_CODEHASH" \
  "$(cast keccak "$(forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier deployedBytecode)")"

declared_axioms="$(
  rg -n -P "^[\\t ]*axiom[\\t ]+[A-Za-z_][A-Za-z0-9_!?']*" \
    verity/NiceTry/Fors/Bridge --glob '*.lean'
)"
axiom_count="$(printf '%s\n' "$declared_axioms" | wc -l | tr -d ' ')"
if [[ "$axiom_count" != "2" ]]; then
  printf 'Expected exactly 2 Bridge axioms, found %s:\n%s\n' \
    "$axiom_count" "$declared_axioms" >&2
  exit 1
fi
printf 'Declared Bridge axioms:\n%s\n' "$declared_axioms"

cd verity
lake build NiceTry
lake env lean NiceTry/Fors/Bridge/Audit.lean
