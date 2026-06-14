#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="src/Verifiers/ForsVerifier.sol"
RUNTIME="verity/NiceTry/Fors/Bridge/ForsRuntime.lean"

EXPECTED_SOURCE_SHA256="aa6d44b994bdb5877863dd0400252649b03b48116f3da432bf4d932031436faf"
EXPECTED_RUNTIME_SHA256="ae3412b2f7fb063938456db4b328a407e0061f9f447f56177442f71d0d91507e"
EXPECTED_IR_SHA256="531d8dd32a84ec56961bd4f220fce1466c533e40019e0729b97c6b328de21691"

sha256_file() {
  openssl dgst -sha256 "$1" | awk '{print $NF}'
}

sha256_stdin() {
  openssl dgst -sha256 | awk '{print $NF}'
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
check_hash "solc optimized IR" "$EXPECTED_IR_SHA256" \
  "$(forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier irOptimized | sha256_stdin)"

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
