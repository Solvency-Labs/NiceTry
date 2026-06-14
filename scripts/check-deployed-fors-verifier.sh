#!/usr/bin/env bash
set -euo pipefail

if [[ "$#" -ne 2 ]]; then
  printf 'Usage: %s RPC_URL VERIFIER_ADDRESS\n' "$0" >&2
  exit 2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RPC_URL="$1"
VERIFIER_ADDRESS="$2"

EXPECTED_SOURCE_SHA256="aa6d44b994bdb5877863dd0400252649b03b48116f3da432bf4d932031436faf"
EXPECTED_IR_SHA256="531d8dd32a84ec56961bd4f220fce1466c533e40019e0729b97c6b328de21691"
EXPECTED_DEPLOYED_CODEHASH="0x41345cf3e55d977f792efdfee943698c695c544d01d28dc0a9412eb7e3fca113"

sha256_file() {
  openssl dgst -sha256 "$1" | awk '{print $NF}'
}

sha256_stdin() {
  openssl dgst -sha256 | awk '{print $NF}'
}

fail_mismatch() {
  local label="$1"
  local expected="$2"
  local actual="$3"
  printf '%s mismatch\nexpected: %s\nactual:   %s\n' \
    "$label" "$expected" "$actual" >&2
  exit 1
}

cd "$ROOT"

source_hash="$(sha256_file src/Verifiers/ForsVerifier.sol)"
[[ "$source_hash" == "$EXPECTED_SOURCE_SHA256" ]] ||
  fail_mismatch "Solidity source hash" "$EXPECTED_SOURCE_SHA256" "$source_hash"

ir_hash="$(
  forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier irOptimized |
    sha256_stdin
)"
[[ "$ir_hash" == "$EXPECTED_IR_SHA256" ]] ||
  fail_mismatch "optimized IR hash" "$EXPECTED_IR_SHA256" "$ir_hash"

compiled_code="$(
  forge inspect src/Verifiers/ForsVerifier.sol:ForsVerifier deployedBytecode |
    tr -d '[:space:]' |
    tr '[:upper:]' '[:lower:]'
)"
compiled_codehash="$(cast keccak "$compiled_code")"
[[ "$compiled_codehash" == "$EXPECTED_DEPLOYED_CODEHASH" ]] ||
  fail_mismatch \
    "compiled deployed runtime codehash" \
    "$EXPECTED_DEPLOYED_CODEHASH" \
    "$compiled_codehash"

deployed_code="$(
  cast code "$VERIFIER_ADDRESS" --rpc-url "$RPC_URL" |
    tr -d '[:space:]' |
    tr '[:upper:]' '[:lower:]'
)"
if [[ -z "$deployed_code" || "$deployed_code" == "0x" ]]; then
  printf 'No contract code found at %s\n' "$VERIFIER_ADDRESS" >&2
  exit 1
fi

deployed_codehash="$(cast keccak "$deployed_code")"
[[ "$deployed_code" == "$compiled_code" ]] ||
  fail_mismatch \
    "deployed bytecode" \
    "$compiled_codehash" \
    "$deployed_codehash"

printf 'FORS verifier deployment matches the pinned artifact.\n'
printf 'address:  %s\n' "$VERIFIER_ADDRESS"
printf 'codehash: %s\n' "$deployed_codehash"
printf 'bytes:    %s\n' "$(((${#deployed_code} - 2) / 2))"
