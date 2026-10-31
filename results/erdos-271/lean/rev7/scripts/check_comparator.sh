#!/usr/bin/env bash
# From any directory: bash results/erdos-271/lean/rev7/scripts/check_comparator.sh
# Linux + Lean v4.35.0 + bubblewrap required. Evidence stays outside writable .lake.
# This invokes Lake's native comparator with its sandbox and nanoda external kernel.
set -euo pipefail
cd "$(dirname "$0")/.."
evidence=logs/comparator
mkdir -p "$evidence"

fail() { printf 'FAIL: %s\n' "$*" >&2; exit 2; }
[[ $(uname -s) == Linux ]] || fail 'native comparator sandbox requires Linux'
[[ $(id -u) -ne 0 ]] || fail 'run comparator as a non-root user'
[[ ! -e .lake/build ]] || fail 'project build outputs already exist; use the fresh replay'
[[ $(cat lean-toolchain) == leanprover/lean4:v4.35.0 ]] || fail 'unexpected Lean toolchain'
command -v elan >/dev/null || fail 'elan is required to locate the pinned toolchain binaries'
command -v lake >/dev/null || fail 'lake is unavailable'
toolchain_bin=$(dirname "$(elan which lean)")
export PATH="$toolchain_bin:$PATH"
[[ $(lean --version) == *'4.35.0'* ]] || fail 'Lean v4.35.0 is unavailable'
command -v bwrap >/dev/null || fail 'bubblewrap is unavailable'
export COMPARATOR_BWRAP=$(command -v bwrap)
[[ -x "$toolchain_bin/nanoda_bin" ]] || fail 'bundled nanoda_bin is unavailable in the pinned toolchain'
command -v sha256sum >/dev/null || fail 'sha256sum is unavailable'
[[ -f lake-manifest.json && -f Challenge.lean && -f Solution.lean ]] || fail 'manifest, Challenge, or Solution is missing'

{
  date -u '+UTC %Y-%m-%dT%H:%M:%SZ'
  lean --version
  lake --version
  id -u
  bwrap --version
  stat -c '%a %U %G' "$COMPARATOR_BWRAP"
  printf 'COMPARATOR_BWRAP=%s\n' "$COMPARATOR_BWRAP"
  command -v nanoda_bin
  sha256sum "$COMPARATOR_BWRAP" "$toolchain_bin/nanoda_bin" \
    "$toolchain_bin/lean" "$toolchain_bin/lake" "$toolchain_bin/leanexport" "$toolchain_bin/leanchecker"
  sha256sum lean-toolchain lake-manifest.json comparator.json Challenge.lean Solution.lean Statement.lean Abstract.lean
} > "$evidence/environment.txt"

set +e
lake comparator --config comparator.json > "$evidence/stdout.log" 2> "$evidence/stderr.log"
status=$?
set -e
printf '%s\n' "$status" > "$evidence/exit-code.txt"
if [[ $status -ne 0 ]]; then
  printf 'FAIL: comparator exit %s; see %s/stdout.log and stderr.log\n' "$status" "$evidence" >&2
  exit "$status"
fi
grep -Fq 'nanoda kernel accepts the solution' "$evidence/stdout.log" || fail 'nanoda acceptance is missing from the comparator log'
grep -Fq 'Your solution is okay!' "$evidence/stdout.log" || fail 'comparator acceptance is missing from the log'
! grep -Fq 'Sandbox disabled' "$evidence/stderr.log" || fail 'comparator sandbox was disabled'
printf 'PASS: sandboxed comparator and nanoda; evidence: %s\n' "$evidence"
