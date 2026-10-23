#!/usr/bin/env bash
# One-command replay of THIS tree (reuses any existing .lake; for a clean replay use scripts/replay_fresh.sh <new_dir>): verifies hashes, fetches pinned Mathlib + its cache, builds, prints statements/axioms, audits sources.
# Requires: elan (https://github.com/leanprover/elan), git, curl, python3, sha256sum. Needs network for Mathlib.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd "$(dirname "$0")"
mkdir -p logs
echo "== host: $(uname -a)" | tee logs/env.log
echo "== date (UTC): $(date -u +%FT%TZ)" | tee -a logs/env.log
echo "== toolchain file: $(cat lean-toolchain)" | tee -a logs/env.log
sha256sum -c SHA256SUMS 2>&1 | tee logs/sha256-check.log
lean --version | tee -a logs/env.log
lake --version | tee -a logs/env.log
# 1. Mathlib (pinned by lake-manifest.json) and its prebuilt cache
( time lake exe cache get ) 2>&1 | tee logs/cache-get.log
git -C .lake/packages/mathlib rev-parse HEAD | tee -a logs/env.log
# 2. Build the full local closure (all project modules are compiled locally; only Mathlib/deps come from cache)
( time lake build ) 2>&1 | tee logs/build.log
# 3. Statements and transitive axioms of every headline theorem
( time lake env lean scripts/Headline.lean ) > logs/axioms.log 2>&1
cat logs/axioms.log
# 4. Acceptance checks
python3 scripts/check_axioms.py logs/axioms.log | tee logs/acceptance.log
python3 scripts/test_check_axioms.py logs/axioms.log 2>&1 | tee logs/audit-tests.log
bash scripts/grep_audit.sh | tee logs/grep-audit.log
python3 scripts/compose_check.py checker-bundles | tee logs/compose-check.log
echo "== REPLAY DONE"
