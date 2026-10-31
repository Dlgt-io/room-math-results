#!/usr/bin/env bash
# Fresh-directory replay (round 34). Copies ONLY the files listed in SHA256SUMS into a NEW directory, so no
# project .olean, .lake/build or old log can be reused; fetches the pinned dependencies; builds; audits.
# Usage: scripts/replay_fresh.sh <new_dir> [--deps-from <dir containing .lake/packages>]
#   default: dependencies via `lake exe cache get` (network: GitHub + Mathlib cache).
#   --deps-from: use only a trusted dependency cache that proof code has never been allowed to modify.
# Optional: EXPECT_SUMS=<sha256 of SHA256SUMS> to pin the manifest itself.
# Writes <new_dir>/logs/SUCCESS.json only if every step passes. Requires elan, git, python3, sha256sum (and curl for cache).
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
SRC="$(cd "$(dirname "$0")/.." && pwd)"
[ $# -ge 1 ] || { echo "usage: $0 <new_dir> [--deps-from DIR]"; exit 2; }
DST="$1"; shift; DEPS=""
if [ "${1:-}" = "--deps-from" ]; then DEPS="$(cd "$2" && pwd)"; fi
[ -e "$DST" ] && { echo "FAIL: $DST already exists (must be fresh)"; exit 1; }
SUMS_SHA=$(sha256sum "$SRC/SHA256SUMS" | cut -d' ' -f1)
if [ -n "${EXPECT_SUMS:-}" ] && [ "$SUMS_SHA" != "$EXPECT_SUMS" ]; then echo "FAIL: SHA256SUMS is $SUMS_SHA, expected $EXPECT_SUMS"; exit 1; fi
( cd "$SRC" && sha256sum -c --quiet SHA256SUMS ) || { echo "FAIL: source hashes"; exit 1; }
mkdir -p "$DST"; DST="$(cd "$DST" && pwd)"
( cd "$SRC" && awk '{print $2}' SHA256SUMS | while read -r f; do mkdir -p "$DST/$(dirname "$f")"; cp -p "$f" "$DST/$f"; done; cp -p SHA256SUMS "$DST/" )
cd "$DST"; mkdir -p logs
[ ! -e .lake ] || { echo "FAIL: .lake present in fresh dir"; exit 1; }
echo "== fresh dir: $DST; source: $SRC; SHA256SUMS $SUMS_SHA; $(date -u +%FT%TZ)" | tee logs/env.log
sha256sum -c --quiet SHA256SUMS
lean --version | tee -a logs/env.log; lake --version | tee -a logs/env.log
if [ -n "$DEPS" ]; then
  mkdir -p .lake && cp -a "$DEPS/.lake/packages" .lake/packages
  echo "== deps copied from $DEPS/.lake/packages (dependencies only)" | tee -a logs/env.log
else
  ( time lake exe cache get ) 2>&1 | tee logs/cache-get.log
fi
python3 - <<'PY' | tee logs/dependency-pins.log
import json, subprocess
for package in json.load(open('lake-manifest.json'))['packages']:
    actual = subprocess.check_output(['git', '-C', '.lake/packages/' + package['name'], 'rev-parse', 'HEAD'], text=True).strip()
    if actual != package['rev']:
        raise SystemExit('FAIL: dependency pin ' + package['name'])
    print(package['name'] + ' ' + actual + ' (pinned)')
PY
[ ! -e .lake/build ] || { echo "FAIL: project build outputs present before build"; exit 1; }
bash scripts/check_comparator.sh > logs/comparator-summary.log 2>&1 || { cat logs/comparator-summary.log; echo "FAIL: comparator"; exit 1; }
bash scripts/test_comparator_negative.sh > logs/comparator-negative-summary.log 2>&1 || { cat logs/comparator-negative-summary.log; echo "FAIL: comparator negative controls"; exit 1; }
bash scripts/test_sandbox.sh > logs/sandbox-controls.log 2>&1 || { cat logs/sandbox-controls.log; echo "FAIL: replay sandbox controls"; exit 1; }
( time bash scripts/run_sandboxed.sh lake build ) > logs/build.log 2>&1 || { tail -30 logs/build.log; echo "FAIL: lake build"; exit 1; }
tail -4 logs/build.log
( time bash scripts/run_sandboxed.sh lake env lean scripts/Headline.lean ) > logs/axioms.log 2>&1 || { echo "FAIL: Headline"; exit 1; }
bash scripts/run_sandboxed.sh python3 scripts/check_axioms.py logs/axioms.log > logs/acceptance.json || { cat logs/acceptance.json; echo "FAIL: strict axiom audit"; exit 1; }
bash scripts/run_sandboxed.sh python3 scripts/test_check_axioms.py logs/axioms.log > logs/audit-tests.log 2>&1 || { cat logs/audit-tests.log; echo "FAIL: audit tests"; exit 1; }
bash scripts/run_sandboxed.sh bash scripts/grep_audit.sh | tee logs/grep-audit.log
bash scripts/run_sandboxed.sh python3 scripts/compose_check.py checker-bundles > logs/compose-check.log || { cat logs/compose-check.log; echo "FAIL: compose_check"; exit 1; }
bash scripts/run_sandboxed.sh python3 scripts/check_c1675.py > logs/check-c1675.log || { cat logs/check-c1675.log; echo "FAIL: check_c1675"; exit 1; }
sha256sum -c --quiet SHA256SUMS || { echo "FAIL: sources changed during replay"; exit 1; }
python3 - "$SUMS_SHA" <<'PY'
import json,sys,datetime
r=json.load(open('logs/acceptance.json'))
json.dump({'status':'SUCCESS','sha256sums':sys.argv[1],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
 'theorems':r['parsed_count'],'unique':r['unique_count'],'axioms_allowed':['propext','Classical.choice','Quot.sound'],
 'comparator':'PASS','comparator_theorems':['Erdos271.main_result'],
 'sandbox':True,'external_kernel':'nanoda','negative_controls':'PASS'},open('logs/SUCCESS.json','w'),indent=2)
PY
cat logs/SUCCESS.json; echo "== FRESH REPLAY DONE"
