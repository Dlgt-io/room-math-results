#!/usr/bin/env bash
# Linux: bash results/erdos-271/lean/rev7/scripts/test_comparator_negative.sh
# Exercises Lake's native comparator, its bwrap sandbox, and nanoda on tiny controls.
set -euo pipefail
cd "$(dirname "$0")/.."
[[ $(uname -s) == Linux ]] || { echo 'FAIL: Linux required' >&2; exit 2; }
[[ $(id -u) -ne 0 ]] || { echo 'FAIL: run comparator as a non-root user' >&2; exit 2; }
[[ $(cat lean-toolchain) == leanprover/lean4:v4.35.0 ]] || { echo 'FAIL: wrong toolchain' >&2; exit 2; }
command -v elan >/dev/null && command -v lake >/dev/null && command -v bwrap >/dev/null || {
  echo 'FAIL: elan, lake, or bwrap unavailable' >&2; exit 2;
}
toolchain_bin=$(dirname "$(elan which lean)")
export PATH="$toolchain_bin:$PATH"
export COMPARATOR_BWRAP=$(command -v bwrap)
[[ -x "$toolchain_bin/nanoda_bin" ]] || { echo 'FAIL: bundled nanoda_bin unavailable' >&2; exit 2; }
mkdir -p logs
evidence=$(mktemp -d "$PWD/logs/comparator-negative.XXXXXX")
printf 'Evidence: %s\n' "$evidence"

make_project() {
  local kind=$1 dir=$evidence/$1
  mkdir -p "$dir"
  cp lean-toolchain "$dir/lean-toolchain"
  cat > "$dir/lakefile.toml" <<'EOF'
name = "comparatorControl"
defaultTargets = ["Challenge", "Solution"]
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
EOF
  cat > "$dir/lake-manifest.json" <<'EOF'
{"version":"1.3.0","packagesDir":".lake/packages","packages":[],"name":"comparatorControl","lakeDir":".lake","fixedToolchain":false}
EOF
  cat > "$dir/comparator.json" <<'EOF'
{"challenge_module":"Challenge","solution_module":"Solution","theorem_names":["fixture"],"permitted_axioms":["propext","Quot.sound","Classical.choice"],"external_kernels":{"nanoda":["nanoda_bin"]}}
EOF
  printf 'theorem fixture : True := by sorry\n' > "$dir/Challenge.lean"
  case $kind in
    valid) printf 'theorem fixture : True := by trivial\n' > "$dir/Solution.lean" ;;
    mismatch) printf 'theorem fixture : (1 : Nat) = 1 := by rfl\n' > "$dir/Solution.lean" ;;
    forbidden_axiom) printf 'axiom fixtureAxiom : True\ntheorem fixture : True := fixtureAxiom\n' > "$dir/Solution.lean" ;;
  esac
}

for kind in valid mismatch forbidden_axiom; do
  make_project "$kind"
  set +e
  (cd "$evidence/$kind" && lake comparator --config comparator.json) > "$evidence/$kind/stdout.log" 2> "$evidence/$kind/stderr.log"
  status=$?
  set -e
  printf '%s\n' "$status" > "$evidence/$kind/exit-code.txt"
  case "$kind:$status" in
    valid:0|mismatch:1|forbidden_axiom:1) ;;
    *) printf 'FAIL: %s returned %s; inspect %s\n' "$kind" "$status" "$evidence/$kind" >&2; exit 1 ;;
  esac
done
grep -Fq 'nanoda kernel accepts the solution' "$evidence/valid/stdout.log" || { echo 'FAIL: nanoda did not accept valid control' >&2; exit 1; }
grep -Fq 'Your solution is okay!' "$evidence/valid/stdout.log" || { echo 'FAIL: valid control not accepted' >&2; exit 1; }
grep -Fq 'Challenge and solution theorem statement do not match' "$evidence/mismatch/stderr.log" || { echo 'FAIL: mismatch rejection reason not confirmed' >&2; exit 1; }
grep -Fq 'Illegal axiom detected' "$evidence/forbidden_axiom/stderr.log" || { echo 'FAIL: forbidden axiom rejection reason not confirmed' >&2; exit 1; }
printf 'PASS: valid proof accepted; statement mismatch and forbidden axiom rejected\n'
