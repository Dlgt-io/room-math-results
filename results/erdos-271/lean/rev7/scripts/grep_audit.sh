#!/usr/bin/env bash
# Forbidden-token audit over all project sources (comments included, so any hit is reported for manual inspection).
cd "$(dirname "$0")/.."
pat='\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|ofReduceBool|Lean\.ofReduceBool|decide\s*\+native)\b'
files=$(find Audit -name '*.lean'; ls *.lean | grep -v '^Challenge.lean$')
if [ "$(grep -c '^  sorry$' Challenge.lean)" -ne 1 ] || \
    sed '/^  sorry$/d' Challenge.lean | grep -nE "$pat"; then
  echo "GREP AUDIT: Challenge must contain exactly its one intentional target hole"
  exit 1
fi
if grep -nE "$pat" $files; then echo "GREP AUDIT: hits above (inspect)"; exit 1; else echo "GREP AUDIT: no forbidden tokens in $(echo $files | wc -w) source files"; fi
