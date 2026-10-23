#!/usr/bin/env bash
# Forbidden-token audit over all project sources (comments included, so any hit is reported for manual inspection).
cd "$(dirname "$0")/.."
pat='\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|ofReduceBool|Lean\.ofReduceBool|decide\s*\+native)\b'
files=$(find Audit -name '*.lean'; ls *.lean)
if grep -nE "$pat" $files; then echo "GREP AUDIT: hits above (inspect)"; exit 1; else echo "GREP AUDIT: no forbidden tokens in $(echo $files | wc -w) source files"; fi
