#!/usr/bin/env bash
# Run later replay steps without granting proof code access to sources, logs, or tools.
set -euo pipefail
cd "$(dirname "$0")/.."
[[ $(uname -s) == Linux && $(id -u) -ne 0 ]] || { echo 'FAIL: non-root Linux user required' >&2; exit 2; }
[[ $# -gt 0 ]] || { echo 'FAIL: command required' >&2; exit 2; }
sandbox_bwrap=$(command -v bwrap)
toolchain_bin=$(dirname "$(elan which lean)")
toolchain_root=$(cd "$toolchain_bin/.." && pwd)
[[ -d .lake && ! -L .lake ]] || { echo 'FAIL: a real project .lake directory is required' >&2; exit 2; }
exec "$sandbox_bwrap" --unshare-all --die-with-parent --new-session \
  --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /var --tmpfs /tmp \
  --ro-bind "$PWD" "$PWD" \
  --ro-bind "$toolchain_root" "$toolchain_root" \
  --bind "$PWD/.lake" "$PWD/.lake" --proc /proc --dev /dev \
  --dir /tmp/home --dir /tmp/runtime \
  --clearenv --setenv PATH "$toolchain_bin:/usr/local/bin:/usr/bin:/bin" \
  --setenv HOME /tmp/home --setenv XDG_RUNTIME_DIR /tmp/runtime \
  --setenv LANG C.UTF-8 --setenv TMPDIR /tmp \
  --setenv LEAN_NUM_THREADS "${LEAN_NUM_THREADS:-1}" --chdir "$PWD" -- "$@"
