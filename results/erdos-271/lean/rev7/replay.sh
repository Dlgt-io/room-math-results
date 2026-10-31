#!/usr/bin/env bash
# Rev7 always starts from a fresh directory; an inherited writable build cache is not trusted.
set -euo pipefail
cd "$(dirname "$0")"
[[ $# -ge 1 ]] || { echo 'usage: bash replay.sh /absolute/path/to/a/new-build' >&2; exit 2; }
exec bash scripts/replay_fresh.sh "$@"
