#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p logs
probe=logs/.sandbox-protected-probe
[[ ! -e "$probe" ]] || { echo 'FAIL: sandbox probe already exists' >&2; exit 2; }
printf 'protected\n' > "$probe"
trap 'rm -f "$probe"' EXIT
bash scripts/run_sandboxed.sh python3 - <<'PY'
import errno, os, pathlib, socket
assert os.getuid() != 0
status = dict(line.split(':', 1) for line in pathlib.Path('/proc/self/status').read_text().splitlines() if ':' in line)
assert int(status['CapEff'].strip(), 16) == 0
assert int(status['CapPrm'].strip(), 16) == 0
assert status['NoNewPrivs'].strip() == '1'
assert pathlib.Path('logs/.sandbox-protected-probe').read_text() == 'protected\n'
try:
    pathlib.Path('logs/.sandbox-protected-probe').write_text('changed')
except OSError as exc:
    assert exc.errno in (errno.EROFS, errno.EACCES, errno.EPERM)
else:
    raise SystemExit('FAIL: parent evidence directory is writable')
pathlib.Path('.lake/sandbox-write-probe').write_text('allowed')
assert os.environ['HOME'] == '/tmp/home'
assert os.environ['XDG_RUNTIME_DIR'] == '/tmp/runtime'
assert not pathlib.Path('/run/docker.sock').exists()
assert not pathlib.Path('/var/run/docker.sock').exists()
with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
    try:
        sock.connect(('192.0.2.1', 9))
    except OSError as exc:
        assert exc.errno in (errno.ENETUNREACH, errno.EHOSTUNREACH)
    else:
        raise SystemExit('FAIL: external network route is available')
print('PASS: non-root, zero capabilities, no-new-privileges, read-only evidence, writable .lake, no external route')
PY
[[ $(cat "$probe") == protected ]] || { echo 'FAIL: protected probe changed' >&2; exit 1; }
