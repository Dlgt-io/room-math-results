# Erdős #271 — Lean release rev 5 (frozen): how to verify it yourself

This archive contains the **frozen rev-5 Lean release, byte for byte**, plus a guide for checking it independently. Its status as of 2026-10-21 is given in §2. Nothing here claims more than that list.

## 1. Layout

| path | what it is |
|---|---|
| `rev5/` | The frozen release: 73 hash-pinned files plus `SHA256SUMS`. **Unmodified.** Its own `README.md` describes the package. |
| `rev5/SHA256SUMS` | sha256 `2d4f22165d1e3b60461315f8cd4e2d8e70d0498aaf1add86e4bd459ff4f090ef`. This is the release identifier. |
| `CHECKER_EVIDENCE.md` | Every external Lean-checker verdict for this release: job ids, environment hash, statement/proof hashes. |
| `extras/c9-glue/` | Statement and proof of the C\* gluing check (checker job `68fdc6fb`). |
| `extras/liminf-419/` | Self-contained single-term proof of the strong-covering liminf bound 419√3/384 (job `d5e58222`). |
| `extras/liminf-1675/` | Self-contained single-term proof of the smaller bound 1675√3/1536 (job `042a1cf7`). It is **not part of rev 5**; it was proposed for rev 6. |
| `extras/SHA256SUMS.extras` | Hashes of the `extras/` files and the two `.md` files. |

No `.olean` or other build outputs are included. The author's raw build logs (`rev5/logs/`, mentioned in `rev5/README.md`) are not part of the hash-pinned set, so they are not included either.

## 2. Status (honest, 2026-10-21)

| layer | status | by whom |
|---|---|---|
| Source integrity | ✅ `sha256sum -c SHA256SUMS` passes for all 73 files. The tree was reconstructed from the room notes by script, without hand transcription. The generated files (`LiminfCert3072.lean`, `LiminfCert49152.lean`, `Composed.lean`) were regenerated with the package's own scripts and match their pinned hashes. | Claude |
| Non-Lean audits | ✅ All pass on this exact copy: `grep_audit.sh` (no forbidden tokens in 38 files), `compose_check.py` (ALL OK), `test_check_axioms.py` (16 tests OK). | Claude |
| Full project build + strict axiom audit | ✅ **author-reported**: fresh-directory replay SUCCESS, strict audit 24/24, axioms only `propext`, `Classical.choice`, `Quot.sound`. | Grok (author environment) |
| Independent second-environment full build | ☐ **NOT DONE YET.** Claude's sandbox cannot reach the Mathlib cache, and its from-source Mathlib build was interrupted. **This is the open release gate. Running §3 on your own machine closes it.** | — |
| External checker (Delegate Lean checker, Lean/Mathlib 4.35.0) | ✅ 11 bundle jobs, the C\* gluing job and two single-term liminf jobs, all `verified` in one environment (`a82a2014…`). See `CHECKER_EVIDENCE.md`. | Grok, Claude |

**What "C\* is externally checked" means here ([EXT-chain]):** eight checker verdicts in one fixed environment join by modus ponens:
- the seven bundle statements B1, B5, B6, B7, B8a, B8b, B9;
- one gluing job proving (B1 → … → B9 → C9).

It is **not** one kernel check: a single-term version was tried and exceeds the checker's default heartbeat budget, about 483k against 200k (job `bb93cb63`). It is also **not** an axiom audit, since the checker reports no axioms. The axiom claim rests on the local `#print axioms` audit in §3.

**Not established by anything in this archive:** novelty, publication status, or that each Lean statement matches its paper wording. The theorem→Lean crosswalk and the paper reviews cover the last point.

## 3. Independent test (the step that is still open)

Requirements:
- Linux or macOS, `elan`, `git`, `curl`, `python3`, `sha256sum`;
- network access to GitHub and the Mathlib cache;
- about 8 GB RAM, about 10 GB disk.

```bash
cd rev5
sha256sum SHA256SUMS                       # must print 2d4f22165d1e3b60461315f8cd4e2d8e70d0498aaf1add86e4bd459ff4f090ef
sha256sum -c SHA256SUMS                    # all 73 files OK
chmod +x scripts/*.sh replay.sh
EXPECT_SUMS=2d4f22165d1e3b60461315f8cd4e2d8e70d0498aaf1add86e4bd459ff4f090ef \
LEAN_NUM_THREADS=2 scripts/replay_fresh.sh /tmp/e271-fresh
```

`replay_fresh.sh` does the following:
- copies only the 73 pinned files into a new directory;
- fetches Mathlib at commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake exe cache get`);
- builds all 38 modules;
- runs `scripts/Headline.lean` (`#check` and `#print axioms` for the 24 headline theorems);
- runs the strict audit and its tests, the grep audit and `compose_check`;
- re-verifies the hashes.

**Pass criterion:** `/tmp/e271-fresh/logs/SUCCESS.json` exists, with `"status": "SUCCESS"` and 24 parsed / 24 unique theorems. It is written only if every step passed.

Timing: with the Mathlib cache, a few minutes. Without the cache (Mathlib built from source), about 4 h on 2 cores. If Mathlib is already built in another project, pass `--deps-from <that project dir>`.

Please report these to the room:
- `logs/SUCCESS.json`;
- `logs/acceptance.json`;
- the `lean --version` line from `logs/env.log`;
- your OS and CPU.

## 4. Re-checking the external verdicts yourself (optional)

Each pair in `rev5/checker-bundles/` and `extras/*/` is self-contained: `import Mathlib` only, Lean/Mathlib 4.35.0. To compile one locally:

```lean
import Mathlib
theorem t : <contents of statement file> := <contents of proof file>
```

`b4` needs `set_option maxRecDepth 10000 in` in front. To check through the Delegate Lean checker instead, submit the statement and proof texts unchanged. The returned `statement_sha256` / `proof_sha256` must equal the hashes in `CHECKER_EVIDENCE.md`.
