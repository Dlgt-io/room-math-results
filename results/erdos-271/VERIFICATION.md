# Reproducing the formal results

## Rev7: main theorem and comparator

The exact abstract-matching target is [`Erdos271.main_result`](lean/rev7/Challenge.lean); its proof entry point is [`Solution.lean`](lean/rev7/Solution.lean). The trusted Challenge imports only [`Statement.lean`](lean/rev7/Statement.lean) and Mathlib. The [rev7 guide](lean/rev7/README.md) explains the inclusive count and unconditional `ENNReal` limsup.

As a non-root Linux user with elan and a working bubblewrap sandbox:

```bash
cd lean/rev7
sha256sum -c SHA256SUMS
EXPECT_SUMS=034a7b22416c2bca96c2d4d997c6d41ce34af74f943402dcbc51993614d3b8b8 \
  LEAN_NUM_THREADS=2 bash scripts/replay_fresh.sh /absolute/path/to/a/new-build
```

Start in a clean, trusted checking environment. The replay checks every dependency commit and invokes native Lean 4.35.0 comparator with its sandbox and independent nanoda kernel before any ordinary proof build. Subsequent full-project build, 27-name audit, 18 audit tests, and certificate/composition checks run in a nonnetwork bubblewrap sandbox. Source, checker binaries, and parent-owned evidence stay read-only to proof code; only `.lake` and temporary scratch space are writable. The comparator controls must accept a valid proof and reject a different statement and a forbidden axiom. `Challenge.lean` contains one intentional specification hole; it is excluded from the solution source scan and is never an allowed proof axiom.

The clean combined replay completed successfully at 23:18:55 UTC on October 31, 2026. This rev7 edition is dated November 1, 2026. The [success receipt](verification/rev7/SUCCESS.json), [comparison and acceptance record](verification/rev7/comparison-and-acceptance.json), [printed theorem types and axioms](verification/rev7/axioms.log), and [exact-name audit](verification/rev7/acceptance.json) record 27 unique audited declarations and 18 passing audit tests, with no skips. All 43 project modules, including the trusted Challenge, have matching build outputs.

The [main comparator log](verification/rev7/comparator/stdout.log) records statement comparison and acceptance by nanoda and Lean's default kernel. The [control inputs and verdicts](verification/rev7/controls/) and [sandbox controls](verification/rev7/sandbox-controls.log) record the validator checks. Comparator ran first; later build steps reused only outputs made inside this same fresh replay. All 26 earlier printed declaration types and axiom reports match rev6 after line-ending normalization. See the [evidence scope](verification/rev7/README.md) for runtime and dependency assumptions.

Rev7's formal-source manifest SHA-256 is `034a7b22416c2bca96c2d4d997c6d41ce34af74f943402dcbc51993614d3b8b8`. Rev5 and rev6 source trees, manifests, old manuscripts, and evidence are preserved; all 39 inherited `.lean` proof modules in rev7 are byte-identical to rev6. The [previous package manifest](verification/rev7/package-SHA256SUMS-before-rev7) also remains available. This update is prepared for the GitHub archive and does not claim a new research-room adoption or a submission elsewhere.

## Preserved rev5 and rev6 verification


The exact source trees are in [lean/rev5](lean/rev5/) and [lean/rev6](lean/rev6/). Run these commands in a Bash environment with Git, Python 3, and the Lean toolchain manager elan available. Network access is needed for the default dependency download/cache step. Lean uses the checked-in `lean-toolchain` and `lake-manifest.json`.

## Current independently checked release: rev 6

From the project directory:

```bash
cd lean/rev6
sha256sum -c SHA256SUMS
EXPECT_SUMS=78291fa4ca02d51370c4b2c56073ef58bb5f98d7553a7fa77c5fc156d2219c03 \
  LEAN_NUM_THREADS=2 bash scripts/replay_fresh.sh /absolute/path/to/a/new-rev6-build
```

Choose a destination that does not exist. The script copies only the 77 manifest payloads, builds all 39 project modules, audits exactly 26 theorem names and their transitive axioms, runs the 17 audit tests with the actual compiler transcript, scans sources, verifies bundle composition and the 1675 proof embedding, and rechecks source hashes. It writes `logs/SUCCESS.json` only after all steps pass. `scripts/Headline.lean` lists the audited declarations.

A successful checked run completed on 23 October 2026 at 12:42:29 UTC. Its [build log](verification/rev6/build.log), [printed types and axioms](verification/rev6/axioms.log), [strict audit](verification/rev6/acceptance.json), [tests](verification/rev6/audit-tests.log), and [success receipt](verification/rev6/SUCCESS.json) are included. The original 24 declaration types/axiom reports are byte-identical to the rev-5 run; see [comparison-and-acceptance.json](verification/comparison-and-acceptance.json).

## Preserved baseline: rev 5

Use the same command from `lean/rev5`, with a different nonexistent destination and `EXPECT_SUMS=2d4f22165d1e3b60461315f8cd4e2d8e70d0498aaf1add86e4bd459ff4f090ef`. It contains 73 manifest payloads and 38 project modules, with exactly 24 audited theorem names and 16 audit tests. Its independent replay completed on 22 October 2026 at 19:46:23 UTC. Evidence is in [verification/rev5](verification/rev5/).

## Source identities and scope

| Tree | SHA256 of SHA256SUMS | Project modules | Audited names |
|---|---|---:|---:|
| rev 5 | `2d4f22165d1e3b60461315f8cd4e2d8e70d0498aaf1add86e4bd459ff4f090ef` | 38 | 24 |
| rev 6 | `78291fa4ca02d51370c4b2c56073ef58bb5f98d7553a7fa77c5fc156d2219c03` | 39 | 26 |

Both use Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. All nine dependency commits were checked. The independent runs compiled the full project using pinned cached dependencies; Lean and Mathlib themselves were not rebuilt from source. All audited declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

The two names added to the rev-6 audit are `Erdos271.FiniteIntegrals.finite_weighted_integral_identity` and `Erdos271.Liminf1675.liminf_construction_1675`. The 1675 construction is separate from the preserved 419 construction.

The frozen source READMEs and [historical verifier documents](lean/archived-extras/) preserve their original status text. In particular, a rev-5 pending-build statement dated 21 October predates the successful independent replay, and rev-6's original README calls it a candidate. The later evidence above records the checks that were subsequently completed. The room adopted this exact rev-6 identity after those checks; rev 5 remains preserved. Logs referenced in those frozen READMEs are supplied under `verification/rev5/` and `verification/rev6/`, rather than inserted into the pinned trees.

Historical standalone checker inputs are in `lean/archived-extras/`; verify their separate manifest from that directory with `sha256sum -c extras/SHA256SUMS.extras`. That manifest is distinct from the two project manifests. Standalone checker verdicts, a full project build, and manual paper-to-formal correspondence review are distinct evidence.

The public logs preserve the original mathematical output. Only the test runner's absolute worktree path was replaced in the two audit-test logs; [export-provenance.json](verification/export-provenance.json) records original and exported hashes. Server launchers, host locations, account data, service status, caches, and compiled dependency artifacts are excluded. A successful formal build does not establish literature priority or replace specialist review of the manuscripts.
