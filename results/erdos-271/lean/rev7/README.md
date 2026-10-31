# Erdős #271 — abstract-matching statement and proof (rev7)

## Main theorem

For every set $S\subseteq\mathbb N_0$ that weakly covers every sufficiently large non-member as $z=2b-a$ with $a<b<z$,

$$
\limsup_{x\to\infty}\frac{|S\cap[0,x]|}{\sqrt x}\ge\sqrt{\frac{2\sqrt2}{\log(1+\sqrt2)}}.
$$

The limsup takes values in the nonnegative extended reals, so it can be infinite. There is no eventual upper-boundedness or decidability hypothesis. This is the same mathematical bound as rev6, with a direct formal counterpart of the paper abstract.

- **Read the target:** [`Challenge.lean`](Challenge.lean), theorem `Erdos271.main_result`.
- **Read the proof entry point:** [`Solution.lean`](Solution.lean), the same theorem name and statement.
- **Review the definitions:** [`Statement.lean`](Statement.lean), defining the inclusive count `F` and `WeaklyAP3Covering`. It imports only the required pinned Mathlib modules.
- **Read the bridge:** [`Abstract.lean`](Abstract.lean), relating the positive and inclusive counts, identifying the constants, and deriving the unconditional `ENNReal` conclusion from the preserved analytic proof.

`Challenge.lean` intentionally leaves the target unproved. It is a trusted specification for comparator, not proof evidence. `Solution.lean` does not import it. All solution dependencies are checked for permitted axioms; the challenge's intentional hole is never accepted as a solution axiom.

## Verify

Use a non-root Linux account with elan and a working bubblewrap (`bwrap`) sandbox. The pinned Lean 4.35.0 release supplies the native `lake comparator`, proof exporter, and `nanoda` checker. Mathlib is pinned by `lake-manifest.json` to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Network access is needed to fetch dependencies and their cache.

From this directory:

```bash
bash scripts/replay_fresh.sh /absolute/path/to/a/new-build
```

Use a clean, trusted checking environment that has not executed the proposed proof outside a sandbox. The replay copies only manifest payloads to a new directory, fetches trusted pinned dependencies, and runs comparator with nanoda before any ordinary proof build. It then builds the complete project and audits all 27 designated declarations inside a nonnetwork sandbox, with source files, checker binaries, and evidence read-only. Only the project `.lake` directory and temporary scratch space are writable. Comparator controls must accept a valid proof and reject both a different statement and an extra axiom. A success receipt is written only after every check passes. `replay.sh` is an alias for this fresh replay and requires a new output directory. If you supply `--deps-from`, use only a trusted dependency cache that proof code has never been allowed to modify.

For a standalone comparator run, prepare a fresh workspace with trusted dependencies and no project build outputs:

```bash
bash scripts/check_comparator.sh
bash scripts/test_comparator_negative.sh
```

The comparator configuration is [`comparator.json`](comparator.json). It permits only `propext`, `Quot.sound`, and `Classical.choice`. Scripts fail if the required checker or sandbox is unavailable. Main comparator evidence is saved under `logs/comparator/`; control evidence is saved under `logs/comparator-negative.*`. These directories are outside `.lake`, which proof builds can write. The sandbox controls also check read-only evidence, non-root execution, zero capabilities, no-new-privileges, and absence of an external network route. See the [verification guide](../../VERIFICATION.md) for published evidence and the exact manifest identity.

## Version scope

Rev5 and rev6, their manifests, manuscripts, and verification evidence remain preserved. The inherited proof modules in rev7 are unchanged; rev7 adds the statement interface and its validation. This revision is prepared for the GitHub archive. It does not claim research-room adoption, peer review, novelty clearance, or submission elsewhere. Human review of the trusted statement and its definitions remains essential; comparator checks formal correspondence and proof validity under its documented trust assumptions.
