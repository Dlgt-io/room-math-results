# Rev7 verification evidence

The exact formal-source manifest is `034a7b22416c2bca96c2d4d997c6d41ce34af74f943402dcbc51993614d3b8b8`. The [combined success receipt](SUCCESS.json) was written only after every required check passed. The source contains 86 manifest payloads. The [module-output record](module-outputs.json) lists all 43 matching project outputs: the solution library and its trusted Challenge module.

## Main theorem

The [trusted statement](../../lean/rev7/Challenge.lean) and [solution](../../lean/rev7/Solution.lean) both name `Erdos271.main_result`. The [comparator output](comparator/stdout.log) records the target export, acceptance by nanoda and Lean's default kernel, and the final success verdict. [Exit status](comparator/exit-code.txt) is zero and [standard error](comparator/stderr.log) is empty. The [environment record](comparator/environment.txt) identifies the input hashes, actual sandbox executable, non-root UID, and checker binary hashes.

The comparator independently validates only this main target. The [exact-name/axiom audit](acceptance.json) covers all 27 designated declarations. All [18 audit tests](audit-tests.log) passed with no skips. The [comparison record](comparison-and-acceptance.json) confirms that the earlier 26 printed declaration types and axiom reports match rev6 after line-ending normalization.

## Validator and sandbox controls

The [controls](controls/) include a valid proof, a different theorem statement, and a forbidden axiom. Their exit codes are respectively zero, one, and one. The negative verdicts must contain their prescribed rejection reasons, so an environment failure cannot count as a successful negative test. These fixture Lean files are deliberate validator inputs, not mathematical results.

The [sandbox control log](sandbox-controls.log) records non-root execution, zero effective and permitted capabilities, no-new-privileges, protected parent evidence, a writable build cache, and no external network route. Comparator and control evidence stay outside the proof-writable `.lake` directory.

## Execution and trust scope

The run used a clean disposable Linux container, a fresh official Lean 4.35.0 installation, and freshly fetched pinned Mathlib dependencies and public cache. All [nine dependency commits](dependency-pins.log) matched the lock file. No earlier project outputs or proof-writable dependency cache were reused. Comparator ran before any ordinary proof build. Later build and audit commands ran in a nonnetwork bubblewrap sandbox and could reuse only outputs produced during this same combined replay.

The [runtime context](run-context.json) distinguishes the proof sandbox from the outer container. The outer container's restrictions were relaxed to support nested bubblewrap, while comparator ran as a non-root user using the real sandbox. Lean and Mathlib were not independently rebuilt from source. The trusted statement and imported definitions still require mathematical review. These checks do not establish novelty or peer review.

The [export provenance](EXPORT_PROVENANCE.json) records raw and exported hashes. Only generic temporary build/toolchain paths were replaced by labels; mathematical output is unchanged. Existing compatibility/linter warnings and an inherited test-file resource warning remain visible in the logs. The [previous package manifest](package-SHA256SUMS-before-rev7) belongs to commit `59fe96c938d1f24777ccdc71e601ec4fdf9b5c52`, not to the updated package.
