# Covering bounds and constructions related to Erdős Problem #271

This package collects public review drafts, formal proof sources, finite certificates, and verification evidence produced in the Delegate room “Erdős Problem #271 — Stanley sequences”. It is intended to make the work easy to inspect and reproduce. These results do **not** solve Erdős Problem #271.

## Three headline results

Paper 1 proves one universal lower bound. Paper 2 gives two separate strong-covering constructions. The constants below concern the normalized counting function $F_A(x)/\sqrt{x}$, where $F_A(x)=|A\cap[0,x]|$ includes $0$ when $0\in A$.

| Result | Applies to | Cited comparison bound | Our result | Paper |
|---|---|---|---|---|
| Universal limsup lower bound | Every weak forward covering, including Stanley sequences | Dai–Chen: $\approx1.774153391$ | At least $\sqrt{2\sqrt2/\log(1+\sqrt2)}\approx1.791399633$ | Paper 1 |
| Smaller limsup construction | One explicit strong forward covering | Fang: $8/\sqrt5\approx3.577708764$ | Exactly $17/6\approx2.833333333$ | Paper 2 |
| Smaller liminf construction | A different explicit strong forward covering | Kiss–Sándor–Yang: $2$ | At most $419\sqrt3/384\approx1.889920022$; separate refinement: at most $1675\sqrt3/1536\approx1.888792385$ | Paper 2 |

- A larger universal lower bound is the improvement in the first row.
- Smaller construction constants are the improvements in the other rows.
- The two constructions use different sets and are not Stanley sequences.
- The $1.888792385$ refinement belongs to the third result. It uses another set and a separate certificate; it is not a fourth headline result or a replacement for the original construction based on the $416$-element certificate.

A weak forward arithmetic-progression covering represents every sufficiently large integer outside $A$ as $2b-a$ with $0\le a<b$ in $A$. A strong covering represents every sufficiently large integer, including members of $A$.

Dai–Chen is the cited comparison for Stanley sequences; Paper 1 proves the larger constant for the wider class of weak coverings. See [Paper 1, Section 7](manuscripts/Erdos271_Weighted_Covering_Review_v2.7.tex#L386-L409) for its evaluation and [Paper 2's comparison paragraph](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex#L66-L71) for Fang and Kiss–Sándor–Yang. These are cited comparison bounds; the package does not claim an exhaustive literature assessment or optimal constants.

## Formal entry points

| Result | Paper theorem | Canonical Lean entry | Verification evidence |
|---|---|---|---|
| Universal limsup lower bound | [Paper 1, Theorem 1.2: limsup conclusion](manuscripts/Erdos271_Weighted_Covering_Review_v2.7.tex#L66-L74) | [`Erdos271.main_result`](lean/rev7/Solution.lean#L6-L10); [trusted target](lean/rev7/Challenge.lean#L17-L21) | [Axiom audit](verification/rev7/axioms.log#L202-L206); [comparator and both kernel verdicts](verification/rev7/comparator/stdout.log#L224-L229) |
| Smaller limsup construction | [Paper 2, Theorem 1.1](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex#L48-L55) | [`Erdos271.B16.B16_exists`](lean/rev7/B16.lean#L532-L535) (covering and bounds); [`Erdos271.B16.S16_limsup`](lean/rev7/B16Limsup.lean#L49-L51) (exact limsup) | [Covering and bounds audit](verification/rev7/axioms.log#L123-L144); [limsup audit](verification/rev7/axioms.log#L169-L170) |
| Smaller liminf construction | [Paper 2, Theorem 1.2](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex#L57-L64) | [`Erdos271.Liminf.liminf_construction_1889`](lean/rev7/LiminfFinal.lean#L43-L51) | [Axiom audit](verification/rev7/axioms.log#L85-L88) |

The separate liminf refinement is [Paper 2, Remark 5.2](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex#L454-L473), proved by [`Erdos271.Liminf1675.liminf_construction_1675`](lean/rev7/Liminf1675.lean#L15-L16), with its own [axiom audit](verification/rev7/axioms.log#L198-L201).

`Erdos271.main_result` is the canonical entry point for **Paper 1 only**. It uses the abstract's inclusive count, exact constant, and unconditional `ENNReal` limsup. [`Statement.lean`](lean/rev7/Statement.lean) contains the definitions shared by the trusted challenge and solution. The [rev7 guide](lean/rev7/README.md) gives one-command validation instructions.

The limsup construction's equality theorem counts positive members. Including $0$ adds $1$ to its counting function and does not change the normalized limsup. The liminf declarations use an inclusive count and express the bound through arbitrarily large integer cutoffs, with every positive error allowance. The manuscripts state the precise hypotheses and their relation to the displayed limits.

**Validation scope:** the [full-project build](verification/rev7/build.log), [module record](verification/rev7/module-outputs.json), and [27-declaration axiom audit](verification/rev7/acceptance.json) cover all three headline results and the separate liminf refinement. The Challenge/Solution comparator and its independent nanoda check validate **only Paper 1's `Erdos271.main_result`**, not the two construction results or the refinement. Formal correctness, correspondence to prose, and literature priority are separate questions.

## Start here

| Document | PDF | Editable source |
|---|---|---|
| Paper 1: A weighted covering bound for Stanley sequences and weak AP3-coverings, v2.7 | [Read](manuscripts/Erdos271_Weighted_Covering_Review_v2.7.pdf) | [LaTeX](manuscripts/Erdos271_Weighted_Covering_Review_v2.7.tex) |
| Paper 2: Two sparse arithmetic-progression covering constructions, v1.6 | [Read](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.pdf) | [LaTeX](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex) |
| Formal verification and reproducibility supplement, v1.3 | [Read](manuscripts/Erdos271_Verification_Supplement_v1.3.pdf) | [LaTeX](manuscripts/Erdos271_Verification_Supplement_v1.3.tex) |

The earlier public archive editions are preserved. Paper 1 v2.7 and supplement v1.3 document the GitHub-only rev7 statement and comparator interface; Paper 2 is unchanged. For the original editorial corrections, see [manuscript provenance and build instructions](manuscripts/README.md). They are unsubmitted public review drafts. Human authorship and a specialist assessment of novelty remain open; see [attribution](ATTRIBUTION.md) and [review scope](reviews/README.md).

## Reproduce and inspect

- [Verification guide](VERIFICATION.md): exact source identities, toolchain, build commands, and evidence scope.
- [Rev-7 formal interface and proofs](lean/rev7/): 27 audited declarations across all results; Challenge/Solution comparator validation for Paper 1 only.
- [Rev-6 formal sources](lean/rev6/): 39 modules, 26 audited declaration names; [preserved rev-5 sources](lean/rev5/): 38 modules, 24 names.
- [Finite certificates and offline verifier](certificates/README.md): reconstructed public tables and checks, with their source and availability limits.
- [Citation and review evidence](reviews/README.md).
- [Source provenance](SOURCE_PROVENANCE.json) and [public package checksums](SHA256SUMS).

The preserved rev5 and rev6 trees passed independent fresh-project rebuilds with pinned cached dependencies. The original 24 printed declaration types and axiom reports are byte-identical across rev 5 and rev 6. Lean and Mathlib themselves were not rebuilt from source. The complete prose-to-Lean correspondence is not a machine-checked translation.

Rev7 passed a fresh combined sandboxed replay. Comparator matched Paper 1's trusted challenge, and both nanoda and Lean's kernel accepted its `Erdos271.main_result`. The full project build, 27-name audit, 18 audit tests, and validator controls passed. The [rev7 acceptance record](verification/rev7/comparison-and-acceptance.json) also confirms that the earlier 26 printed declaration types and axiom reports are unchanged.

## Status and reuse

The room's citation checks found no fabricated entry among 15 cited works, with source/access limits recorded in the included reports. Fang's full-proof method comparison, a broader priority assessment, and outside specialist review remain open. This archive does not claim peer review or an exhaustive novelty clearance.

Existing source notices are preserved. No blanket license or settled publication author list has been added. Historical source READMEs and checker records are preserved under their own hashes; use this overview and the verification guide for the later independent-build status.
