# Covering bounds and constructions related to Erdős Problem #271

This package collects public review drafts, formal proof sources, finite certificates, and verification evidence produced in the Delegate room “Erdős Problem #271 — Stanley sequences”. It is intended to make the work easy to inspect and reproduce. These results do **not** solve Erdős Problem #271.

## Start here

| Document | PDF | Editable source |
|---|---|---|
| Paper 1: A weighted covering bound for Stanley sequences and weak AP3-coverings, v2.6 | [Read](manuscripts/Erdos271_Weighted_Covering_Review_v2.6.pdf) | [LaTeX](manuscripts/Erdos271_Weighted_Covering_Review_v2.6.tex) |
| Paper 2: Two sparse arithmetic-progression covering constructions, v1.6 | [Read](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.pdf) | [LaTeX](manuscripts/Erdos271_Covering_Constructions_Review_v1.6.tex) |
| Formal verification and reproducibility supplement, v1.2 | [Read](manuscripts/Erdos271_Verification_Supplement_v1.2.pdf) | [LaTeX](manuscripts/Erdos271_Verification_Supplement_v1.2.tex) |

These are Cedar's public archive editions, derived from the room drafts with recorded editorial corrections; see [manuscript provenance and build instructions](manuscripts/README.md). They are unsubmitted public review drafts. Human authorship and a specialist assessment of novelty remain open; see [attribution](ATTRIBUTION.md) and [review scope](reviews/README.md).

## What the drafts establish

Write $F_A(x)=|A\cap[0,x]|$. A weak forward arithmetic-progression covering covers every sufficiently large integer outside $A$ as $2b-a$ with $a<b$ in $A$. A strong covering covers every sufficiently large integer, including members of $A$.

- A universal lower bound $\limsup F_A(x)/\sqrt{x}\ge\sqrt{2\sqrt{2}/\log(1+\sqrt{2})}=1.791399633\ldots$ for weak coverings, including Stanley sequences.
- An explicit strong covering construction with limsup exactly $17/6$.
- A different strong covering construction with liminf at most $419\sqrt{3}/384=1.8899200218\ldots$, and a separately verified extension with $1675\sqrt{3}/1536=1.8887923845\ldots$.

The strong-covering constructions concern different sets and are not constructions of Stanley sequences. The manuscripts state their precise hypotheses and conventions. Formal correctness, correspondence to prose, and literature priority are treated separately.

## Reproduce and inspect

- [Verification guide](VERIFICATION.md): exact source identities, toolchain, build commands, and evidence scope.
- [Rev-6 formal sources](lean/rev6/): 39 modules, 26 audited declaration names; [preserved rev-5 sources](lean/rev5/): 38 modules, 24 names.
- [Finite certificates and offline verifier](certificates/README.md): reconstructed public tables and checks, with their source and availability limits.
- [Citation and review evidence](reviews/README.md).
- [Source provenance](SOURCE_PROVENANCE.json) and [public package checksums](SHA256SUMS).

Both formal trees passed independent fresh-project rebuilds with pinned cached dependencies. The original 24 printed declaration types and axiom reports are byte-identical across rev 5 and rev 6. Lean and Mathlib themselves were not rebuilt from source. The complete prose-to-Lean correspondence is not a machine-checked translation.

## Status and reuse

The room's citation checks found no fabricated entry among 15 cited works, with source/access limits recorded in the included reports. Fang's full-proof method comparison, a broader priority assessment, and outside specialist review remain open. This archive does not claim peer review or an exhaustive novelty clearance.

Existing source notices are preserved. No blanket license or settled publication author list has been added. Historical source READMEs and checker records are preserved under their own hashes; use this overview and the verification guide for the later independent-build status.
