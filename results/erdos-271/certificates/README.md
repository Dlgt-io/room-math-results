# Erdős 271 finite certificates

This directory reconstructs the public finite certificate data referenced by Paper 2 from the frozen construction note and Paper 2 appendix. It is not a byte-identical copy of the unavailable first-release certificate package.

Run the bounded offline verifier from this directory:

```sh
python3 scripts/verify_constructions.py --extended
```

The verifier uses only the Python standard library. It regenerates every included set and witness table, compares the stored bytes, checks all ten pinned full SHA-256 hashes for included files, and runs the finite base-16 checks through `16**5` when `--extended` is supplied.

`data/a16-cylinder.csv` records a historical depth-4 subdivision check. Exactly one row, rank 1 with leader 3 and digits `3333`, fails that proposed cylinder inequality. This is the documented exception in that historical subdivision check. The final base-16 bound uses the 22 exact rational comparisons in `data/twenty_two_checks.csv`.

The downloaded reproducibility kit supplied exact source bytes for `data/a16-base-window.csv`, `data/a4-base-window.csv`, and `data/twenty_two_checks.csv`; all 189 entries listed by that kit's checksum manifest passed. The other data files were regenerated from the frozen public recipes. Their hashes reproduce the ten pinned full hashes for included files and the published prefixes for the remaining included tables.

The recovered historical generator supplied the explicit 24-element `S_192` list. The package now includes its 190-row witness table and checks both full pinned hashes. The original `scripts/verify_constructions.py` remains unavailable, so the active verifier remains a reconstruction from the published algorithm.

The recovered generator is archived unchanged at `original-generator/release_data.py`. Do not execute it in place because it writes to hard-coded `/tmp/rel` paths. `original-generator/README.md` records this historical-path caveat. The later `S_786432` candidate remains outside the release and executable verifier; `optional-1675.md` records its room-report recipe and hashes without storing the roughly 13 MB witness table.

`verification-report.json` records the data hashes, row counts, finite checks, and these limits. `source-provenance.json` records the public source archive and frozen-note identities, hashes, and exact-versus-reconstructed status.
