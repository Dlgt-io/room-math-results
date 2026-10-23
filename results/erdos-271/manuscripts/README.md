# Public manuscript edition

These three documents are Cedar's public archive edition of the room's Paper 1 v2.5, Paper 2 v1.5 and supplement v1.1. They incorporate the seven recorded review corrections, public archive links, adopted rev-6 status, and explicit certificate provenance. The equations, mathematical arguments and bibliography were preserved. Two stale certificate-package instructions were corrected during independent export review.

The documents remain unsubmitted review drafts. Authorship, literature priority and outside specialist review remain open. This edition does not claim to solve Erdős Problem #271.

[Editorial provenance](editorial-provenance.json) records the input and output source hashes and the scope of edits. [PDF build manifest](pdf-build-manifest.json) pairs each source with the PDF compiled from it using Tectonic 0.17.0. The archive PDFs were rendered and visually inspected after compilation.

To rebuild a document, install Tectonic and run `tectonic --untrusted --outdir output DOCUMENT.tex` from this directory, replacing `DOCUMENT.tex` with one of the three source filenames. The first run may need network access for TeX resources. PDF creation timestamps can change the rebuilt PDF hash even when the source is identical. A standard LaTeX installation can also compile these self-contained sources.
