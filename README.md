# Canonical distinguishing colorings of cyclic tournaments

Alex Chan  
Harvard University and NBER  
achan@hbs.edu

## Current status — October 30, 2026

The prescribed half-coloring theorem for cyclic tournaments is formally
proved. The stronger odd-order permutation-group statement is also proved.

The project builds with Lean 4.35.0-rc3. The final theorem axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.
Burnside-Schur is supplied by proof terms, not an unproved hypothesis.

See `lean/verification_status.json` for the verification record.

## Contents

- paper/canonical_coloring.tex — editable manuscript.
- paper/canonical_coloring.pdf — compiled manuscript.
- code/ — graph construction and exact automorphism checks.
- graphs/ — directed graph data and illustrations.
- lean/ — formal definitions and completed proof components.
- verification/ — mathematical audits and finite-check records.

The proof-and-audit guide describes the completed proof. The original
roadmap and model audit remain available as historical records, with
dated addenda that explain the completed verification.

## Build the Lean project

From the lean directory, run:

~~~bash
lake update
lake exe cache get
lake build
~~~

The toolchain and dependency manifest record the required versions.

## Verified conclusions

- `AlbertsonCollins.canonicalHalfGroup_proved`
- `AlbertsonCollins.tournament_half_regular`

Neither theorem takes an unproved classification hypothesis.

The external Burnside-Schur proof comes from AxiomMath/CFSG.
Its pinned source revision is recorded in `CFSG/UPSTREAM.json` within
the Lean directory, with the Apache-2.0 license in `CFSG/LICENSE`.

The manuscript and proof-and-audit guide document the completed
formalization and its external proof attribution. The initial roadmap
and original audit are retained with dated status addenda. Their
original draft notices describe earlier checkpoints.

## Computational material

The Python implementation constructs cyclic tournaments from connector
sets and searches arbitrary color-preserving automorphisms.

Finite checks cover every connector set at odd orders through 23.
These computations support the formulation and software; they are
not premises of the all-orders mathematical proof.

See code/README.md for commands and details.

## Publication status

This is a working research project and manuscript draft.
Publication priority and external peer review are not established.

