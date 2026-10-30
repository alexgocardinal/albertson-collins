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

See verification_status.json in the Lean directory for the verification record.

## Contents

- paper/canonical_coloring.tex — editable manuscript.
- paper/canonical_coloring.pdf — compiled manuscript.
- code/ — graph construction and exact automorphism checks.
- graphs/ — directed graph data and illustrations.
- lean/ — formal definitions and completed proof components.
- verification/ — mathematical audits and finite-check records.

The proof-and-audit guide and original roadmap describe the initial
package. Their statements that Lean files were uncompiled are
superseded by the current verification record.

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

Historical draft notices describe earlier checkpoints.
The manuscript and historical audit documents have not yet been updated
to describe the completed formalization.

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
