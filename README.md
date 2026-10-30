# Canonical distinguishing colorings of cyclic tournaments

Alex Chan  
Harvard University and NBER  
achan@hbs.edu

## Current status — October 29, 2026

The manuscript presents an all-orders proof of the prescribed
Albertson–Collins coloring statement, using the classical
Burnside–Schur theorem.

The Lean formalization is **in progress**. The existing project
builds successfully with Lean 4.19.0, and its completed components
have been checked by Lean. The main universal group theorem has
not yet been formally proved.

A successful build of this project does **not** currently constitute
a complete Lean verification of the conjecture.

See lean/verification_status.json for the current verification record.

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

## Remaining formalization

The block reductions, both induced actions, coordinate transport,
and strong induction have been checked by Lean.

The theorem `canonicalHalfGroup_of_primitive_case` takes
`PrimitiveResidueHalfCase` as an explicit hypothesis.
That hypothesis remains unproved, so the full conjecture is
not yet formally verified.

- Primitive-case classification and affine coordinate alignment.
- Affine half-interval stabilizer argument.
- A formal proof of the required Burnside-Schur theorem.

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
