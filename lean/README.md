# Lean formalization

## Current status — October 30, 2026

The prescribed half-coloring theorem for cyclic tournaments is formally
proved. The stronger odd-order permutation-group statement is also proved.

The project builds with Lean 4.35.0-rc3. The final theorem axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.
Burnside-Schur is supplied by proof terms, not an unproved hypothesis.

See verification_status.json in the Lean directory for the verification record.

## Completed components

- Elementary stabilizer and tournament lemmas.
- Odd order of tournament automorphism groups.
- Actual cyclic tournament constructions and translation automorphisms.
- Block intersection arithmetic and counts.
- Generation of every translation from the shift by one.
- Construction of additive subgroups from blocks containing zero.
- Description of block images as additive translates.
- Classification of cyclic subgroups by divisibility.
- Two smaller odd factors arising from a nontrivial block.

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

## Build

From this directory:

~~~bash
lake update
lake exe cache get
lake build
~~~

Commit both lean-toolchain and lake-manifest.json to preserve
the intended toolchain and dependency revisions.

## Historical notes

INITIAL_FORMALIZATION_NOTES.md preserves the original detailed
roadmap and API references. Its uncompiled-status statements,
and historical draft notices in the original source comments,
describe the initial package rather than the current build status.

