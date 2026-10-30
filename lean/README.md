# Lean formalization — work in progress

## Current status: October 29, 2026

The project builds successfully with Lean 4.19.0.
Completed proof components have been checked by Lean on Alex Chan's Mac.

The full canonical-coloring theorem remains unfinished.
In particular, CanonicalHalfGroupStatement is a target proposition,
not a proved theorem. The existing conditional tournament reduction
takes that proposition as an explicit hypothesis.

See verification_status.json for the current verification record.

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

## Remaining work

The block reductions, both induced actions, coordinate transport,
and strong induction have been checked by Lean.

The theorem `canonicalHalfGroup_of_primitive_case` takes
`PrimitiveResidueHalfCase` as an explicit hypothesis.
That hypothesis remains unproved, so the full conjecture is
not yet formally verified.

- Primitive-case classification and affine coordinate alignment.
- Affine half-interval stabilizer argument.
- A formal proof of the required Burnside-Schur theorem.

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
