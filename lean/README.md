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

- Coordinate equivalences and induced group actions.
- The strong induction proving the universal group theorem.
- The primitive-case reduction and affine interval argument.
- A formal proof of the required Burnside–Schur theorem.

No unproved project axiom replaces these missing steps.
Standard Lean foundations such as Classical.choice are distinct
from assuming an unproved mathematical theorem.

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
