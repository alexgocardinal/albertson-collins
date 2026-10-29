# Lean foundation: explicitly uncompiled and incomplete

**This is not a Lean-verified proof of the conjecture.** Neither `lean` nor
`lake` was available in the execution environment. No module in this folder
has been compiled, elaborated, or checked by a Lean kernel. Type errors or
version-specific API adjustments may remain. Complete proof terms have been
written for the elementary lemmas, Cauchy bridge, and tournament reduction;
the main group theorem has not been formalized.

The intended baseline is Lean 4.19.0 with mathlib tag `v4.19.0`, recorded in
`lean-toolchain` and `lakefile.lean`. This is a reproducibility starting point,
not a claim that this combination has passed a build. API references were
inspected in current official documentation, which can differ from that tag.

## Files and exact content

| File | Content | Verification status |
| --- | --- | --- |
| `AlbertsonCollins/Elementary.lean` | Standard-library definitions; numeric labels versus subset stabilizer; complement regularity; transport under conjugation; involutive tournament automorphisms fix every vertex | Full proof terms written; uncompiled |
| `AlbertsonCollins/GroupInterface.lean` | Actual automorphism subgroup, no group involutions, Cauchy-at-two bridge, odd automorphism-group order, interval endpoint alignment, conditional tournament reduction | Full proof terms written for these lemmas; uncompiled |
| `AlbertsonCollins/Cyclic.lean` | Actual connector-set tournaments on `ZMod n`; tournament laws; translation permutations and arc preservation; odd automorphism-group order; prescribed labels; concrete directed C3 and Paley T7 | Full proof terms written; uncompiled |
| `AlbertsonCollins/Obligations.lean` | Exact statements for residue-block counts, interval correlations, and the affine multiplier subgoal | Propositions defined only; no proofs |
| `AlbertsonCollins.lean` | Entry point and axiom-printing commands for later inspection | Uncompiled |

`CanonicalHalfGroupStatement` is a **definition of the main target
proposition**. There is no constant asserting it. The theorem
`conditional_tournament_reduction` takes it as an explicit hypothesis. Thus
building the current project, even if successful, would only establish the
stated conditional reduction and elementary lemmas. It would not establish
the universal theorem.

No project axioms, omitted proof terms, or proof-obligation bypasses have
been introduced. Classical reasoning is used where indicated. Lean's
standard logical axioms may therefore appear in `#print axioms`; this is
separate from adding an unproved mathematical theorem to the project.

## First build on a Lean-enabled machine

Run these from this folder after installing the pinned Lean toolchain:

```bash
lake update
lake exe cache get
lake build
```

For the standard-library file alone, a Lean installation is sufficient:

```bash
lean AlbertsonCollins/Elementary.lean
```

These commands are instructions, not a record of commands that passed here.
Do not replace a failed proof with an axiom or suppress a failure. Record a
successful build log, exact dependency revisions, and `#print axioms` output
before claiming formal verification.

## Remaining work, in mathematical dependency order

1. **Cyclic-coordinate interface.** `Cyclic.lean` now constructs the actual
   tournament with arcs `u -> v` exactly when `v-u` belongs to the connector
   set, proves the tournament laws and preservation by every translation,
   and gives concrete C3 (`S={1}`) and Paley T7 (`S={1,2,4}`) examples. It
   records the same positive odd-order and connector conditions as Python.
   Still relate `Fin n`, addition modulo `n`, `ZMod n`, and `finRotate n`
   explicitly, and transport the graph and prescribed labeling through that
   identification. The current Fin-based corollary continues to accept
   `hcyclic`; the ZMod-based translation theorem has not yet been connected
   to that parameter.
2. **Base case and induction.** Establish the `n = 1` group theorem; set up
   strong induction over odd `n` with two nontrivial factors `a,b < n` in
   every imprimitive branch.
3. **Blocks for a regular cyclic subgroup.** A block containing zero is an
   additive subgroup. A nontrivial invariant block system therefore consists
   of congruence classes `B_r = {r + a*t : 0 <= t < b}`, with `n = a*b`.
   This requires actual quotient/restricted action constructions and their
   homomorphisms; it is not just a cardinality calculation.
4. **Oddness and cyclic shifts in the two induced actions.** The action on
   blocks is an odd-order image and contains the `a`-cycle. The action of a
   setwise block stabilizer on a block is an odd-order image and contains
   the restriction of the `a`th power of the original shift, a `b`-cycle.
5. **Block intersections.** Prove `BlockHalfCountStatement`. Identify the
   full subsets, not only their sizes: high intersections are `I_b`; low
   intersections are `{0,...,(b-3)/2}` and their complements are translates
   of `I_b`. The complement/coordinate-transport lemmas already written
   provide the elementary final step.
6. **Primitive classification: the external theorem boundary.** Supply the
   Burnside--Schur theorem in its *permutation-action* form: a finite
   primitive group with a regular cyclic subgroup is doubly transitive or
   has prime degree and is permutation-isomorphic to a subgroup of
   `AGL(1,p)`. A citation in the human proof does not constitute a Lean
   proof. Either locate and verify an existing formalization or formalize
   the theorem and its dependencies. If a relative formalization is the
   chosen deliverable, make this single external hypothesis explicit and
   print it in the result's dependency statement. No such hypothesis has
   silently been added here.
7. **Exclude double transitivity.** Prove that `n*(n-1)` divides the order
   of the group by orbit--stabilizer, contradicting odd order for odd
   `n > 1`.
8. **Affine coordinate alignment.** Show an affine element of order `p` is
   a nonzero translation. If the conjugacy sends the original shift to
   translation by `c`, show `f(j)=f(0)+j*c`; renormalize so all group
   elements are affine in the *original* cyclic coordinates.
9. **Affine stabilizer.** One route is to prove
   `IntervalCorrelationStatement`, then show an affine interval stabilizer
   satisfies `C(a*d)=C(d)`. The maximum for nonzero `d` occurs exactly at
   `d=1` and `d=-1`, so the multiplier is `1` or `-1`. This gives
   `AffineHalfMultiplierStatement`. Exclude a nonzero translation because
   it is transitive in prime degree and the half is proper and nonempty;
   exclude multiplier `-1` because the resulting affine map is an
   involution. This route avoids finite-field moments. The uploaded
   second-moment argument is an alternative, with characteristic three
   handled separately.
10. **Close the induction.** Construct a term of
    `CanonicalHalfGroupStatement`, replace the explicit `hmain` parameter
    in the final application with that term, and connect to actual labels
    through `mem_halfSet_odd` and `preserves_twoColor_iff`.

A proof that assumes the full `CanonicalHalfGroupStatement` has not completed
steps 2--10. A proof that assumes Burnside--Schur alone may become a useful
*relative* formalization after the other steps are completed, but must be
reported as such.

## Official API references inspected

- Lean language reference: <https://lean-lang.org/doc/reference/latest/>
- Mathlib rotation on `Fin n`:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Fin/Rotate.html>
- Mathlib Cauchy theorem, including the `Finite`/`Nat.card` variant
  `exists_prime_orderOf_dvd_card'`:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Cycle/Type.html>
- Mathlib residue definitions and finite residue instances:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Defs.html>
- Mathlib additive normalization used in the translation proof:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Abel.html>
- Mathlib orders of elements and `pow_orderOf_eq_one`:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/OrderOfElement.html>
- Mathlib equivalences/permutations source:
  <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Logic/Equiv/Defs.lean>
- Official Mathematics in Lean documentation (v4.19.0 baseline):
  <https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html>

The current documentation pages were inspected; they are not a build log.
