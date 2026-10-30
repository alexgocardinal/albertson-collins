import Mathlib
import AlbertsonCollins.Elementary

/-!
# Group definitions and a conditional tournament reduction (UNCOMPILED DRAFT)

There are no new axioms or omitted proof terms in this file. The universal main theorem is a named proposition, NOT a proved constant.
The standard finite-group Cauchy bridge is connected to Mathlib below. The
theorem at the end takes the main group statement as an explicit hypothesis.
It is not a proof of the conjecture.
-/

namespace AlbertsonCollins

universe u

/-- The automorphism group, as an actual subgroup of the symmetric group. -/
def Tournament.autGroup {V : Type u} (T : Tournament V) :
    Subgroup (Equiv.Perm V) where
  carrier := {f | ArcPreserving T f}
  one_mem' := by
    intro x y
    rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    have h := hf (f.symm x) (f.symm y)
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

/-- The elementary no-involution argument, now phrased inside the group. -/
theorem Tournament.autGroup_involutive_eq_one {V : Type u}
    (T : Tournament V) (f : Equiv.Perm V)
    (hf : f ∈ T.autGroup) (h2 : f * f = 1) : f = 1 := by
  apply Equiv.ext
  intro x
  apply involutive_automorphism_fixed T f hf _ x
  intro y
  have h := congrArg (fun p : Equiv.Perm V => p y) h2
  change f (f y) = y at h
  exact h

/-- Setwise stabilizer convention used by the paper. -/
def PermStabilizes {V : Type u} (S : Set V) (f : Equiv.Perm V) : Prop :=
  ∀ x, f x ∈ S ↔ x ∈ S

/-- A regular subset has trivial setwise stabilizer in the stated subgroup. -/
def RegularSubset {V : Type u} (G : Subgroup (Equiv.Perm V))
    (S : Set V) : Prop :=
  ∀ f, f ∈ G → PermStabilizes S f → f = 1

/-- The high half for arbitrary degree n, in the original cyclic coordinates. -/
def halfSet (n : Nat) : Set (Fin n) :=
  {x | x.val ≤ (n - 1) / 2}

/--
MAIN UNPROVED TARGET, stated as a proposition rather than an axiom.
The file does not construct a term of this type.
-/
def CanonicalHalfGroupStatement : Prop :=
  ∀ n : Nat, Odd n →
    ∀ G : Subgroup (Equiv.Perm (Fin n)),
      Odd (Nat.card G) → finRotate n ∈ G → RegularSubset G (halfSet n)

/-- Standard Cauchy-at-two bridge, isolated so its precise content is visible. -/
def FiniteGroupCauchyTwo : Prop :=
  ∀ (H : Type) [Group H] [Finite H],
    ¬ Odd (Nat.card H) → ∃ g : H, g ≠ 1 ∧ g * g = 1

/-- Proof of the bridge using Mathlib's Cauchy theorem (UNCOMPILED). -/
theorem finiteGroupCauchyTwo : FiniteGroupCauchyTwo := by
  classical
  intro H _ _ hodd
  have hdiv : 2 ∣ Nat.card H := by
    apply Nat.dvd_of_mod_eq_zero
    by_contra hmod
    apply hodd
    refine ⟨Nat.card H / 2, ?_⟩
    omega
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  refine ⟨g, ?_, ?_⟩
  · intro hone
    subst g
    norm_num at hg
  · have hp := pow_orderOf_eq_one g
    rw [hg] at hp
    simpa only [pow_two] using hp

/-- The oddness of an automorphism group, conditional only on the Cauchy bridge. -/
theorem Tournament.autGroup_odd_of_cauchyTwo
    (hcauchy : FiniteGroupCauchyTwo) {V : Type} [Finite V]
    (T : Tournament V) : Odd (Nat.card T.autGroup) := by
  classical
  by_contra hodd
  obtain ⟨g, hne, hsq⟩ := hcauchy T.autGroup hodd
  have hsq' := congrArg (fun x : T.autGroup => (x : Equiv.Perm V)) hsq
  change (g : Equiv.Perm V) * (g : Equiv.Perm V) = 1 at hsq'
  have hval : (g : Equiv.Perm V) = 1 :=
    T.autGroup_involutive_eq_one g g.property hsq'
  have hg : g = 1 := Subtype.ext hval
  exact hne hg

/-- Odd tournament automorphism order with no project-specific hypotheses. -/
theorem Tournament.autGroup_odd {V : Type} [Finite V]
    (T : Tournament V) : Odd (Nat.card T.autGroup) :=
  T.autGroup_odd_of_cauchyTwo finiteGroupCauchyTwo

/-- The subgroup half has exactly the prescribed interval endpoint. -/
theorem mem_halfSet_odd (q : Nat) (x : Fin (2 * q + 1)) :
    x ∈ halfSet (2 * q + 1) ↔ CanonicalHalf q x := by
  change x.val ≤ ((2 * q + 1 - 1) / 2) ↔ x.val ≤ q
  omega

/--
CONDITIONAL REDUCTION, not the final conjecture theorem.
To obtain a theorem without this explicit hypothesis one must prove the
main group statement. The tournament/Cauchy part is supplied above.
-/
theorem conditional_tournament_reduction
    (hmain : CanonicalHalfGroupStatement)
    (q : Nat) (T : Tournament (Fin (2 * q + 1)))
    (hcyclic : ArcPreserving T (finRotate (2 * q + 1))) :
    RegularSubset T.autGroup (halfSet (2 * q + 1)) := by
  have hn : Odd (2 * q + 1) := ⟨q, by omega⟩
  exact hmain (2 * q + 1) hn T.autGroup
    T.autGroup_odd hcyclic

end AlbertsonCollins
