import AlbertsonCollins.AffineCoordinates

namespace AlbertsonCollins

/-- The precise Burnside-Schur classification consequence required here.
This defines a proposition; it does not assert a proof of it. -/
def BurnsideSchurStatement : Prop :=
  ∀ n : Nat, 1 < n →
    ∀ G : Subgroup (Equiv.Perm (ZMod n)),
      residueTranslation (1 : ZMod n) ∈ G →
      (¬ ∃ B : Set (ZMod n),
        (0 : ZMod n) ∈ B ∧
        MulAction.IsBlock G B ∧
        B ≠ Set.univ ∧
        ∃ x : ZMod n, x ∈ B ∧ x ≠ 0) →
      (∀ x y u v : ZMod n, x ≠ y → u ≠ v →
        ∃ g : G, g.1 x = u ∧ g.1 y = v) ∨
      (Nat.Prime n ∧
        ∃ e : Equiv.Perm (ZMod n),
          ∀ f : Equiv.Perm (ZMod n), f ∈ G →
            ∃ a b : ZMod n,
              ∀ z : ZMod n, e (f (e.symm z)) = a * z + b)

/-- Burnside-Schur supplies the remaining primitive case. -/
theorem primitive_half_of_burnsideSchur
    (hBS : BurnsideSchurStatement) :
    PrimitiveResidueHalfCase := by
  intro n hnodd hn G hodd h1 hno
  rcases hBS n hn G h1 hno with hdouble | ⟨hp, e, hconj⟩
  · letI : NeZero n := ⟨by omega⟩
    have h01 : (0 : ZMod n) ≠ 1 := by
      intro h
      have h1val : (1 : ZMod n).val = 1 := by
        simpa only [Nat.cast_one] using
          (ZMod.val_natCast_of_lt (show 1 < n from hn))
      have h0val : (0 : ZMod n).val = 0 := by simp
      have hv := congrArg (fun z : ZMod n => z.val) h
      change (0 : ZMod n).val = (1 : ZMod n).val at hv
      rw [h0val, h1val] at hv
      omega
    exact False.elim
      ((oddSubgroup_not_two_transitive G hodd 0 1 h01) hdouble)
  · exact odd_affine_group_half_regular n hnodd G hodd
      (affine_coordinates_of_conjugacy n hp G h1 e hconj)

/-- The full group target, with Burnside-Schur as an explicit hypothesis. -/
theorem canonicalHalfGroup_of_burnsideSchur
    (hBS : BurnsideSchurStatement) :
    CanonicalHalfGroupStatement :=
  canonicalHalfGroup_of_primitive_case
    (primitive_half_of_burnsideSchur hBS)

/-- The tournament conclusion, conditional on the same classification theorem. -/
theorem tournament_half_of_burnsideSchur
    (hBS : BurnsideSchurStatement)
    (q : Nat) (T : Tournament (Fin (2 * q + 1)))
    (hcyclic : ArcPreserving T (finRotate (2 * q + 1))) :
    RegularSubset T.autGroup (halfSet (2 * q + 1)) :=
  conditional_tournament_reduction
    (canonicalHalfGroup_of_burnsideSchur hBS) q T hcyclic

end AlbertsonCollins

#check AlbertsonCollins.canonicalHalfGroup_of_burnsideSchur
#print axioms AlbertsonCollins.primitive_half_of_burnsideSchur
#print axioms AlbertsonCollins.tournament_half_of_burnsideSchur
