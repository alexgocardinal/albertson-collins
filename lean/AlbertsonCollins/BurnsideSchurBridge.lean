import AlbertsonCollins.BurnsideSchurReduction
import CFSG.Permutation.BurnsideSchur.Main

namespace AlbertsonCollins

/-- The classification hypothesis is supplied by the imported proof. -/
theorem burnsideSchurStatement_proved : BurnsideSchurStatement := by
  classical
  intro n hn G h1 hno
  letI : NeZero n := ⟨by omega⟩

  have htranslations : ∀ c : ZMod n, Equiv.addRight c ∈ G := by
    intro c
    have heq : Equiv.addRight c = residueTranslation c := by
      apply Equiv.ext
      intro x
      rfl
    rw [heq]
    exact all_translations_mem G h1 c

  letI : MulAction.IsPretransitive G (ZMod n) :=
    shift_group_pretransitive G h1

  letI : MulAction.IsPreprimitive G (ZMod n) := by
    apply MulAction.IsPreprimitive.of_isTrivialBlock_base
      (G := G) (0 : ZMod n)
    intro B hzero hB
    by_cases hfull : B = Set.univ
    · exact Or.inr hfull
    · apply Or.inl
      have hz : ∀ z : ZMod n, z ∈ B → z = 0 := by
        intro z hzB
        by_contra hne
        exact hno ⟨B, hzero, hB, hfull, z, hzB, hne⟩
      intro x hx y hy
      exact (hz x hx).trans (hz y hy).symm

  by_cases hdouble :
      MulAction.IsMultiplyPretransitive G (ZMod n) 2
  · left
    intro x y u v hxy huv
    obtain ⟨g, hgx, hgy⟩ :=
      (MulAction.is_two_pretransitive_iff.mp hdouble) hxy huv
    exact ⟨g, hgx, hgy⟩
  · right
    have hp : Nat.Prime n := by
      by_contra hnp
      have hcard : ¬ (Nat.card (ZMod n)).Prime := by
        simpa only [Nat.card_zmod] using hnp
      exact hdouble
        (CFSG.BurnsideSchur.isMultiplyPretransitive_of_not_prime
          htranslations hcard)
    letI : Fact n.Prime := ⟨hp⟩
    refine ⟨hp, Equiv.refl (ZMod n), ?_⟩
    intro f hf
    obtain ⟨a, ha, b, hab⟩ :=
      CFSG.BurnsideSchur.exists_affine_of_not_isMultiplyPretransitive
        htranslations hdouble hf
    exact ⟨a, b, fun z => by simpa using hab z⟩

/-- The canonical half is regular for every odd-order group containing rotation. -/
theorem canonicalHalfGroup_proved : CanonicalHalfGroupStatement :=
  canonicalHalfGroup_of_burnsideSchur burnsideSchurStatement_proved

/-- The prescribed half-coloring has trivial stabilizer in a cyclic tournament. -/
theorem tournament_half_regular
    (q : Nat) (T : Tournament (Fin (2 * q + 1)))
    (hcyclic : ArcPreserving T (finRotate (2 * q + 1))) :
    RegularSubset T.autGroup (halfSet (2 * q + 1)) :=
  tournament_half_of_burnsideSchur burnsideSchurStatement_proved
    q T hcyclic

end AlbertsonCollins

#check AlbertsonCollins.canonicalHalfGroup_proved
#check AlbertsonCollins.tournament_half_regular
#print axioms AlbertsonCollins.burnsideSchurStatement_proved
#print axioms AlbertsonCollins.canonicalHalfGroup_proved
#print axioms AlbertsonCollins.tournament_half_regular
