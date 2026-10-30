import AlbertsonCollins.IntervalCorrelation

namespace AlbertsonCollins

/-- An involution in an odd-order group is the identity. -/
theorem oddOrder_involution_eq_one {H : Type*} [Group H]
    (hodd : Odd (Nat.card H)) (g : H)
    (hsq : g * g = 1) :
    g = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hcard : Nat.card H = 2 * k + 1 := by omega
  have htwo : g ^ 2 = 1 := by
    simpa only [pow_two] using hsq
  have hp : g ^ (2 * k + 1) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  simpa only [pow_add, pow_mul, htwo, one_pow,
    pow_one, one_mul] using hp

/-- The involution result expressed for elements of a permutation subgroup. -/
theorem oddSubgroup_involution_eq_one {V : Type*}
    (G : Subgroup (Equiv.Perm V))
    (hodd : Odd (Nat.card G))
    (f : Equiv.Perm V) (hf : f ∈ G)
    (hsq : f * f = 1) :
    f = 1 := by
  let g : G := ⟨f, hf⟩
  have hsqG : g * g = 1 := Subtype.ext hsq
  have hid : g = 1 := oddOrder_involution_eq_one hodd g hsqG
  exact congrArg (fun x : G => (x : Equiv.Perm V)) hid

/-- An affine reflection belonging to an odd-order group acts trivially. -/
theorem oddSubgroup_reflection_eq_one {n : Nat}
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (hodd : Odd (Nat.card G))
    (f : Equiv.Perm (ZMod n)) (hf : f ∈ G)
    (c : ZMod n)
    (hform : ∀ x : ZMod n, f x = c - x) :
    f = 1 := by
  apply oddSubgroup_involution_eq_one G hodd f hf
  apply Equiv.ext
  intro x
  change f (f x) = x
  rw [hform, hform]
  abel

end AlbertsonCollins

#print axioms AlbertsonCollins.oddOrder_involution_eq_one
#print axioms AlbertsonCollins.oddSubgroup_reflection_eq_one

namespace AlbertsonCollins

/-- A translation preserving the large half has zero displacement. -/
theorem translation_preserving_half_eq_zero
    (q : Nat) (b : ZMod (2 * q + 1))
    (hhalf : ∀ x : ZMod (2 * q + 1),
      (x + b).val ≤ q ↔ x.val ≤ q) :
    b = 0 := by
  letI : NeZero (2 * q + 1) := ⟨by omega⟩
  have hb : b.val ≤ q := by
    have h := (hhalf 0).2 (by simp)
    simpa only [zero_add] using h
  have hqval : (q : ZMod (2 * q + 1)).val = q :=
    ZMod.val_natCast_of_lt (by omega)
  have hsum :
      (q : ZMod (2 * q + 1)).val + b.val < 2 * q + 1 := by
    rw [hqval]
    omega
  have hq :
      ((q : ZMod (2 * q + 1)) + b).val ≤ q :=
    (hhalf (q : ZMod (2 * q + 1))).2
      (by simpa only [hqval] using (Nat.le_refl q))
  rw [ZMod.val_add_of_lt hsum, hqval] at hq
  have hbval : b.val = 0 := by omega
  calc
    b = (b.val : ZMod (2 * q + 1)) :=
      (ZMod.natCast_zmod_val b).symm
    _ = 0 := by rw [hbval, Nat.cast_zero]

/-- The translation result in the general odd-degree coordinates. -/
theorem residue_translation_half_eq_zero
    (n : Nat) (hnodd : Odd n) (b : ZMod n)
    (hhalf : PermStabilizes
      {x : ZMod n | x.val ≤ (n - 1) / 2}
      (residueTranslation b)) :
    b = 0 := by
  obtain ⟨q, hq⟩ := hnodd
  have hn : n = 2 * q + 1 := by omega
  subst n
  have hend : (2 * q + 1 - 1) / 2 = q := by omega
  apply translation_preserving_half_eq_zero q b
  intro x
  have h := hhalf x
  change
    (x + b).val ≤ (2 * q + 1 - 1) / 2 ↔
      x.val ≤ (2 * q + 1 - 1) / 2 at h
  simpa only [hend] using h

/-- Once the affine multiplier is ±1, odd order forces the identity. -/
theorem affine_half_eq_one_of_multiplier_sign
    (n : Nat) (hnodd : Odd n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (hodd : Odd (Nat.card G))
    (f : Equiv.Perm (ZMod n)) (hf : f ∈ G)
    (a b : ZMod n)
    (hform : ∀ x : ZMod n, f x = a * x + b)
    (hhalf : PermStabilizes
      {x : ZMod n | x.val ≤ (n - 1) / 2} f)
    (hcase : a = 1 ∨ a = -1) :
    f = 1 := by
  rcases hcase with ha | ha
  · have htranslation : PermStabilizes
        {x : ZMod n | x.val ≤ (n - 1) / 2}
        (residueTranslation b) := by
      intro x
      change (x + b).val ≤ (n - 1) / 2 ↔ x.val ≤ (n - 1) / 2
      have h := hhalf x
      change (f x).val ≤ (n - 1) / 2 ↔ x.val ≤ (n - 1) / 2 at h
      simpa only [hform x, ha, one_mul] using h
    have hb := residue_translation_half_eq_zero n hnodd b htranslation
    apply Equiv.ext
    intro x
    change f x = x
    rw [hform, ha, hb, one_mul, add_zero]
  · apply oddSubgroup_reflection_eq_one G hodd f hf b
    intro x
    rw [hform, ha]
    ring

end AlbertsonCollins

#print axioms AlbertsonCollins.residue_translation_half_eq_zero
#print axioms AlbertsonCollins.affine_half_eq_one_of_multiplier_sign

namespace AlbertsonCollins

/-- An affine half-preserving permutation transports correlation intersections. -/
def affineCorrelationEquiv
    (q : Nat) (f : Equiv.Perm (ZMod (2 * q + 1)))
    (a b d : ZMod (2 * q + 1))
    (hform : ∀ x : ZMod (2 * q + 1), f x = a * x + b)
    (hhalf : ∀ x : ZMod (2 * q + 1),
      (f x).val ≤ q ↔ x.val ≤ q) :
    residueCorrelationVertices q d ≃
      residueCorrelationVertices q (a * d) :=
  f.subtypeEquiv (by
    intro x
    have hsub : f (x - d) = f x - a * d := by
      rw [hform, hform]
      ring
    change
      (x.val ≤ q ∧ (x - d).val ≤ q) ↔
        ((f x).val ≤ q ∧ (f x - a * d).val ≤ q)
    rw [← hsub]
    exact and_congr (hhalf x).symm (hhalf (x - d)).symm)

/-- Affine preservation of the half implies C(a*d) = C(d). -/
theorem affine_residueCorrelation_invariant
    (q : Nat) (f : Equiv.Perm (ZMod (2 * q + 1)))
    (a b d : ZMod (2 * q + 1))
    (hform : ∀ x : ZMod (2 * q + 1), f x = a * x + b)
    (hhalf : ∀ x : ZMod (2 * q + 1),
      (f x).val ≤ q ↔ x.val ≤ q) :
    residueCorrelation q (a * d) = residueCorrelation q d := by
  exact Nat.card_congr
    (affineCorrelationEquiv q f a b d hform hhalf).symm

end AlbertsonCollins

#print axioms AlbertsonCollins.affineCorrelationEquiv
#print axioms AlbertsonCollins.affine_residueCorrelation_invariant

namespace AlbertsonCollins

/-- Correlation q identifies precisely the representatives of ±1. -/
theorem residueCorrelation_eq_q_val_iff
    (q : Nat) (hq : 0 < q) (d : ZMod (2 * q + 1)) :
    residueCorrelation q d = q ↔
      d.val = 1 ∨ d.val = 2 * q := by
  letI : NeZero (2 * q + 1) := ⟨by omega⟩
  rw [residueCorrelation_formula]
  have hdlt := ZMod.val_lt d
  by_cases hd : d.val ≤ q
  · rw [min_eq_left (show d.val ≤ 2 * q + 1 - d.val by omega)]
    omega
  · rw [min_eq_right (show 2 * q + 1 - d.val ≤ d.val by omega)]
    omega

/-- Every affine permutation preserving a nontrivial odd half has multiplier ±1. -/
theorem affine_half_multiplier_sign
    (q : Nat) (hq : 0 < q)
    (f : Equiv.Perm (ZMod (2 * q + 1)))
    (a b : ZMod (2 * q + 1))
    (hform : ∀ x : ZMod (2 * q + 1), f x = a * x + b)
    (hhalf : ∀ x : ZMod (2 * q + 1),
      (f x).val ≤ q ↔ x.val ≤ q) :
    a = 1 ∨ a = -1 := by
  letI : NeZero (2 * q + 1) := ⟨by omega⟩
  have h1val : (1 : ZMod (2 * q + 1)).val = 1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (show 1 < 2 * q + 1 by omega))
  have hC1 : residueCorrelation q (1 : ZMod (2 * q + 1)) = q :=
    (residueCorrelation_eq_q_val_iff q hq 1).2 (Or.inl h1val)
  have hCa : residueCorrelation q a = q := by
    have hc := affine_residueCorrelation_invariant
      q f a b 1 hform hhalf
    simpa only [mul_one, hC1] using hc
  rcases (residueCorrelation_eq_q_val_iff q hq a).1 hCa with ha | ha
  · left
    apply ZMod.val_injective (2 * q + 1)
    exact ha.trans h1val.symm
  · right
    have hval :
        ((2 * q : Nat) : ZMod (2 * q + 1)).val = 2 * q :=
      ZMod.val_natCast_of_lt (by omega)
    have hae : a = ((2 * q : Nat) : ZMod (2 * q + 1)) :=
      (ZMod.val_injective (2 * q + 1)) (ha.trans hval.symm)
    have hz :
        ((2 * q : Nat) : ZMod (2 * q + 1)) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ZMod.natCast_self (2 * q + 1))
    calc
      a = ((2 * q : Nat) : ZMod (2 * q + 1)) := hae
      _ = (((2 * q : Nat) : ZMod (2 * q + 1)) + 1) - 1 := by
        ring
      _ = -1 := by rw [hz, zero_sub]

end AlbertsonCollins

#print axioms AlbertsonCollins.affine_half_multiplier_sign

namespace AlbertsonCollins

/-- The canonical half is regular for every odd-order group acting affinely
in the original residue coordinates. -/
theorem odd_affine_group_half_regular
    (n : Nat) (hnodd : Odd n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (hodd : Odd (Nat.card G))
    (haffine :
      ∀ f : Equiv.Perm (ZMod n), f ∈ G →
        ∃ a b : ZMod n, ∀ x : ZMod n, f x = a * x + b) :
    RegularSubset G {x : ZMod n | x.val ≤ (n - 1) / 2} := by
  obtain ⟨q, hq⟩ := hnodd
  have hn : n = 2 * q + 1 := by omega
  subst n
  intro f hf hhalf
  by_cases hqpos : 0 < q
  · obtain ⟨a, b, hform⟩ := haffine f hf
    have hend : (2 * q + 1 - 1) / 2 = q := by omega
    have hnatural : ∀ x : ZMod (2 * q + 1),
        (f x).val ≤ q ↔ x.val ≤ q := by
      intro x
      have h := hhalf x
      change
        (f x).val ≤ (2 * q + 1 - 1) / 2 ↔
          x.val ≤ (2 * q + 1 - 1) / 2 at h
      simpa only [hend] using h
    exact affine_half_eq_one_of_multiplier_sign
      (2 * q + 1) ⟨q, by omega⟩ G hodd f hf a b hform hhalf
      (affine_half_multiplier_sign q hqpos f a b hform hnatural)
  · have hqzero : q = 0 := by omega
    subst q
    apply Equiv.ext
    intro x
    exact Subsingleton.elim (α := ZMod 1) (f x) x

end AlbertsonCollins

#print axioms AlbertsonCollins.odd_affine_group_half_regular
