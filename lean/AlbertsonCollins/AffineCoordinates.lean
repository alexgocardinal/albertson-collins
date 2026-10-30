import AlbertsonCollins.AffineHalf

namespace AlbertsonCollins

/-- A map intertwining translation by one with translation by c is affine. -/
theorem residue_shift_equivariant_affine {n : Nat} [NeZero n]
    (e : ZMod n → ZMod n) (c : ZMod n)
    (hshift : ∀ x : ZMod n, e (x + 1) = e x + c) :
    ∀ x : ZMod n, e x = e 0 + x * c := by
  have hnat (k : Nat) :
      e (k : ZMod n) = e 0 + (k : ZMod n) * c := by
    induction k with
    | zero =>
      simp
    | succ k ih =>
      change
        e ((k + 1 : Nat) : ZMod n) =
          e 0 + ((k + 1 : Nat) : ZMod n) * c
      rw [Nat.cast_add, Nat.cast_one, hshift, ih]
      ring
  intro x
  have h := hnat x.val
  simpa only [ZMod.natCast_zmod_val] using h

/-- An affine map over a field with multiplier different from one has a fixed point. -/
theorem fixedPointFree_affine_multiplier_one {K : Type*} [Field K]
    (f : K → K) (a b : K)
    (hform : ∀ x : K, f x = a * x + b)
    (hfree : ∀ x : K, f x ≠ x) :
    a = 1 := by
  by_contra ha
  have hden : 1 - a ≠ 0 := by
    intro h
    exact ha (sub_eq_zero.mp h).symm
  have hfixed : f (b / (1 - a)) = b / (1 - a) := by
    rw [hform]
    field_simp [hden] <;> ring
  exact hfree (b / (1 - a)) hfixed

end AlbertsonCollins

#print axioms AlbertsonCollins.residue_shift_equivariant_affine
#print axioms AlbertsonCollins.fixedPointFree_affine_multiplier_one

namespace AlbertsonCollins

/-- A permutation conjugating the cyclic shift to an affine map is itself affine. -/
theorem cyclic_affine_conjugacy_is_affine
    (p : Nat) (hp : Nat.Prime p)
    (e : Equiv.Perm (ZMod p))
    (hconj : ∃ a b : ZMod p,
      ∀ z : ZMod p, e (e.symm z + 1) = a * z + b) :
    ∃ c : ZMod p, c ≠ 0 ∧
      ∀ x : ZMod p, e x = e 0 + x * c := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, b, hab⟩ := hconj
  let f : ZMod p → ZMod p := fun z => e (e.symm z + 1)
  have hfree : ∀ z : ZMod p, f z ≠ z := by
    intro z hz
    have h := congrArg e.symm hz
    change e.symm (e (e.symm z + 1)) = e.symm z at h
    rw [e.symm_apply_apply] at h
    have hone : (1 : ZMod p) = 0 := by
      calc
        (1 : ZMod p) = (e.symm z + 1) - e.symm z := by ring
        _ = 0 := by rw [h, sub_self]
    exact one_ne_zero hone
  have ha : a = 1 :=
    fixedPointFree_affine_multiplier_one f a b hab hfree
  have hshift : ∀ x : ZMod p, e (x + 1) = e x + b := by
    intro x
    have h := hab (e x)
    rw [e.symm_apply_apply, ha, one_mul] at h
    exact h
  have heform := residue_shift_equivariant_affine e b hshift
  have hb : b ≠ 0 := by
    intro hb
    have h := heform 1
    have heq : e 1 = e 0 := by
      simpa only [hb, mul_zero, add_zero] using h
    exact one_ne_zero (e.injective heq)
  exact ⟨b, hb, heform⟩

/-- Affine conjugacy of a group containing the shift implies affine action
in the original residue coordinates. -/
theorem affine_coordinates_of_conjugacy
    (p : Nat) (hp : Nat.Prime p)
    (G : Subgroup (Equiv.Perm (ZMod p)))
    (h1 : residueTranslation (1 : ZMod p) ∈ G)
    (e : Equiv.Perm (ZMod p))
    (hconj :
      ∀ f : Equiv.Perm (ZMod p), f ∈ G →
        ∃ a b : ZMod p,
          ∀ z : ZMod p, e (f (e.symm z)) = a * z + b) :
    ∀ f : Equiv.Perm (ZMod p), f ∈ G →
      ∃ a b : ZMod p, ∀ x : ZMod p, f x = a * x + b := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, hc, he⟩ :=
    cyclic_affine_conjugacy_is_affine p hp e
      (hconj (residueTranslation (1 : ZMod p)) h1)
  intro f hf
  obtain ⟨a, b, hab⟩ := hconj f hf
  refine ⟨a, f 0, ?_⟩
  intro x
  have hfx : e (f x) = a * e x + b := by
    have h := hab (e x)
    simpa only [Equiv.symm_apply_apply] using h
  have hf0 : e (f 0) = a * e 0 + b := by
    have h := hab (e 0)
    simpa only [Equiv.symm_apply_apply] using h
  rw [he (f x), he x] at hfx
  rw [he (f 0)] at hf0
  have hprod : (f x - (a * x + f 0)) * c = 0 := by
    linear_combination hfx - hf0
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · exact (hc h).elim

end AlbertsonCollins

#print axioms AlbertsonCollins.cyclic_affine_conjugacy_is_affine
#print axioms AlbertsonCollins.affine_coordinates_of_conjugacy

namespace AlbertsonCollins

/-- An element of an odd-order permutation group cannot swap distinct vertices. -/
theorem oddSubgroup_swap_implies_eq {V : Type*}
    (G : Subgroup (Equiv.Perm V))
    (hodd : Odd (Nat.card G))
    (f : Equiv.Perm V) (hf : f ∈ G)
    (x y : V) (hfx : f x = y) (hfy : f y = x) :
    x = y := by
  obtain ⟨k, hk⟩ := hodd
  have hcard : Nat.card G = 1 + 2 * k := by omega
  have heven (m : Nat) : (f ^ (2 * m)) x = x := by
    induction m with
    | zero =>
      simp
    | succ m ih =>
      have hstep : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [hstep, pow_add, pow_two]
      change (f ^ (2 * m)) (f (f x)) = x
      rw [hfx, hfy]
      exact ih
  have hp : f ^ Nat.card G = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (G.orderOf_dvd_natCard hf)
  have hpx := congrArg (fun s : Equiv.Perm V => s x) hp
  rw [hcard, pow_add] at hpx
  change f ((f ^ (2 * k)) x) = x at hpx
  rw [heven k, hfx] at hpx
  exact hpx.symm

/-- An odd-order action with two distinct vertices is not doubly transitive. -/
theorem oddSubgroup_not_two_transitive {V : Type*}
    (G : Subgroup (Equiv.Perm V))
    (hodd : Odd (Nat.card G))
    (x y : V) (hxy : x ≠ y) :
    ¬ (∀ u v s t : V, u ≠ v → s ≠ t →
      ∃ g : G, g.1 u = s ∧ g.1 v = t) := by
  intro h
  obtain ⟨g, hgx, hgy⟩ := h x y y x hxy hxy.symm
  exact hxy
    (oddSubgroup_swap_implies_eq
      G hodd g.1 g.property x y hgx hgy)

end AlbertsonCollins

#print axioms AlbertsonCollins.oddSubgroup_swap_implies_eq
#print axioms AlbertsonCollins.oddSubgroup_not_two_transitive
