import AlbertsonCollins.Obligations

namespace AlbertsonCollins

/-- The endpoint of the canonical half when n = (2u+1)(2v+1). -/
theorem half_product_endpoint (u v : Nat) :
    ((2 * u + 1) * (2 * v + 1) - 1) / 2 =
      (2 * u + 1) * v + u := by
  have h :
      (2 * u + 1) * (2 * v + 1) =
        2 * ((2 * u + 1) * v + u) + 1 := by
    ring
  rw [h]
  omega

end AlbertsonCollins

namespace AlbertsonCollins

/-- Membership in the half-interval, expressed in block coordinates. -/
theorem block_half_membership (u v r t : Nat)
    (hr : r < 2 * u + 1) :
    r + (2 * u + 1) * t ≤ (2 * u + 1) * v + u ↔
      t < v ∨ (t = v ∧ r ≤ u) := by
  constructor
  · intro h
    by_cases htv : t < v
    · exact Or.inl htv
    · right
      have ht : t = v := by
        by_contra hne
        have hstep : v + 1 ≤ t := by omega
        have hmul :=
          Nat.mul_le_mul_left (2 * u + 1) hstep
        nlinarith
      subst t
      exact ⟨rfl, by omega⟩
  · intro h
    rcases h with hlt | ⟨ht, hru⟩
    · have hstep : t + 1 ≤ v := by omega
      have hmul :=
        Nat.mul_le_mul_left (2 * u + 1) hstep
      nlinarith
    · subst t
      omega

end AlbertsonCollins

namespace AlbertsonCollins

/-- The exact high/low intersection counts in odd block coordinates. -/
theorem block_half_count_coordinates (u v r : Nat)
    (hr : r < 2 * u + 1) :
    blockHalfCount (2 * u + 1) (2 * v + 1) r =
      if r ≤ u then v + 1 else v := by
  unfold blockHalfCount
  rw [half_product_endpoint u v]
  have hset :
      (Finset.range (2 * v + 1)).filter
        (fun t => r + (2 * u + 1) * t ≤
          (2 * u + 1) * v + u) =
      Finset.range (if r ≤ u then v + 1 else v) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [block_half_membership u v r t hr]
    split_ifs <;> omega
  rw [hset, Finset.card_range]

end AlbertsonCollins

namespace AlbertsonCollins

/-- The general block-counting obligation is now proved. -/
theorem blockHalfCountStatement_proved :
    BlockHalfCountStatement := by
  intro a b ha hb r hr
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  have hau : a = 2 * u + 1 := by omega
  have hbv : b = 2 * v + 1 := by omega
  subst a
  subst b
  have hu' : (2 * u + 1 - 1) / 2 = u := by omega
  have hv' : (2 * v + 1 + 1) / 2 = v + 1 := by omega
  have hv'' : (2 * v + 1 - 1) / 2 = v := by omega
  simpa only [hu', hv', hv''] using
    block_half_count_coordinates u v r hr

end AlbertsonCollins

#print axioms AlbertsonCollins.blockHalfCountStatement_proved

namespace AlbertsonCollins

/-- High blocks contain the large half; low blocks contain the small half. -/
theorem block_half_membership_by_block (u v r t : Nat)
    (hr : r < 2 * u + 1) :
    r + (2 * u + 1) * t ≤ (2 * u + 1) * v + u ↔
      (if r ≤ u then t ≤ v else t < v) := by
  rw [block_half_membership u v r t hr]
  split_ifs <;> omega

/-- Within 0,...,2v, the complement of the small half is the large half + v. -/
theorem low_half_complement_translate (v t : Nat)
    (ht : t < 2 * v + 1) :
    (¬ t < v) ↔ ∃ s : Nat, s ≤ v ∧ t = s + v := by
  constructor
  · intro h
    refine ⟨t - v, ?_, ?_⟩
    · omega
    · omega
  · rintro ⟨s, hs, hts⟩
    omega

end AlbertsonCollins

#print axioms AlbertsonCollins.block_half_membership_by_block
#print axioms AlbertsonCollins.low_half_complement_translate
