import AlbertsonCollins.BlockCosets

namespace AlbertsonCollins

/-- Subgroups of ZMod n are described by divisibility of representatives. -/
theorem cyclic_subgroup_divisibility {n : Nat}
    (H : AddSubgroup (ZMod n)) :
    ∃ a : Nat, a ∣ n ∧
      ∀ k : Nat, (k : ZMod n) ∈ H ↔ a ∣ k := by
  let K : AddSubgroup ℤ :=
    H.comap (Int.castAddHom (ZMod n))
  obtain ⟨z, hz⟩ :
      ∃ z : ℤ, AddSubgroup.zmultiples z = K :=
    (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top K).mp
      (inferInstance : IsAddCyclic K)
  let a : Nat := z.natAbs
  have hK : K = AddSubgroup.zmultiples (a : ℤ) := by
    dsimp [a]
    rw [Int.zmultiples_natAbs]
    exact hz.symm
  have hmem (k : Nat) :
      (k : ZMod n) ∈ H ↔ a ∣ k := by
    have hk :
        ((k : ℤ) : ZMod n) ∈ H ↔
          (a : ℤ) ∣ (k : ℤ) := by
      change (k : ℤ) ∈ K ↔ (a : ℤ) ∣ (k : ℤ)
      rw [hK, Int.mem_zmultiples_iff]
    simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using hk
  refine ⟨a, ?_, hmem⟩
  apply (hmem n).1
  simpa only [ZMod.natCast_self] using H.zero_mem

end AlbertsonCollins

namespace AlbertsonCollins

/-- A block containing zero consists exactly of multiples of a divisor of n. -/
theorem shift_block_divisor_description {n : Nat}
    (hn : 0 < n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B) :
    ∃ a : Nat, 0 < a ∧ a ∣ n ∧
      ∀ x : ZMod n, x ∈ B ↔ a ∣ x.val := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let H := subgroupOfShiftBlock G h1 B hzero hB
  obtain ⟨a, ha, hmem⟩ := cyclic_subgroup_divisibility H
  refine ⟨a, Nat.pos_of_dvd_of_pos ha hn, ha, ?_⟩
  intro x
  have hm := hmem x.val
  change ((x.val : ZMod n) ∈ B ↔ a ∣ x.val) at hm
  simpa only [ZMod.natCast_zmod_val] using hm

end AlbertsonCollins

#print axioms AlbertsonCollins.cyclic_subgroup_divisibility
#print axioms AlbertsonCollins.shift_block_divisor_description

namespace AlbertsonCollins

/-- A proper block containing a nonzero vertex gives a proper divisor. -/
theorem nontrivial_shift_block_divisor {n : Nat}
    (hn : 0 < n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (hproper : B ≠ Set.univ)
    (hnontrivial : ∃ x : ZMod n, x ∈ B ∧ x ≠ 0) :
    ∃ a : Nat, 1 < a ∧ a < n ∧ a ∣ n ∧
      ∀ x : ZMod n, x ∈ B ↔ a ∣ x.val := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  obtain ⟨a, hapos, hadiv, hmem⟩ :=
    shift_block_divisor_description hn G h1 B hzero hB
  refine ⟨a, ?_, ?_, hadiv, hmem⟩
  · by_contra h
    have haone : a = 1 := by omega
    apply hproper
    ext x
    simp only [Set.mem_univ, iff_true]
    apply (hmem x).2
    simp [haone]
  · obtain ⟨x, hx, hxne⟩ := hnontrivial
    have hxpos : 0 < x.val := by
      by_contra h
      have hxval : x.val = 0 := by omega
      apply hxne
      calc
        x = (x.val : ZMod n) :=
          (ZMod.natCast_zmod_val x).symm
        _ = 0 := by rw [hxval, Nat.cast_zero]
    have hale : a ≤ x.val :=
      Nat.le_of_dvd hxpos ((hmem x).1 hx)
    exact lt_of_le_of_lt hale (ZMod.val_lt x)

end AlbertsonCollins

#print axioms AlbertsonCollins.nontrivial_shift_block_divisor

namespace AlbertsonCollins

/-- A proper divisor of an odd number gives two smaller odd factors. -/
theorem proper_divisor_odd_factors {n a : Nat}
    (hn : 0 < n) (hodd : Odd n)
    (ha : 1 < a) (han : a < n) (hadiv : a ∣ n) :
    ∃ b : Nat, n = a * b ∧ Odd a ∧ Odd b ∧
      1 < b ∧ b < n := by
  obtain ⟨b, hb⟩ := hadiv
  have hbgt : 1 < b := by
    by_contra h
    have hcases : b = 0 ∨ b = 1 := by omega
    rcases hcases with hbzero | hbone
    · rw [hbzero, Nat.mul_zero] at hb
      omega
    · rw [hbone, Nat.mul_one] at hb
      omega
  have hmul : 2 * b ≤ a * b :=
    Nat.mul_le_mul_right b (by omega)
  have hblt : b < n := by omega
  refine ⟨b, hb, hodd.of_dvd_nat ⟨b, hb⟩, ?_, hbgt, hblt⟩
  apply hodd.of_dvd_nat
  exact ⟨a, by simpa only [Nat.mul_comm] using hb⟩

/-- A nontrivial block supplies the factorization needed for induction. -/
theorem nontrivial_shift_block_factors {n : Nat}
    (hn : 0 < n) (hodd : Odd n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (hproper : B ≠ Set.univ)
    (hnontrivial : ∃ x : ZMod n, x ∈ B ∧ x ≠ 0) :
    ∃ a b : Nat, n = a * b ∧ Odd a ∧ Odd b ∧
      1 < a ∧ a < n ∧ 1 < b ∧ b < n ∧
      ∀ x : ZMod n, x ∈ B ↔ a ∣ x.val := by
  obtain ⟨a, ha, han, hadiv, hmem⟩ :=
    nontrivial_shift_block_divisor
      hn G h1 B hzero hB hproper hnontrivial
  obtain ⟨b, hab, haodd, hbodd, hb, hbn⟩ :=
    proper_divisor_odd_factors hn hodd ha han hadiv
  exact ⟨a, b, hab, haodd, hbodd, ha, han, hb, hbn, hmem⟩

end AlbertsonCollins

#print axioms AlbertsonCollins.nontrivial_shift_block_factors
