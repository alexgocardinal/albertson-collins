import AlbertsonCollins.BlockQuotient

namespace AlbertsonCollins

/-- Identify finite labels with their residues modulo n. -/
def finResidueEquiv (n : Nat) (hn : 0 < n) :
    Fin n ≃ ZMod n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact
    { toFun := fun x => (x.val : ZMod n)
      invFun := fun x => ⟨x.val, ZMod.val_lt x⟩
      left_inv := by
        intro x
        apply Fin.ext
        exact ZMod.val_natCast_of_lt x.isLt
      right_inv := by
        intro x
        exact ZMod.natCast_zmod_val x }

/-- The identification preserves the prescribed half-interval. -/
theorem finResidueEquiv_half (n : Nat) (hn : 0 < n)
    (x : Fin n) :
    (finResidueEquiv n hn x).val ≤ (n - 1) / 2 ↔
      x ∈ halfSet n := by
  change
    (x.val : ZMod n).val ≤ (n - 1) / 2 ↔
      x.val ≤ (n - 1) / 2
  rw [ZMod.val_natCast_of_lt x.isLt]

/-- Rotation of finite labels is translation by one in residue coordinates. -/
theorem finResidueEquiv_rotate (n : Nat) (hn : 0 < n)
    (x : Fin n) :
    finResidueEquiv n hn (finRotate n x) =
      residueTranslation (1 : ZMod n) (finResidueEquiv n hn x) := by
  change
    ((finRotate n x).val : ZMod n) = (x.val : ZMod n) + 1
  rw [finRotate_val_mod n hn]
  calc
    (((x.val + 1) % n : Nat) : ZMod n) =
        ((x.val + 1 : Nat) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).2 (Nat.mod_mod _ _)
    _ = (x.val : ZMod n) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]

end AlbertsonCollins

#print axioms AlbertsonCollins.finResidueEquiv
#print axioms AlbertsonCollins.finResidueEquiv_half
#print axioms AlbertsonCollins.finResidueEquiv_rotate

namespace AlbertsonCollins

/-- The residue-coordinate group theorem implies the finite-label version. -/
theorem fin_half_of_residue_half (n : Nat) (hn : 0 < n)
    (hres :
      ∀ K : Subgroup (Equiv.Perm (ZMod n)),
        Odd (Nat.card K) →
          residueTranslation (1 : ZMod n) ∈ K →
            RegularSubset K
              {z : ZMod n | z.val ≤ (n - 1) / 2})
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hodd : Odd (Nat.card G))
    (hrotate : finRotate n ∈ G) :
    RegularSubset G (halfSet n) := by
  let e := finResidueEquiv n hn
  let F : G →* Equiv.Perm (ZMod n) :=
    (permCoordinatesHom e.symm).comp G.subtype
  let K := F.range
  have hKodd : Odd (Nat.card K) :=
    hodd.of_dvd_nat (Subgroup.card_range_dvd F)
  have hKshift : residueTranslation (1 : ZMod n) ∈ K := by
    refine ⟨⟨finRotate n, hrotate⟩, ?_⟩
    apply Equiv.ext
    intro z
    change
      e (finRotate n (e.symm z)) =
        residueTranslation (1 : ZMod n) z
    have h := finResidueEquiv_rotate n hn (e.symm z)
    change
      e (finRotate n (e.symm z)) =
        residueTranslation (1 : ZMod n) (e (e.symm z)) at h
    simpa only [Equiv.apply_symm_apply] using h
  have hKregular := hres K hKodd hKshift
  intro f hf hhalf
  let g : G := ⟨f, hf⟩
  have hFmem : F g ∈ K := ⟨g, rfl⟩
  have hFhalf : PermStabilizes
      {z : ZMod n | z.val ≤ (n - 1) / 2} (F g) := by
    intro z
    change
      (e (f (e.symm z))).val ≤ (n - 1) / 2 ↔
        z.val ≤ (n - 1) / 2
    have h :=
      (finResidueEquiv_half n hn (f (e.symm z))).trans
        ((hhalf (e.symm z)).trans
          (finResidueEquiv_half n hn (e.symm z)).symm)
    change
      (e (f (e.symm z))).val ≤ (n - 1) / 2 ↔
        (e (e.symm z)).val ≤ (n - 1) / 2 at h
    simpa only [Equiv.apply_symm_apply] using h
  have hid : F g = 1 := hKregular (F g) hFmem hFhalf
  apply Equiv.ext
  intro x
  have hx := congrArg
    (fun p : Equiv.Perm (ZMod n) => p (e x)) hid
  change e (f (e.symm (e x))) = e x at hx
  rw [e.symm_apply_apply] at hx
  exact e.injective hx

end AlbertsonCollins

#print axioms AlbertsonCollins.fin_half_of_residue_half

namespace AlbertsonCollins

/-- The remaining case: no nontrivial block containing zero exists. -/
def PrimitiveResidueHalfCase : Prop :=
  ∀ n : Nat, Odd n → 1 < n →
    ∀ G : Subgroup (Equiv.Perm (ZMod n)),
      Odd (Nat.card G) →
      residueTranslation (1 : ZMod n) ∈ G →
      (¬ ∃ B : Set (ZMod n),
        (0 : ZMod n) ∈ B ∧
        MulAction.IsBlock G B ∧
        B ≠ Set.univ ∧
        ∃ x : ZMod n, x ∈ B ∧ x ≠ 0) →
      RegularSubset G {x : ZMod n | x.val ≤ (n - 1) / 2}

/-- Strong induction reduces the residue theorem to the remaining primitive case. -/
theorem residue_half_of_primitive_case
    (hprimitive : PrimitiveResidueHalfCase) :
    ∀ n : Nat, Odd n →
      ∀ G : Subgroup (Equiv.Perm (ZMod n)),
        Odd (Nat.card G) →
        residueTranslation (1 : ZMod n) ∈ G →
        RegularSubset G {x : ZMod n | x.val ≤ (n - 1) / 2} := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnodd G hodd h1
    have hnpos : 0 < n := by
      obtain ⟨k, hk⟩ := hnodd
      omega
    by_cases hn1 : n = 1
    · subst n
      intro f hf hhalf
      apply Equiv.ext
      intro x
      exact Subsingleton.elim _ _
    · by_cases hex : ∃ B : Set (ZMod n),
          (0 : ZMod n) ∈ B ∧
          MulAction.IsBlock G B ∧
          B ≠ Set.univ ∧
          ∃ x : ZMod n, x ∈ B ∧ x ≠ 0
      · obtain ⟨B, hzero, hB, hproper, hnontrivial⟩ := hex
        apply nontrivial_block_induction_step
          n hnpos hnodd G hodd h1 B hzero hB hproper hnontrivial
        intro m hmn hmodd
        have hmpos : 0 < m := by
          obtain ⟨k, hk⟩ := hmodd
          omega
        exact fin_half_of_residue_half m hmpos (ih m hmn hmodd)
      · exact hprimitive n hnodd (by omega) G hodd h1 hex

/-- The original finite-label target follows from the primitive case. -/
theorem canonicalHalfGroup_of_primitive_case
    (hprimitive : PrimitiveResidueHalfCase) :
    CanonicalHalfGroupStatement := by
  intro n hnodd G hodd hrotate
  have hnpos : 0 < n := by
    obtain ⟨k, hk⟩ := hnodd
    omega
  exact fin_half_of_residue_half n hnpos
    (residue_half_of_primitive_case hprimitive n hnodd)
    G hodd hrotate

end AlbertsonCollins

#print axioms AlbertsonCollins.residue_half_of_primitive_case
#print axioms AlbertsonCollins.canonicalHalfGroup_of_primitive_case
