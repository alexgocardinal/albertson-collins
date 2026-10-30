import AlbertsonCollins.CoordinateTransport

namespace AlbertsonCollins

/-- Vertices counted by the interval correlation. -/
abbrev intervalCorrelationVertices (q : Nat) (d : Fin (2 * q + 1)) : Type :=
  {x : Fin (2 * q + 1) //
    x.val ≤ q ∧
      (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q}

/-- The subtype cardinality agrees with the original finite-set definition. -/
theorem intervalCorrelationVertices_card
    (q : Nat) (d : Fin (2 * q + 1)) :
    Nat.card (intervalCorrelationVertices q d) =
      intervalCorrelation q d := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype
    (p := fun x : Fin (2 * q + 1) =>
      x.val ≤ q ∧
        (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q)
    ((Finset.univ : Finset (Fin (2 * q + 1))).filter
      (fun x => x.val ≤ q ∧
        (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q))
    (by intro x; simp)

/-- For a low shift, the intersection consists exactly of d,...,q. -/
theorem intervalCorrelation_low_membership
    (q : Nat) (d : Fin (2 * q + 1)) (hd : d.val ≤ q)
    (x : Fin (2 * q + 1)) :
    (x.val ≤ q ∧
      (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q) ↔
      d.val ≤ x.val ∧ x.val ≤ q := by
  by_cases hx : x.val ≤ q
  · by_cases hdx : d.val ≤ x.val
    · have heq :
          x.val + (2 * q + 1) - d.val =
            (x.val - d.val) + (2 * q + 1) := by omega
      have hlt : x.val - d.val < 2 * q + 1 := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      omega
    · have hlt :
          x.val + (2 * q + 1) - d.val < 2 * q + 1 := by omega
      rw [Nat.mod_eq_of_lt hlt]
      omega
  · omega

/-- Enumerate the low-shift intersection by its displacement from d. -/
def intervalCorrelationLowEquiv
    (q : Nat) (d : Fin (2 * q + 1)) (hd : d.val ≤ q) :
    Fin (q + 1 - d.val) ≃ intervalCorrelationVertices q d where
  toFun := fun t =>
    ⟨⟨d.val + t.val, by
        have ht := t.isLt
        omega⟩,
      (intervalCorrelation_low_membership q d hd _).2
        ⟨(by
            change d.val ≤ d.val + t.val
            omega),
         (by
            change d.val + t.val ≤ q
            have ht := t.isLt
            omega)⟩⟩
  invFun := fun x =>
    ⟨x.val.val - d.val, by
      have hx :=
        (intervalCorrelation_low_membership q d hd x.val).1 x.property
      omega⟩
  left_inv := by
    intro t
    apply Fin.ext
    change d.val + t.val - d.val = t.val
    omega
  right_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    change d.val + (x.val.val - d.val) = x.val.val
    have hx :=
      (intervalCorrelation_low_membership q d hd x.val).1 x.property
    omega

/-- The exact correlation count for shifts at most q. -/
theorem intervalCorrelation_low
    (q : Nat) (d : Fin (2 * q + 1)) (hd : d.val ≤ q) :
    intervalCorrelation q d = q + 1 - d.val := by
  have hc := Nat.card_congr (intervalCorrelationLowEquiv q d hd).symm
  rw [intervalCorrelationVertices_card] at hc
  simpa using hc

end AlbertsonCollins

#print axioms AlbertsonCollins.intervalCorrelation_low

namespace AlbertsonCollins

/-- For a high shift, the intersection is the initial segment of length d-q. -/
theorem intervalCorrelation_high_membership
    (q : Nat) (d : Fin (2 * q + 1)) (hd : q < d.val)
    (x : Fin (2 * q + 1)) :
    (x.val ≤ q ∧
      (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q) ↔
      x.val < d.val - q := by
  have hdlt := d.isLt
  by_cases hx : x.val ≤ q
  · have hlt :
        x.val + (2 * q + 1) - d.val < 2 * q + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · omega

/-- Enumerate the high-shift intersection by its initial-segment coordinates. -/
def intervalCorrelationHighEquiv
    (q : Nat) (d : Fin (2 * q + 1)) (hd : q < d.val) :
    Fin (d.val - q) ≃ intervalCorrelationVertices q d where
  toFun := fun t =>
    ⟨⟨t.val, by
        have ht := t.isLt
        have hdlt := d.isLt
        omega⟩,
      (intervalCorrelation_high_membership q d hd _).2 (by
        change t.val < d.val - q
        exact t.isLt)⟩
  invFun := fun x =>
    ⟨x.val.val,
      (intervalCorrelation_high_membership q d hd x.val).1 x.property⟩
  left_inv := by
    intro t
    apply Fin.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- The exact correlation count for shifts greater than q. -/
theorem intervalCorrelation_high
    (q : Nat) (d : Fin (2 * q + 1)) (hd : q < d.val) :
    intervalCorrelation q d = d.val - q := by
  have hc := Nat.card_congr (intervalCorrelationHighEquiv q d hd).symm
  rw [intervalCorrelationVertices_card] at hc
  simpa using hc

/-- The full interval-correlation obligation is proved. -/
theorem intervalCorrelationStatement_proved :
    IntervalCorrelationStatement := by
  intro q d
  have hdlt := d.isLt
  by_cases hd : d.val ≤ q
  · rw [intervalCorrelation_low q d hd,
      min_eq_left (show d.val ≤ 2 * q + 1 - d.val by omega)]
  · rw [intervalCorrelation_high q d (by omega),
      min_eq_right (show 2 * q + 1 - d.val ≤ d.val by omega)]
    omega

end AlbertsonCollins

#print axioms AlbertsonCollins.intervalCorrelation_high
#print axioms AlbertsonCollins.intervalCorrelationStatement_proved

namespace AlbertsonCollins

/-- For a nontrivial odd interval, correlation q occurs exactly at shifts ±1. -/
theorem intervalCorrelation_eq_q_iff
    (q : Nat) (hq : 0 < q) (d : Fin (2 * q + 1)) :
    intervalCorrelation q d = q ↔
      d.val = 1 ∨ d.val = 2 * q := by
  have hdlt := d.isLt
  by_cases hd : d.val ≤ q
  · rw [intervalCorrelation_low q d hd]
    omega
  · rw [intervalCorrelation_high q d (by omega)]
    omega

/-- The representative of a residue difference, expressed by natural modulo. -/
theorem residue_sub_val {n : Nat} [NeZero n]
    (x d : ZMod n) :
    (x - d).val = (x.val + n - d.val) % n := by
  have hdle : d.val ≤ x.val + n := by
    have hdlt := ZMod.val_lt d
    omega
  have hc :
      ((x.val + n - d.val : Nat) : ZMod n) = x - d := by
    rw [Nat.cast_sub hdle, Nat.cast_add, ZMod.natCast_self,
      add_zero, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [← hc, ZMod.val_natCast]

/-- The intersection whose cardinality is used by the affine argument. -/
abbrev residueCorrelationVertices
    (q : Nat) (d : ZMod (2 * q + 1)) : Type :=
  {x : ZMod (2 * q + 1) //
    x.val ≤ q ∧ (x - d).val ≤ q}

noncomputable def residueCorrelation (q : Nat) (d : ZMod (2 * q + 1)) : Nat :=
  Nat.card (residueCorrelationVertices q d)

/-- The interval-correlation formula in residue coordinates. -/
theorem residueCorrelation_formula
    (q : Nat) (d : ZMod (2 * q + 1)) :
    residueCorrelation q d =
      q + 1 - min d.val (2 * q + 1 - d.val) := by
  letI : NeZero (2 * q + 1) := ⟨by omega⟩
  let e := finResidueEquiv (2 * q + 1) (by omega)
  let df : Fin (2 * q + 1) := e.symm d
  have hval (x : Fin (2 * q + 1)) :
      (e x).val = x.val :=
    ZMod.val_natCast_of_lt x.isLt
  let f : intervalCorrelationVertices q df ≃
      residueCorrelationVertices q d :=
    e.subtypeEquiv (by
      intro x
      change
        (x.val ≤ q ∧
          (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q) ↔
        ((e x).val ≤ q ∧ (e x - d).val ≤ q)
      simp only [residue_sub_val, hval x])
  calc
    residueCorrelation q d =
        Nat.card (intervalCorrelationVertices q df) :=
      Nat.card_congr f.symm
    _ = intervalCorrelation q df :=
      intervalCorrelationVertices_card q df
    _ = q + 1 - min d.val (2 * q + 1 - d.val) :=
      intervalCorrelationStatement_proved q df

end AlbertsonCollins

#print axioms AlbertsonCollins.intervalCorrelation_eq_q_iff
#print axioms AlbertsonCollins.residueCorrelation_formula
