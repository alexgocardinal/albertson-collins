import AlbertsonCollins.CyclicSubgroups
import AlbertsonCollins.BlockArithmetic

open Fin.NatCast

namespace AlbertsonCollins

/-- A block coordinate gives a representative below a * b. -/
theorem block_coordinate_lt {a b : Nat}
    (r : Fin a) (t : Fin b) :
    r.val + a * t.val < a * b := by
  have hr := r.isLt
  have ht : t.val + 1 ≤ b := by omega
  have hm := Nat.mul_le_mul_left a ht
  nlinarith

/-- Every residue has a unique block index and position within its block. -/
def residueBlockCoordinates (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) :
    ZMod (a * b) ≃ Fin a × Fin b := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  exact
    { toFun := fun x =>
        (⟨x.val % a, Nat.mod_lt x.val ha⟩,
         ⟨x.val / a, by
           have hx := ZMod.val_lt x
           have hdecomp := Nat.mod_add_div x.val a
           by_contra h
           have hle : b ≤ x.val / a := by omega
           have hm := Nat.mul_le_mul_left a hle
           omega⟩)
      invFun := fun p =>
        ((p.1.val + a * p.2.val : Nat) : ZMod (a * b))
      left_inv := by
        intro x
        change
          ((x.val % a + a * (x.val / a) : Nat) :
            ZMod (a * b)) = x
        rw [Nat.mod_add_div, ZMod.natCast_zmod_val]
      right_inv := by
        intro p
        apply Prod.ext
        · apply Fin.ext
          change
            (((p.1.val + a * p.2.val : Nat) :
              ZMod (a * b)).val % a) = p.1.val
          rw [ZMod.val_natCast_of_lt
                (block_coordinate_lt p.1 p.2),
              Nat.add_mul_mod_self_left,
              Nat.mod_eq_of_lt p.1.isLt]
        · apply Fin.ext
          change
            (((p.1.val + a * p.2.val : Nat) :
              ZMod (a * b)).val / a) = p.2.val
          rw [ZMod.val_natCast_of_lt
                (block_coordinate_lt p.1 p.2),
              Nat.add_mul_div_left _ _ ha,
              Nat.div_eq_of_lt p.1.isLt,
              Nat.zero_add] }

end AlbertsonCollins

#print axioms AlbertsonCollins.block_coordinate_lt
#print axioms AlbertsonCollins.residueBlockCoordinates

namespace AlbertsonCollins

/-- The block with representative r consists of one residue class modulo a. -/
def residueBlock (a b : Nat) (r : Fin a) :
    Set (ZMod (a * b)) :=
  {x | x.val % a = r.val}

/-- Block membership means that the first coordinate is r. -/
theorem mem_residueBlock_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (r : Fin a) (x : ZMod (a * b)) :
    x ∈ residueBlock a b r ↔
      (residueBlockCoordinates a b ha hb x).1 = r := by
  constructor
  · intro hx
    apply Fin.ext
    exact hx
  · intro hx
    exact congrArg (fun z : Fin a => z.val) hx

/-- The positions within a fixed block are precisely Fin b. -/
def residueBlockEquiv (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (r : Fin a) :
    Fin b ≃ {x : ZMod (a * b) // x ∈ residueBlock a b r} := by
  let e := residueBlockCoordinates a b ha hb
  exact
    { toFun := fun t =>
        ⟨e.symm (r, t), by
          apply (mem_residueBlock_iff a b ha hb r _).2
          exact congrArg
            (fun p : Fin a × Fin b => p.1)
            (e.apply_symm_apply (r, t))⟩
      invFun := fun x => (e x.val).2
      left_inv := by
        intro t
        exact congrArg
          (fun p : Fin a × Fin b => p.2)
          (e.apply_symm_apply (r, t))
      right_inv := by
        intro x
        apply Subtype.ext
        change e.symm (r, (e x.val).2) = x.val
        have hr : (e x.val).1 = r :=
          (mem_residueBlock_iff a b ha hb r x.val).1 x.property
        have hp : (r, (e x.val).2) = e x.val := by
          apply Prod.ext
          · exact hr.symm
          · rfl
        rw [hp, e.symm_apply_apply] }

/-- Every residue block has exactly b vertices. -/
theorem residueBlock_card (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (r : Fin a) :
    Nat.card {x : ZMod (a * b) // x ∈ residueBlock a b r} = b := by
  simpa using Nat.card_congr (residueBlockEquiv a b ha hb r).symm

end AlbertsonCollins

#print axioms AlbertsonCollins.residueBlockEquiv
#print axioms AlbertsonCollins.residueBlock_card

namespace AlbertsonCollins

/-- The vertex in position t of block r has representative r + a*t. -/
theorem residueBlockEquiv_val (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (r : Fin a) (t : Fin b) :
    (residueBlockEquiv a b ha hb r t).val.val =
      r.val + a * t.val := by
  change
    ((r.val + a * t.val : Nat) : ZMod (a * b)).val =
      r.val + a * t.val
  exact ZMod.val_natCast_of_lt (block_coordinate_lt r t)

/-- Exact half-interval membership under the block bijection. -/
theorem block_half_in_residue_coordinates
    (u v : Nat) (r : Fin (2 * u + 1))
    (t : Fin (2 * v + 1)) :
    (residueBlockEquiv (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) r t).val.val ≤
        ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
      (if r.val ≤ u then t.val ≤ v else t.val < v) := by
  rw [residueBlockEquiv_val, half_product_endpoint]
  exact block_half_membership_by_block u v r.val t.val r.isLt

/-- In a high block, the preserved subset is the canonical large half. -/
theorem high_block_half_iff
    (u v : Nat) (r : Fin (2 * u + 1))
    (hr : r.val ≤ u) (t : Fin (2 * v + 1)) :
    (residueBlockEquiv (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) r t).val.val ≤
        ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
      t.val ≤ v := by
  rw [block_half_in_residue_coordinates, if_pos hr]

/-- In a low block, the complement is the large half translated by v. -/
theorem low_block_half_complement_iff
    (u v : Nat) (r : Fin (2 * u + 1))
    (hr : u < r.val) (t : Fin (2 * v + 1)) :
    (¬ (residueBlockEquiv (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) r t).val.val ≤
        ((2 * u + 1) * (2 * v + 1) - 1) / 2) ↔
      ∃ s : Nat, s ≤ v ∧ t.val = s + v := by
  rw [block_half_in_residue_coordinates, if_neg (by omega)]
  exact low_half_complement_translate v t.val t.isLt

end AlbertsonCollins

#print axioms AlbertsonCollins.high_block_half_iff
#print axioms AlbertsonCollins.low_block_half_complement_iff

namespace AlbertsonCollins

/-- The subgroup of G that preserves S setwise. -/
def setwiseStabilizerIn {V : Type*}
    (G : Subgroup (Equiv.Perm V)) (S : Set V) :
    Subgroup G where
  carrier := {g | PermStabilizes S (g : Equiv.Perm V)}
  one_mem' := by
    intro x
    rfl
  mul_mem' := by
    intro g h hg hh x
    exact (hg (h.1 x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    have h := hg (g.1.symm x)
    simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm

/-- A setwise stabilizer element restricts to a permutation of the set. -/
def restrictToSet {V : Type*}
    {G : Subgroup (Equiv.Perm V)} {S : Set V}
    (g : setwiseStabilizerIn G S) : Equiv.Perm S where
  toFun := fun x =>
    ⟨g.1.1 x.val, (g.property x.val).2 x.property⟩
  invFun := fun x =>
    ⟨g.1.1.symm x.val, by
      apply (g.property (g.1.1.symm x.val)).1
      simpa only [Equiv.apply_symm_apply] using x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact g.1.1.symm_apply_apply x.val
  right_inv := by
    intro x
    apply Subtype.ext
    exact g.1.1.apply_symm_apply x.val

/-- Restriction respects identity and multiplication. -/
def restrictToSetHom {V : Type*}
    (G : Subgroup (Equiv.Perm V)) (S : Set V) :
    setwiseStabilizerIn G S →* Equiv.Perm S where
  toFun := restrictToSet
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl

end AlbertsonCollins

#print axioms AlbertsonCollins.setwiseStabilizerIn
#print axioms AlbertsonCollins.restrictToSetHom

namespace AlbertsonCollins

/-- Express permutations in the coordinates supplied by an equivalence. -/
def permCoordinatesHom {V W : Type*} (e : W ≃ V) :
    Equiv.Perm V →* Equiv.Perm W where
  toFun := fun p => (e.trans p).trans e.symm
  map_one' := by
    apply Equiv.ext
    intro x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  map_mul' := by
    intro p q
    apply Equiv.ext
    intro x
    change
      e.symm (p (q (e x))) =
        e.symm (p (e (e.symm (q (e x)))))
    rw [e.apply_symm_apply]

/-- Restrict a block stabilizer and express its action on Fin b. -/
def blockRestrictionHom (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (r : Fin a) :
    setwiseStabilizerIn G (residueBlock a b r) →*
      Equiv.Perm (Fin b) :=
  (permCoordinatesHom (residueBlockEquiv a b ha hb r)).comp
    (restrictToSetHom G (residueBlock a b r))

/-- The actual permutation group induced on the coordinates of a block. -/
def blockActionGroup (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (r : Fin a) :
    Subgroup (Equiv.Perm (Fin b)) :=
  (blockRestrictionHom a b ha hb G r).range

/-- The coordinate action agrees with the original action on vertices. -/
theorem blockRestrictionHom_apply (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (r : Fin a)
    (g : setwiseStabilizerIn G (residueBlock a b r))
    (t : Fin b) :
    (residueBlockEquiv a b ha hb r
      (blockRestrictionHom a b ha hb G r g t)).val =
        g.1.1 ((residueBlockEquiv a b ha hb r t).val) := by
  let e := residueBlockEquiv a b ha hb r
  change
    (e (e.symm (restrictToSet g (e t)))).val =
      g.1.1 ((e t).val)
  rw [e.apply_symm_apply]
  rfl

end AlbertsonCollins

#print axioms AlbertsonCollins.blockRestrictionHom
#print axioms AlbertsonCollins.blockRestrictionHom_apply

namespace AlbertsonCollins

/-- The order of the induced block action divides the order of G. -/
theorem blockActionGroup_card_dvd (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (r : Fin a) :
    Nat.card (blockActionGroup a b ha hb G r) ∣ Nat.card G := by
  change
    Nat.card (blockRestrictionHom a b ha hb G r).range ∣
      Nat.card G
  exact dvd_trans
    (Subgroup.card_range_dvd
      (blockRestrictionHom a b ha hb G r))
    (Subgroup.card_subgroup_dvd_card
      (setwiseStabilizerIn G (residueBlock a b r)))

/-- An odd-order group induces an odd-order group on each block. -/
theorem blockActionGroup_odd (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (hodd : Odd (Nat.card G)) (r : Fin a) :
    Odd (Nat.card (blockActionGroup a b ha hb G r)) := by
  exact hodd.of_dvd_nat
    (blockActionGroup_card_dvd a b ha hb G r)

end AlbertsonCollins

#print axioms AlbertsonCollins.blockActionGroup_card_dvd
#print axioms AlbertsonCollins.blockActionGroup_odd

namespace AlbertsonCollins

/-- Translation by a preserves each residue block modulo a. -/
theorem residueTranslation_a_stabilizes (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (r : Fin a) :
    PermStabilizes (residueBlock a b r)
      (residueTranslation (a : ZMod (a * b))) := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  intro x
  change
    (x + (a : ZMod (a * b))).val % a = r.val ↔
      x.val % a = r.val
  have hx :
      ((x.val + a : Nat) : ZMod (a * b)) =
        x + (a : ZMod (a * b)) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [← hx, ZMod.val_natCast,
    Nat.mod_mod_of_dvd _ (show a ∣ a * b from ⟨b, rfl⟩),
    Nat.add_mod_right]

/-- The original translation by a lifts to the stabilizer of each block. -/
theorem block_translation_lift (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (r : Fin a) :
    ∃ g : setwiseStabilizerIn G (residueBlock a b r),
      g.1.1 = residueTranslation (a : ZMod (a * b)) := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  refine ⟨⟨⟨residueTranslation (a : ZMod (a * b)),
    all_translations_mem G h1 (a : ZMod (a * b))⟩, ?_⟩, rfl⟩
  exact residueTranslation_a_stabilizes a b ha hb r

end AlbertsonCollins

#print axioms AlbertsonCollins.residueTranslation_a_stabilizes
#print axioms AlbertsonCollins.block_translation_lift

namespace AlbertsonCollins

/-- Moving one position within a block is translation by a. -/
theorem block_coordinate_rotate (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (r : Fin a) (t : Fin b) :
    (residueBlockEquiv a b ha hb r (finRotate b t)).val =
      (residueBlockEquiv a b ha hb r t).val +
        (a : ZMod (a * b)) := by
  change
    ((r.val + a * (finRotate b t).val : Nat) : ZMod (a * b)) =
      ((r.val + a * t.val : Nat) : ZMod (a * b)) +
        (a : ZMod (a * b))
  cases b with
  | zero => omega
  | succ k =>
    rw [coe_finRotate]
    split_ifs with ht
    · have htval : t.val = k :=
        congrArg (fun z : Fin (k + 1) => z.val) ht
      rw [htval]
      simp only [Nat.mul_zero, Nat.add_zero]
      calc
        (r.val : ZMod (a * (k + 1))) =
            (r.val : ZMod (a * (k + 1))) +
              ((a * (k + 1) : Nat) : ZMod (a * (k + 1))) := by
          rw [ZMod.natCast_self, add_zero]
        _ = ((r.val + a * k : Nat) : ZMod (a * (k + 1))) +
              (a : ZMod (a * (k + 1))) := by
          push_cast
          ring
    · push_cast
      ring

/-- The induced group on each block contains the standard cyclic shift. -/
theorem finRotate_mem_blockActionGroup (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (r : Fin a) :
    finRotate b ∈ blockActionGroup a b ha hb G r := by
  obtain ⟨g, hg⟩ := block_translation_lift a b ha hb G h1 r
  change finRotate b ∈ (blockRestrictionHom a b ha hb G r).range
  refine ⟨g, ?_⟩
  apply Equiv.ext
  intro t
  apply (residueBlockEquiv a b ha hb r).injective
  apply Subtype.ext
  rw [blockRestrictionHom_apply, hg]
  change
    (residueBlockEquiv a b ha hb r t).val +
        (a : ZMod (a * b)) =
      (residueBlockEquiv a b ha hb r (finRotate b t)).val
  exact (block_coordinate_rotate a b ha hb r t).symm

end AlbertsonCollins

#print axioms AlbertsonCollins.block_coordinate_rotate
#print axioms AlbertsonCollins.finRotate_mem_blockActionGroup

namespace AlbertsonCollins

/-- A trivial coordinate action means every vertex of the block is fixed. -/
theorem blockRestrictionHom_eq_one_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (r : Fin a)
    (g : setwiseStabilizerIn G (residueBlock a b r)) :
    blockRestrictionHom a b ha hb G r g = 1 ↔
      ∀ x : ZMod (a * b),
        x ∈ residueBlock a b r → g.1.1 x = x := by
  let e := residueBlockEquiv a b ha hb r
  constructor
  · intro h x hx
    let z : {x : ZMod (a * b) // x ∈ residueBlock a b r} :=
      ⟨x, hx⟩
    let t : Fin b := e.symm z
    have ht : (e t).val = x :=
      congrArg Subtype.val (e.apply_symm_apply z)
    have hact := blockRestrictionHom_apply a b ha hb G r g t
    rw [h] at hact
    change (e t).val = g.1.1 ((e t).val) at hact
    rw [ht] at hact
    exact hact.symm
  · intro h
    apply Equiv.ext
    intro t
    change blockRestrictionHom a b ha hb G r g t = t
    apply e.injective
    apply Subtype.ext
    change
      (residueBlockEquiv a b ha hb r
        (blockRestrictionHom a b ha hb G r g t)).val =
          (residueBlockEquiv a b ha hb r t).val
    rw [blockRestrictionHom_apply]
    exact h _ (e t).property

end AlbertsonCollins

#print axioms AlbertsonCollins.blockRestrictionHom_eq_one_iff

namespace AlbertsonCollins

/-- The smaller-degree theorem forces pointwise fixation of each high block. -/
theorem high_block_fixed_of_smaller_case
    (u v : Nat)
    (G : Subgroup
      (Equiv.Perm (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (hodd : Odd (Nat.card G))
    (h1 : residueTranslation
      (1 : ZMod ((2 * u + 1) * (2 * v + 1))) ∈ G)
    (hsmall :
      ∀ H : Subgroup (Equiv.Perm (Fin (2 * v + 1))),
        Odd (Nat.card H) → finRotate (2 * v + 1) ∈ H →
          RegularSubset H (halfSet (2 * v + 1)))
    (r : Fin (2 * u + 1)) (hr : r.val ≤ u)
    (g : setwiseStabilizerIn G
      (residueBlock (2 * u + 1) (2 * v + 1) r))
    (hhalf : PermStabilizes
      {x : ZMod ((2 * u + 1) * (2 * v + 1)) |
        x.val ≤ ((2 * u + 1) * (2 * v + 1) - 1) / 2}
      g.1.1) :
    ∀ x : ZMod ((2 * u + 1) * (2 * v + 1)),
      x ∈ residueBlock (2 * u + 1) (2 * v + 1) r →
        g.1.1 x = x := by
  let e := residueBlockEquiv (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) r
  let H := blockActionGroup (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G r
  let f := blockRestrictionHom (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G r g
  have hregular : RegularSubset H (halfSet (2 * v + 1)) :=
    hsmall H
      (blockActionGroup_odd _ _ (by omega) (by omega) G hodd r)
      (finRotate_mem_blockActionGroup
        _ _ (by omega) (by omega) G h1 r)
  have hfmem : f ∈ H := ⟨g, rfl⟩
  have hcoords (t : Fin (2 * v + 1)) :
      (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
        t ∈ halfSet (2 * v + 1) := by
    change
      (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
        t.val ≤ (2 * v + 1 - 1) / 2
    have hv : (2 * v + 1 - 1) / 2 = v := by omega
    rw [hv]
    exact high_block_half_iff u v r hr t
  have hpres : PermStabilizes (halfSet (2 * v + 1)) f := by
    intro t
    have h := hhalf ((e t).val)
    change
      (g.1.1 ((e t).val)).val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
        (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 at h
    rw [← blockRestrictionHom_apply
      _ _ (by omega) (by omega) G r g t] at h
    exact (hcoords (f t)).symm.trans (h.trans (hcoords t))
  exact (blockRestrictionHom_eq_one_iff
    _ _ (by omega) (by omega) G r g).1
      (hregular f hfmem hpres)

end AlbertsonCollins

#print axioms AlbertsonCollins.high_block_fixed_of_smaller_case

namespace AlbertsonCollins

/-- The complement of a regular subset is regular. -/
theorem regularSubset_complement_of_regular {V : Type*}
    {G : Subgroup (Equiv.Perm V)} {S : Set V}
    (hregular : RegularSubset G S) :
    RegularSubset G Sᶜ := by
  classical
  intro f hf hS
  apply hregular f hf
  intro x
  have hx := hS x
  change (¬ f x ∈ S) ↔ (¬ x ∈ S) at hx
  exact not_iff_not.mp hx

/-- Taking the preimage under an element of G preserves regularity. -/
theorem regularSubset_preimage_of_mem {V : Type*}
    {G : Subgroup (Equiv.Perm V)} {S : Set V}
    (hregular : RegularSubset G S)
    (p : Equiv.Perm V) (hp : p ∈ G) :
    RegularSubset G (p ⁻¹' S) := by
  intro f hf hS
  let q : Equiv.Perm V := p * f * p⁻¹
  have hqmem : q ∈ G :=
    G.mul_mem (G.mul_mem hp hf) (G.inv_mem hp)
  have hqstable : PermStabilizes S q := by
    intro x
    have h := hS (p.symm x)
    change
      p (f (p.symm x)) ∈ S ↔ p (p.symm x) ∈ S at h
    change p (f (p.symm x)) ∈ S ↔ x ∈ S
    simpa only [Equiv.apply_symm_apply] using h
  have hq : q = 1 := hregular q hqmem hqstable
  apply Equiv.ext
  intro x
  have hx := congrArg (fun s : Equiv.Perm V => s (p x)) hq
  change p (f (p.symm (p x))) = p x at hx
  rw [p.symm_apply_apply] at hx
  exact p.injective hx

end AlbertsonCollins

#print axioms AlbertsonCollins.regularSubset_complement_of_regular
#print axioms AlbertsonCollins.regularSubset_preimage_of_mem

namespace AlbertsonCollins

/-- Powers of the standard rotation are addition in Fin. -/
theorem finRotate_pow_apply_add (n k : Nat) (t : Fin (n + 1)) :
    (finRotate (n + 1) ^ k) t = t + (k : Fin (n + 1)) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ']
    change
      finRotate (n + 1) ((finRotate (n + 1) ^ k) t) =
        t + ((k + 1 : Nat) : Fin (n + 1))
    rw [ih, finRotate_succ_apply]
    push_cast
    simp only [add_assoc]

/-- Shifting by v+1 takes the complement of the small half to the large half. -/
theorem rotate_to_large_half_iff (v : Nat) (t : Fin (2 * v + 1)) :
    (finRotate (2 * v + 1) ^ (v + 1)) t ∈
        halfSet (2 * v + 1) ↔
      ¬ t.val < v := by
  change
    ((finRotate (2 * v + 1) ^ (v + 1)) t).val ≤
        (2 * v + 1 - 1) / 2 ↔
      ¬ t.val < v
  have hv : (2 * v + 1 - 1) / 2 = v := by omega
  rw [hv, finRotate_pow_apply_add]
  have hval :
      (t + ((v + 1 : Nat) : Fin (2 * v + 1))).val =
        (t.val + (v + 1)) % (2 * v + 1) := by
    rw [Fin.val_add, Fin.val_natCast]
    conv_rhs => rw [Nat.add_mod]
    rw [Nat.mod_eq_of_lt t.isLt]
  rw [hval]
  by_cases ht : t.val < v
  · have hlt : t.val + (v + 1) < 2 * v + 1 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · have heq :
        t.val + (v + 1) = (t.val - v) + (2 * v + 1) := by
      omega
    have hlt : t.val - v < 2 * v + 1 := by
      have := t.isLt
      omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    have := t.isLt
    omega

/-- In a group containing the rotation, regularity of the large half
implies regularity of the small half. -/
theorem small_half_regular_of_large (v : Nat)
    (H : Subgroup (Equiv.Perm (Fin (2 * v + 1))))
    (hrotate : finRotate (2 * v + 1) ∈ H)
    (hregular : RegularSubset H (halfSet (2 * v + 1))) :
    RegularSubset H {t : Fin (2 * v + 1) | t.val < v} := by
  let p := finRotate (2 * v + 1) ^ (v + 1)
  have hp : p ∈ H := H.pow_mem hrotate (v + 1)
  have hpre := regularSubset_preimage_of_mem hregular p hp
  have hset :
      p ⁻¹' halfSet (2 * v + 1) =
        ({t : Fin (2 * v + 1) | t.val < v} : Set _)ᶜ := by
    ext t
    change p t ∈ halfSet (2 * v + 1) ↔ ¬ t.val < v
    exact rotate_to_large_half_iff v t
  rw [hset] at hpre
  simpa using regularSubset_complement_of_regular hpre

end AlbertsonCollins

#print axioms AlbertsonCollins.rotate_to_large_half_iff
#print axioms AlbertsonCollins.small_half_regular_of_large

namespace AlbertsonCollins

/-- The smaller-degree theorem forces pointwise fixation of each low block. -/
theorem low_block_fixed_of_smaller_case
    (u v : Nat)
    (G : Subgroup
      (Equiv.Perm (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (hodd : Odd (Nat.card G))
    (h1 : residueTranslation
      (1 : ZMod ((2 * u + 1) * (2 * v + 1))) ∈ G)
    (hsmall :
      ∀ H : Subgroup (Equiv.Perm (Fin (2 * v + 1))),
        Odd (Nat.card H) → finRotate (2 * v + 1) ∈ H →
          RegularSubset H (halfSet (2 * v + 1)))
    (r : Fin (2 * u + 1)) (hr : u < r.val)
    (g : setwiseStabilizerIn G
      (residueBlock (2 * u + 1) (2 * v + 1) r))
    (hhalf : PermStabilizes
      {x : ZMod ((2 * u + 1) * (2 * v + 1)) |
        x.val ≤ ((2 * u + 1) * (2 * v + 1) - 1) / 2}
      g.1.1) :
    ∀ x : ZMod ((2 * u + 1) * (2 * v + 1)),
      x ∈ residueBlock (2 * u + 1) (2 * v + 1) r →
        g.1.1 x = x := by
  let e := residueBlockEquiv (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) r
  let H := blockActionGroup (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G r
  let f := blockRestrictionHom (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G r g
  have hrotate : finRotate (2 * v + 1) ∈ H :=
    finRotate_mem_blockActionGroup
      _ _ (by omega) (by omega) G h1 r
  have hlarge : RegularSubset H (halfSet (2 * v + 1)) :=
    hsmall H
      (blockActionGroup_odd _ _ (by omega) (by omega) G hodd r)
      hrotate
  have hregular :
      RegularSubset H {t : Fin (2 * v + 1) | t.val < v} :=
    small_half_regular_of_large v H hrotate hlarge
  have hfmem : f ∈ H := ⟨g, rfl⟩
  have hcoords (t : Fin (2 * v + 1)) :
      (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
        t.val < v := by
    have h := block_half_in_residue_coordinates u v r t
    rw [if_neg (by omega)] at h
    exact h
  have hpres :
      PermStabilizes {t : Fin (2 * v + 1) | t.val < v} f := by
    intro t
    have h := hhalf ((e t).val)
    change
      (g.1.1 ((e t).val)).val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 ↔
        (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 at h
    rw [← blockRestrictionHom_apply
      _ _ (by omega) (by omega) G r g t] at h
    exact (hcoords (f t)).symm.trans (h.trans (hcoords t))
  exact (blockRestrictionHom_eq_one_iff
    _ _ (by omega) (by omega) G r g).1
      (hregular f hfmem hpres)

end AlbertsonCollins

#print axioms AlbertsonCollins.low_block_fixed_of_smaller_case

namespace AlbertsonCollins

/-- Once every block is preserved, the smaller-degree theorem forces identity. -/
theorem blockwise_identity_of_smaller_case
    (u v : Nat)
    (G : Subgroup
      (Equiv.Perm (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (hodd : Odd (Nat.card G))
    (h1 : residueTranslation
      (1 : ZMod ((2 * u + 1) * (2 * v + 1))) ∈ G)
    (hsmall :
      ∀ H : Subgroup (Equiv.Perm (Fin (2 * v + 1))),
        Odd (Nat.card H) → finRotate (2 * v + 1) ∈ H →
          RegularSubset H (halfSet (2 * v + 1)))
    (g : G)
    (hblocks : ∀ r : Fin (2 * u + 1),
      PermStabilizes (residueBlock (2 * u + 1) (2 * v + 1) r)
        (g : Equiv.Perm
          (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (hhalf : PermStabilizes
      {x : ZMod ((2 * u + 1) * (2 * v + 1)) |
        x.val ≤ ((2 * u + 1) * (2 * v + 1) - 1) / 2}
      (g : Equiv.Perm
        (ZMod ((2 * u + 1) * (2 * v + 1))))) :
    (g : Equiv.Perm
      (ZMod ((2 * u + 1) * (2 * v + 1)))) = 1 := by
  apply Equiv.ext
  intro x
  change g.1 x = x
  let r : Fin (2 * u + 1) :=
    (residueBlockCoordinates (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) x).1
  have hx : x ∈ residueBlock (2 * u + 1) (2 * v + 1) r := by
    apply (mem_residueBlock_iff
      _ _ (by omega) (by omega) r x).2
    rfl
  let gB : setwiseStabilizerIn G
      (residueBlock (2 * u + 1) (2 * v + 1) r) :=
    ⟨g, hblocks r⟩
  by_cases hr : r.val ≤ u
  · exact high_block_fixed_of_smaller_case
      u v G hodd h1 hsmall r hr gB hhalf x hx
  · exact low_block_fixed_of_smaller_case
      u v G hodd h1 hsmall r (by omega) gB hhalf x hx

end AlbertsonCollins

#print axioms AlbertsonCollins.blockwise_identity_of_smaller_case
