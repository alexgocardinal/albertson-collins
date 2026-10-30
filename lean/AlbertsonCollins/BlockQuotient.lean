import AlbertsonCollins.BlockCoordinates

namespace AlbertsonCollins

/-- Descend a group action through an index map with chosen representatives. -/
def fiberActionHom {V W : Type*}
    (G : Subgroup (Equiv.Perm V))
    (π : V → W) (s : W → V)
    (hsection : ∀ w, π (s w) = w)
    (hcongr : ∀ g : G, ∀ x y : V,
      π x = π y → π (g.1 x) = π (g.1 y)) :
    G →* Equiv.Perm W where
  toFun := fun g =>
    { toFun := fun w => π (g.1 (s w))
      invFun := fun w => π (g.1.symm (s w))
      left_inv := by
        intro w
        have h := hcongr (g⁻¹)
          (s (π (g.1 (s w)))) (g.1 (s w)) (hsection _)
        calc
          π (g.1.symm (s (π (g.1 (s w))))) =
              π (g.1.symm (g.1 (s w))) := h
          _ = w := by
            rw [g.1.symm_apply_apply, hsection]
      right_inv := by
        intro w
        have h := hcongr g
          (s (π (g.1.symm (s w)))) (g.1.symm (s w))
          (hsection _)
        calc
          π (g.1 (s (π (g.1.symm (s w))))) =
              π (g.1 (g.1.symm (s w))) := h
          _ = w := by
            rw [g.1.apply_symm_apply, hsection] }
  map_one' := by
    apply Equiv.ext
    intro w
    change π (s w) = w
    exact hsection w
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro w
    change
      π (g.1 (h.1 (s w))) =
        π (g.1 (s (π (h.1 (s w)))))
    exact hcongr g _ _ (hsection _).symm

/-- The descended action agrees with the original action on every vertex. -/
theorem fiberActionHom_apply {V W : Type*}
    (G : Subgroup (Equiv.Perm V))
    (π : V → W) (s : W → V)
    (hsection : ∀ w, π (s w) = w)
    (hcongr : ∀ g : G, ∀ x y : V,
      π x = π y → π (g.1 x) = π (g.1 y))
    (g : G) (x : V) :
    fiberActionHom G π s hsection hcongr g (π x) =
      π (g.1 x) := by
  change π (g.1 (s (π x))) = π (g.1 x)
  exact hcongr g _ _ (hsection _)

end AlbertsonCollins

#print axioms AlbertsonCollins.fiberActionHom
#print axioms AlbertsonCollins.fiberActionHom_apply

open scoped Pointwise

namespace AlbertsonCollins

/-- Elements of G preserve membership of differences in a block through zero. -/
theorem shift_block_difference_forward {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (g : G) (x y : ZMod n)
    (hxy : y - x ∈ B) :
    g.1 y - g.1 x ∈ B := by
  let k : G :=
    ⟨residueTranslation (-g.1 x),
      all_translations_mem G h1 (-g.1 x)⟩ *
    g *
    ⟨residueTranslation x, all_translations_mem G h1 x⟩
  have hkzero : k.1 0 = 0 := by
    change g.1 (0 + x) + (-g.1 x) = 0
    simp
  have hkB : k • B = B := by
    rw [group_block_image_is_translate G h1 B hzero hB k,
      hkzero]
    simp
  have hm : k.1 (y - x) ∈ k • B := by
    change k.1 (y - x) ∈ (fun z => k.1 z) '' B
    exact ⟨y - x, hxy, rfl⟩
  rw [hkB] at hm
  change g.1 ((y - x) + x) + (-g.1 x) ∈ B at hm
  rw [sub_add_cancel] at hm
  simpa only [sub_eq_add_neg] using hm

/-- The same-block relation is preserved in both directions. -/
theorem shift_block_difference_iff {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (g : G) (x y : ZMod n) :
    y - x ∈ B ↔ g.1 y - g.1 x ∈ B := by
  constructor
  · exact shift_block_difference_forward G h1 B hzero hB g x y
  · intro h
    have h' := shift_block_difference_forward
      G h1 B hzero hB (g⁻¹) (g.1 x) (g.1 y) h
    change
      g.1.symm (g.1 y) - g.1.symm (g.1 x) ∈ B at h'
    simpa only [Equiv.symm_apply_apply] using h'

end AlbertsonCollins

#print axioms AlbertsonCollins.shift_block_difference_iff

namespace AlbertsonCollins

/-- Divisibility of a residue difference means equal remainders modulo a. -/
theorem residue_difference_mod_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (x y : ZMod (a * b)) :
    a ∣ (y - x).val ↔ x.val % a = y.val % a := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  let p : ZMod (a * b) →+* ZMod a :=
    ZMod.castHom (show a ∣ a * b from ⟨b, rfl⟩) (ZMod a)
  have hval (z : ZMod (a * b)) :
      p z = (z.val : ZMod a) := by
    exact ZMod.cast_eq_val z
  calc
    a ∣ (y - x).val ↔
        ((y - x).val : ZMod a) = 0 :=
      (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).symm
    _ ↔ p (y - x) = 0 := by rw [hval]
    _ ↔ p y = p x := by rw [map_sub, sub_eq_zero]
    _ ↔ y.val % a = x.val % a := by
      rw [hval, hval, ZMod.natCast_eq_natCast_iff']
    _ ↔ x.val % a = y.val % a := eq_comm

/-- The first coordinate identifies the residue block. -/
def residueBlockIndex (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (x : ZMod (a * b)) : Fin a :=
  (residueBlockCoordinates a b ha hb x).1

/-- Equal block indices are equivalent to a difference in the zero block. -/
theorem residueBlockIndex_eq_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (x y : ZMod (a * b)) :
    residueBlockIndex a b ha hb x =
        residueBlockIndex a b ha hb y ↔
      y - x ∈ residueBlock a b ⟨0, ha⟩ := by
  constructor
  · intro h
    have hm : x.val % a = y.val % a :=
      congrArg (fun r : Fin a => r.val) h
    change (y - x).val % a = 0
    exact Nat.mod_eq_zero_of_dvd
      ((residue_difference_mod_iff a b ha hb x y).2 hm)
  · intro h
    change (y - x).val % a = 0 at h
    apply Fin.ext
    change x.val % a = y.val % a
    exact (residue_difference_mod_iff a b ha hb x y).1
      (Nat.dvd_of_mod_eq_zero h)

end AlbertsonCollins

#print axioms AlbertsonCollins.residue_difference_mod_iff
#print axioms AlbertsonCollins.residueBlockIndex_eq_iff

namespace AlbertsonCollins

/-- Choose position zero as the representative of each block. -/
def residueBlockRepresentative (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (r : Fin a) :
    ZMod (a * b) :=
  (residueBlockCoordinates a b ha hb).symm (r, ⟨0, hb⟩)

/-- The chosen representative has the specified block index. -/
theorem residueBlockIndex_representative (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (r : Fin a) :
    residueBlockIndex a b ha hb
      (residueBlockRepresentative a b ha hb r) = r := by
  exact congrArg (fun p : Fin a × Fin b => p.1)
    ((residueBlockCoordinates a b ha hb).apply_symm_apply
      (r, ⟨0, hb⟩))

/-- The genuine block property makes the index relation invariant under G. -/
theorem residueBlockIndex_congr (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩)) :
    ∀ g : G, ∀ x y : ZMod (a * b),
      residueBlockIndex a b ha hb x =
          residueBlockIndex a b ha hb y →
        residueBlockIndex a b ha hb (g.1 x) =
          residueBlockIndex a b ha hb (g.1 y) := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  intro g x y hxy
  apply (residueBlockIndex_eq_iff
    a b ha hb (g.1 x) (g.1 y)).2
  exact shift_block_difference_forward
    G h1 (residueBlock a b ⟨0, ha⟩)
    (by simp [residueBlock]) hB g x y
    ((residueBlockIndex_eq_iff a b ha hb x y).1 hxy)

/-- The homomorphism describing the action of G on residue-block indices. -/
def blockIndexActionHom (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩)) :
    G →* Equiv.Perm (Fin a) :=
  fiberActionHom G
    (residueBlockIndex a b ha hb)
    (residueBlockRepresentative a b ha hb)
    (residueBlockIndex_representative a b ha hb)
    (residueBlockIndex_congr a b ha hb G h1 hB)

/-- Taking block indices commutes with the group action. -/
theorem blockIndexActionHom_apply (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩))
    (g : G) (x : ZMod (a * b)) :
    blockIndexActionHom a b ha hb G h1 hB g
        (residueBlockIndex a b ha hb x) =
      residueBlockIndex a b ha hb (g.1 x) := by
  exact fiberActionHom_apply G
    (residueBlockIndex a b ha hb)
    (residueBlockRepresentative a b ha hb)
    (residueBlockIndex_representative a b ha hb)
    (residueBlockIndex_congr a b ha hb G h1 hB) g x

end AlbertsonCollins

#print axioms AlbertsonCollins.blockIndexActionHom
#print axioms AlbertsonCollins.blockIndexActionHom_apply

namespace AlbertsonCollins

/-- The permutation group induced on the block indices. -/
def blockIndexActionGroup (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩)) :
    Subgroup (Equiv.Perm (Fin a)) :=
  (blockIndexActionHom a b ha hb G h1 hB).range

/-- Odd order passes to the action on block indices. -/
theorem blockIndexActionGroup_odd (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩))
    (hodd : Odd (Nat.card G)) :
    Odd (Nat.card (blockIndexActionGroup a b ha hb G h1 hB)) := by
  exact hodd.of_dvd_nat
    (Subgroup.card_range_dvd
      (blockIndexActionHom a b ha hb G h1 hB))

/-- Trivial action on block indices is equivalent to preserving every block. -/
theorem blockIndexAction_eq_one_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩))
    (g : G) :
    blockIndexActionHom a b ha hb G h1 hB g = 1 ↔
      ∀ r : Fin a, PermStabilizes (residueBlock a b r) g.1 := by
  constructor
  · intro hid
    have hidx (x : ZMod (a * b)) :
        residueBlockIndex a b ha hb (g.1 x) =
          residueBlockIndex a b ha hb x := by
      have h := blockIndexActionHom_apply a b ha hb G h1 hB g x
      rw [hid] at h
      exact h.symm
    intro r x
    rw [mem_residueBlock_iff a b ha hb r (g.1 x),
      mem_residueBlock_iff a b ha hb r x]
    change
      residueBlockIndex a b ha hb (g.1 x) = r ↔
        residueBlockIndex a b ha hb x = r
    rw [hidx x]
  · intro hblocks
    apply Equiv.ext
    intro r
    let x := residueBlockRepresentative a b ha hb r
    have hxidx : residueBlockIndex a b ha hb x = r :=
      residueBlockIndex_representative a b ha hb r
    have hxmem : x ∈ residueBlock a b r :=
      (mem_residueBlock_iff a b ha hb r x).2 hxidx
    have hgmem : g.1 x ∈ residueBlock a b r :=
      (hblocks r x).2 hxmem
    have hgidx : residueBlockIndex a b ha hb (g.1 x) = r :=
      (mem_residueBlock_iff a b ha hb r (g.1 x)).1 hgmem
    have hact := blockIndexActionHom_apply a b ha hb G h1 hB g x
    rw [hxidx] at hact
    exact hact.trans hgidx

end AlbertsonCollins

#print axioms AlbertsonCollins.blockIndexActionGroup_odd
#print axioms AlbertsonCollins.blockIndexAction_eq_one_iff

namespace AlbertsonCollins

/-- Rotation increases the representative by one modulo the degree. -/
theorem finRotate_val_mod (a : Nat) (ha : 0 < a) (r : Fin a) :
    (finRotate a r).val = (r.val + 1) % a := by
  cases a with
  | zero => omega
  | succ k =>
    rw [coe_finRotate]
    split_ifs with h
    · have hr : r.val = k :=
        congrArg (fun z : Fin (k + 1) => z.val) h
      rw [hr]
      simp
    · have hne : r.val ≠ k := by
        intro hval
        apply h
        exact Fin.ext hval
      have hr : r.val < k := by
        have := r.isLt
        omega
      rw [Nat.mod_eq_of_lt (show r.val + 1 < k + 1 by omega)]

/-- Translation by one rotates the block index by one. -/
theorem residueBlockIndex_add_one (a b : Nat)
    (ha : 0 < a) (hb : 0 < b) (x : ZMod (a * b)) :
    residueBlockIndex a b ha hb (x + 1) =
      finRotate a (residueBlockIndex a b ha hb x) := by
  letI : NeZero (a * b) :=
    ⟨Nat.ne_of_gt (Nat.mul_pos ha hb)⟩
  apply Fin.ext
  change
    (x + 1).val % a =
      (finRotate a (residueBlockIndex a b ha hb x)).val
  rw [finRotate_val_mod a ha]
  change (x + 1).val % a = (x.val % a + 1) % a
  have hx :
      ((x.val + 1 : Nat) : ZMod (a * b)) = x + 1 := by
    rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  rw [← hx, ZMod.val_natCast,
    Nat.mod_mod_of_dvd _ (show a ∣ a * b from ⟨b, rfl⟩)]
  calc
    (x.val + 1) % a = (x.val % a + 1 % a) % a :=
      Nat.add_mod _ _ _
    _ = (x.val % a + 1) % a := by
      simpa only [Nat.mod_mod] using
        (Nat.add_mod (x.val % a) 1 a).symm

/-- The group induced on block indices contains the standard rotation. -/
theorem finRotate_mem_blockIndexActionGroup (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩)) :
    finRotate a ∈ blockIndexActionGroup a b ha hb G h1 hB := by
  let g : G := ⟨residueTranslation (1 : ZMod (a * b)), h1⟩
  change finRotate a ∈ (blockIndexActionHom a b ha hb G h1 hB).range
  refine ⟨g, ?_⟩
  apply Equiv.ext
  intro r
  let x := residueBlockRepresentative a b ha hb r
  have hrep : residueBlockIndex a b ha hb x = r :=
    residueBlockIndex_representative a b ha hb r
  have hact := blockIndexActionHom_apply a b ha hb G h1 hB g x
  rw [hrep] at hact
  have hshift := residueBlockIndex_add_one a b ha hb x
  rw [hrep] at hshift
  exact hact.trans hshift

end AlbertsonCollins

#print axioms AlbertsonCollins.residueBlockIndex_add_one
#print axioms AlbertsonCollins.finRotate_mem_blockIndexActionGroup

namespace AlbertsonCollins

/-- The half-interval vertices belonging to a specified block. -/
def blockHalfVertices (a b : Nat) (r : Fin a) : Type :=
  {x : ZMod (a * b) //
    x ∈ residueBlock a b r ∧ x.val ≤ (a * b - 1) / 2}

/-- A lower segment of Fin n has the expected coordinate type. -/
def finiteLowerSegmentEquiv (m n : Nat) (hm : m ≤ n) :
    Fin m ≃ {t : Fin n // t.val < m} where
  toFun := fun t =>
    ⟨⟨t.val, lt_of_lt_of_le t.isLt hm⟩, t.isLt⟩
  invFun := fun t => ⟨t.val.val, t.property⟩
  left_inv := by
    intro t
    apply Fin.ext
    rfl
  right_inv := by
    intro t
    apply Subtype.ext
    apply Fin.ext
    rfl

/-- High and low blocks have respectively v+1 and v half-interval vertices. -/
theorem blockHalfVertices_card (u v : Nat) (r : Fin (2 * u + 1)) :
    Nat.card (blockHalfVertices (2 * u + 1) (2 * v + 1) r) =
      if r.val ≤ u then v + 1 else v := by
  let m := if r.val ≤ u then v + 1 else v
  let e := residueBlockEquiv (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) r
  have hm : m ≤ 2 * v + 1 := by
    dsimp [m]
    split_ifs <;> omega
  have hcoords (t : Fin (2 * v + 1)) :
      t.val < m ↔
        (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2 := by
    have h := block_half_in_residue_coordinates u v r t
    change
      t.val < (if r.val ≤ u then v + 1 else v) ↔
        (e t).val.val ≤
          ((2 * u + 1) * (2 * v + 1) - 1) / 2
    split_ifs with hr
    · rw [if_pos hr] at h
      have ht : t.val < v + 1 ↔ t.val ≤ v := by omega
      exact ht.trans h.symm
    · rw [if_neg hr] at h
      exact h.symm
  let f :=
    (finiteLowerSegmentEquiv m (2 * v + 1) hm).trans
      ((e.subtypeEquiv hcoords).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter
          (fun x : ZMod ((2 * u + 1) * (2 * v + 1)) =>
            x ∈ residueBlock (2 * u + 1) (2 * v + 1) r)
          (fun x => x.val ≤
            ((2 * u + 1) * (2 * v + 1) - 1) / 2)))
  have hc := Nat.card_congr f.symm
  simpa [blockHalfVertices, m] using hc

end AlbertsonCollins

#print axioms AlbertsonCollins.blockHalfVertices_card

namespace AlbertsonCollins

/-- An element sends membership in a block to membership in its image block. -/
theorem blockIndexAction_block_iff (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩))
    (g : G) (r : Fin a) (x : ZMod (a * b)) :
    g.1 x ∈ residueBlock a b
        (blockIndexActionHom a b ha hb G h1 hB g r) ↔
      x ∈ residueBlock a b r := by
  rw [mem_residueBlock_iff a b ha hb
      (blockIndexActionHom a b ha hb G h1 hB g r) (g.1 x),
    mem_residueBlock_iff a b ha hb r x]
  change
    residueBlockIndex a b ha hb (g.1 x) =
        blockIndexActionHom a b ha hb G h1 hB g r ↔
      residueBlockIndex a b ha hb x = r
  rw [← blockIndexActionHom_apply a b ha hb G h1 hB g x]
  constructor
  · intro h
    exact (blockIndexActionHom a b ha hb G h1 hB g).injective h
  · intro h
    exact congrArg (blockIndexActionHom a b ha hb G h1 hB g) h

/-- A half-preserving element gives a bijection between block intersections. -/
def blockHalfActionEquiv (a b : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (G : Subgroup (Equiv.Perm (ZMod (a * b))))
    (h1 : residueTranslation (1 : ZMod (a * b)) ∈ G)
    (hB : MulAction.IsBlock G (residueBlock a b ⟨0, ha⟩))
    (g : G)
    (hhalf : PermStabilizes
      {x : ZMod (a * b) | x.val ≤ (a * b - 1) / 2} g.1)
    (r : Fin a) :
    blockHalfVertices a b r ≃
      blockHalfVertices a b
        (blockIndexActionHom a b ha hb G h1 hB g r) :=
  g.1.subtypeEquiv (by
    intro x
    exact and_congr
      (blockIndexAction_block_iff a b ha hb G h1 hB g r x).symm
      (hhalf x).symm)

/-- Preserving the original half forces preservation of the high block indices. -/
theorem blockIndexAction_preserves_half (u v : Nat)
    (G : Subgroup
      (Equiv.Perm (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (h1 : residueTranslation
      (1 : ZMod ((2 * u + 1) * (2 * v + 1))) ∈ G)
    (hB : MulAction.IsBlock G
      (residueBlock (2 * u + 1) (2 * v + 1) ⟨0, by omega⟩))
    (g : G)
    (hhalf : PermStabilizes
      {x : ZMod ((2 * u + 1) * (2 * v + 1)) |
        x.val ≤ ((2 * u + 1) * (2 * v + 1) - 1) / 2} g.1) :
    PermStabilizes (halfSet (2 * u + 1))
      (blockIndexActionHom (2 * u + 1) (2 * v + 1)
        (by omega) (by omega) G h1 hB g) := by
  intro r
  have hc := Nat.card_congr
    (blockHalfActionEquiv (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) G h1 hB g hhalf r)
  rw [blockHalfVertices_card, blockHalfVertices_card] at hc
  change
    (blockIndexActionHom (2 * u + 1) (2 * v + 1)
      (by omega) (by omega) G h1 hB g r).val ≤
        (2 * u + 1 - 1) / 2 ↔
      r.val ≤ (2 * u + 1 - 1) / 2
  have hu : (2 * u + 1 - 1) / 2 = u := by omega
  rw [hu]
  split_ifs at hc <;> omega

end AlbertsonCollins

#print axioms AlbertsonCollins.blockHalfActionEquiv
#print axioms AlbertsonCollins.blockIndexAction_preserves_half

namespace AlbertsonCollins

/-- The two smaller-degree statements imply the theorem for a residue block system. -/
theorem residue_block_induction_step
    (u v : Nat)
    (G : Subgroup
      (Equiv.Perm (ZMod ((2 * u + 1) * (2 * v + 1)))))
    (hodd : Odd (Nat.card G))
    (h1 : residueTranslation
      (1 : ZMod ((2 * u + 1) * (2 * v + 1))) ∈ G)
    (hB : MulAction.IsBlock G
      (residueBlock (2 * u + 1) (2 * v + 1) ⟨0, by omega⟩))
    (hindex :
      ∀ H : Subgroup (Equiv.Perm (Fin (2 * u + 1))),
        Odd (Nat.card H) → finRotate (2 * u + 1) ∈ H →
          RegularSubset H (halfSet (2 * u + 1)))
    (hsmall :
      ∀ H : Subgroup (Equiv.Perm (Fin (2 * v + 1))),
        Odd (Nat.card H) → finRotate (2 * v + 1) ∈ H →
          RegularSubset H (halfSet (2 * v + 1))) :
    RegularSubset G
      {x : ZMod ((2 * u + 1) * (2 * v + 1)) |
        x.val ≤ ((2 * u + 1) * (2 * v + 1) - 1) / 2} := by
  intro f hf hhalf
  let g : G := ⟨f, hf⟩
  let Q := blockIndexActionGroup (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G h1 hB
  let q := blockIndexActionHom (2 * u + 1) (2 * v + 1)
    (by omega) (by omega) G h1 hB g
  have hregularQ : RegularSubset Q (halfSet (2 * u + 1)) :=
    hindex Q
      (blockIndexActionGroup_odd
        _ _ (by omega) (by omega) G h1 hB hodd)
      (finRotate_mem_blockIndexActionGroup
        _ _ (by omega) (by omega) G h1 hB)
  have hqmem : q ∈ Q := ⟨g, rfl⟩
  have hqhalf : PermStabilizes (halfSet (2 * u + 1)) q :=
    blockIndexAction_preserves_half u v G h1 hB g hhalf
  have hid : q = 1 := hregularQ q hqmem hqhalf
  have hblocks :=
    (blockIndexAction_eq_one_iff
      _ _ (by omega) (by omega) G h1 hB g).1 hid
  exact blockwise_identity_of_smaller_case
    u v G hodd h1 hsmall g hblocks hhalf

end AlbertsonCollins

#print axioms AlbertsonCollins.residue_block_induction_step

namespace AlbertsonCollins

/-- An arbitrary nontrivial block reduces the theorem to smaller degrees. -/
theorem nontrivial_block_induction_step
    (n : Nat) (hn : 0 < n) (hnodd : Odd n)
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (hodd : Odd (Nat.card G))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (hproper : B ≠ Set.univ)
    (hnontrivial : ∃ x : ZMod n, x ∈ B ∧ x ≠ 0)
    (ih : ∀ m : Nat, m < n → Odd m →
      ∀ H : Subgroup (Equiv.Perm (Fin m)),
        Odd (Nat.card H) → finRotate m ∈ H →
          RegularSubset H (halfSet m)) :
    RegularSubset G {x : ZMod n | x.val ≤ (n - 1) / 2} := by
  obtain ⟨a, b, hnab, haodd, hbodd, ha, han, hb, hbn, hmem⟩ :=
    nontrivial_shift_block_factors
      hn hnodd G h1 B hzero hB hproper hnontrivial
  obtain ⟨u, hu⟩ := haodd
  obtain ⟨v, hv⟩ := hbodd
  have hau : a = 2 * u + 1 := by omega
  have hbv : b = 2 * v + 1 := by omega
  subst a
  subst b
  subst n
  have hBeq :
      B = residueBlock (2 * u + 1) (2 * v + 1)
        ⟨0, by omega⟩ := by
    ext x
    rw [hmem x]
    change
      (2 * u + 1) ∣ x.val ↔
        x.val % (2 * u + 1) = 0
    constructor
    · exact Nat.mod_eq_zero_of_dvd
    · exact Nat.dvd_of_mod_eq_zero
  have hB' : MulAction.IsBlock G
      (residueBlock (2 * u + 1) (2 * v + 1)
        ⟨0, by omega⟩) := by
    rw [← hBeq]
    exact hB
  exact residue_block_induction_step u v G hodd h1 hB'
    (ih (2 * u + 1) han ⟨u, by omega⟩)
    (ih (2 * v + 1) hbn ⟨v, by omega⟩)

end AlbertsonCollins

#print axioms AlbertsonCollins.nontrivial_block_induction_step
