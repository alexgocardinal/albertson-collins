import AlbertsonCollins.BlockActions

open scoped Pointwise

namespace AlbertsonCollins

/-- Containing the shift makes the action transitive. -/
theorem shift_group_pretransitive {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G) :
    MulAction.IsPretransitive G (ZMod n) := by
  constructor
  intro x y
  refine ⟨⟨residueTranslation (y - x),
    all_translations_mem G h1 (y - x)⟩, ?_⟩
  change x + (y - x) = y
  abel

/-- Every group image of a block containing zero is an additive translate. -/
theorem group_block_image_is_translate {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B)
    (g : G) :
    g • B = (fun x => x + g.1 0) '' B := by
  let t : G :=
    ⟨residueTranslation (g.1 0),
      all_translations_mem G h1 (g.1 0)⟩
  have himage :
      t • B = (fun x => x + g.1 0) '' B := rfl
  rw [← himage]
  apply hB.smul_eq_smul_of_nonempty
  refine ⟨g.1 0, ?_, ?_⟩
  · change g.1 0 ∈ (fun x => g.1 x) '' B
    exact ⟨0, hzero, rfl⟩
  · change g.1 0 ∈ (fun x => x + g.1 0) '' B
    exact ⟨0, hzero, by simp⟩

end AlbertsonCollins

#print axioms AlbertsonCollins.shift_group_pretransitive
#print axioms AlbertsonCollins.group_block_image_is_translate
