import AlbertsonCollins.TranslationGeneration
import AlbertsonCollins.GroupBlocks
import AlbertsonCollins.Cyclic

open scoped Pointwise

namespace AlbertsonCollins

/-- A genuine group-action block has the required translation property. -/
theorem group_block_translation_property {n : Nat}
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (htranslations : ∀ t : ZMod n, residueTranslation t ∈ G)
    (B : Set (ZMod n))
    (hB : MulAction.IsBlock G B) :
    ∀ t : ZMod n,
      (fun x => x + t) '' B = B ∨
        Disjoint B ((fun x => x + t) '' B) := by
  intro t
  let g : G := ⟨residueTranslation t, htranslations t⟩
  have h := hB.smul_eq_or_disjoint g
  have hset :
      g • B = (fun x => x + t) '' B := rfl
  rw [hset] at h
  rcases h with heq | hd
  · exact Or.inl heq
  · exact Or.inr hd.symm

/-- A group-action block containing zero gives an additive subgroup. -/
def subgroupOfGroupBlock {n : Nat}
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (htranslations : ∀ t : ZMod n, residueTranslation t ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B) :
    AddSubgroup (ZMod n) :=
  translationBlockSubgroup B hzero
    (group_block_translation_property G htranslations B hB)

end AlbertsonCollins

namespace AlbertsonCollins

/-- A block containing zero is a subgroup when the group contains the shift. -/
def subgroupOfShiftBlock {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hB : MulAction.IsBlock G B) :
    AddSubgroup (ZMod n) :=
  subgroupOfGroupBlock G (all_translations_mem G h1) B hzero hB

end AlbertsonCollins

#print axioms AlbertsonCollins.all_translations_mem
#print axioms AlbertsonCollins.subgroupOfShiftBlock
