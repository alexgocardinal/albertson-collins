import AlbertsonCollins.GroupInterface

namespace AlbertsonCollins

/-- A block containing zero equals its translate by any of its members. -/
theorem translation_block_eq {n : Nat}
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hblock : ∀ t : ZMod n,
      (fun x => x + t) '' B = B ∨
        Disjoint B ((fun x => x + t) '' B))
    (t : ZMod n) (ht : t ∈ B) :
    (fun x => x + t) '' B = B := by
  rcases hblock t with heq | hd
  · exact heq
  · have himage : t ∈ (fun x => x + t) '' B :=
      ⟨0, hzero, by simp⟩
    exact False.elim ((Set.disjoint_left.mp hd) ht himage)

/-- Such a block is an actual additive subgroup of the residue group. -/
def translationBlockSubgroup {n : Nat}
    (B : Set (ZMod n))
    (hzero : (0 : ZMod n) ∈ B)
    (hblock : ∀ t : ZMod n,
      (fun x => x + t) '' B = B ∨
        Disjoint B ((fun x => x + t) '' B)) :
    AddSubgroup (ZMod n) where
  carrier := B
  zero_mem' := hzero
  add_mem' := by
    intro x y hx hy
    have heq := translation_block_eq B hzero hblock y hy
    have hm : x + y ∈ (fun z => z + y) '' B :=
      ⟨x, hx, rfl⟩
    rw [heq] at hm
    exact hm
  neg_mem' := by
    intro x hx
    have heq := translation_block_eq B hzero hblock x hx
    have hz : (0 : ZMod n) ∈ (fun z => z + x) '' B := by
      rw [heq]
      exact hzero
    obtain ⟨y, hy, hyx⟩ := hz
    have hyneg : y = -x := by
      have h := congrArg (fun z : ZMod n => z - x) hyx
      simpa using h
    simpa only [hyneg] using hy

end AlbertsonCollins
