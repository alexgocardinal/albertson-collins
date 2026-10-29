import AlbertsonCollins.Cyclic

namespace AlbertsonCollins

/-- A group containing translation by one contains every natural-number shift. -/
theorem natural_translation_mem {n : Nat}
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (k : Nat) :
    residueTranslation (k : ZMod n) ∈ G := by
  induction k with
  | zero =>
      have heq : residueTranslation (0 : ZMod n) = 1 := by
        ext x
        change x + 0 = x
        exact add_zero x
      rw [Nat.cast_zero]
      rw [heq]
      exact G.one_mem
  | succ k hk =>
      have heq :
          residueTranslation ((k + 1 : Nat) : ZMod n) =
            residueTranslation (k : ZMod n) *
              residueTranslation (1 : ZMod n) := by
        ext x
        change x + ((k + 1 : Nat) : ZMod n) =
          (x + 1) + (k : ZMod n)
        rw [Nat.cast_add, Nat.cast_one]
        abel
      change residueTranslation ((k + 1 : Nat) : ZMod n) ∈ G
      rw [heq]
      exact G.mul_mem hk h1

/-- For nonzero modulus, every residue translation belongs to the group. -/
theorem all_translations_mem {n : Nat} [NeZero n]
    (G : Subgroup (Equiv.Perm (ZMod n)))
    (h1 : residueTranslation (1 : ZMod n) ∈ G)
    (t : ZMod n) :
    residueTranslation t ∈ G := by
  have h := natural_translation_mem G h1 t.val
  simpa only [ZMod.natCast_zmod_val] using h

end AlbertsonCollins
