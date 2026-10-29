import AlbertsonCollins.GroupInterface

/-!
# Actual cyclic tournaments (UNCOMPILED DRAFT)

The convention agrees with the Python module and the paper:
    arc u v iff v - u belongs to S.
The zero residue is excluded, and exactly one of d,-d is chosen for each
nonzero residue. Numeric labels 1 and 2 are fixed, not interchangeable.

These proof terms have not been compiled or kernel-checked. The remaining
Fin n / ZMod n bridge is described in README.md.
-/

namespace AlbertsonCollins

/-- The same input conditions as the executable cyclic-tournament constructor. -/
structure CyclicConnector (n : Nat) where
  positive : 0 < n
  odd : Odd n
  S : Set (ZMod n)
  zero_not_mem : (0 : ZMod n) ∉ S
  choose_one : ∀ d : ZMod n, d ≠ 0 →
    (d ∈ S ∨ -d ∈ S) ∧ ¬ (d ∈ S ∧ -d ∈ S)

/-- The actual directed graph determined by a connector set. -/
def CyclicConnector.tournament {n : Nat} (C : CyclicConnector n) :
    Tournament (ZMod n) where
  Arc u v := v - u ∈ C.S
  loopless := by
    intro u
    simpa only [sub_self] using C.zero_not_mem
  asymmetric := by
    intro u v huv hvu
    have hd : v - u ≠ 0 := by
      intro hzero
      have hz : (0 : ZMod n) ∈ C.S := by
        simpa only [hzero] using huv
      exact C.zero_not_mem hz
    apply (C.choose_one (v - u) hd).2
    exact ⟨huv, by simpa only [neg_sub] using hvu⟩
  complete := by
    intro u v hne
    have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rcases (C.choose_one (v - u) hd).1 with hforward | hbackward
    · exact Or.inl hforward
    · exact Or.inr (by simpa only [neg_sub] using hbackward)

/-- Translation is a genuine permutation with explicitly given inverse. -/
def residueTranslation {n : Nat} (t : ZMod n) : Equiv.Perm (ZMod n) where
  toFun x := x + t
  invFun x := x - t
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

/-- Every residue translation preserves all arc directions. -/
theorem CyclicConnector.translation_arcPreserving {n : Nat}
    (C : CyclicConnector n) (t : ZMod n) :
    ArcPreserving C.tournament (residueTranslation t) := by
  intro u v
  change (v + t - (u + t) ∈ C.S) ↔ (v - u ∈ C.S)
  have hsub : v + t - (u + t) = v - u := by abel
  rw [hsub]

/-- Thus every translation belongs to the constructed automorphism group. -/
theorem CyclicConnector.translation_mem_autGroup {n : Nat}
    (C : CyclicConnector n) (t : ZMod n) :
    residueTranslation t ∈ C.tournament.autGroup :=
  C.translation_arcPreserving t

/-- Odd order of the automorphism group for these concrete cyclic tournaments. -/
theorem CyclicConnector.autGroup_odd {n : Nat} (C : CyclicConnector n) :
    Odd (Nat.card C.tournament.autGroup) := by
  letI : NeZero n := ⟨ne_of_gt C.positive⟩
  exact C.tournament.autGroup_odd

/-- The exact labels used by the executable constructor. -/
def CyclicConnector.canonicalColor {n : Nat} (_C : CyclicConnector n)
    (x : ZMod n) : Nat :=
  if x.val ≤ (n - 1) / 2 then 1 else 2

/-- The directed 3-cycle: S = {1}. -/
def cycle3Connector : CyclicConnector 3 where
  positive := by decide
  odd := ⟨1, by decide⟩
  S := {d | d = 1}
  zero_not_mem := by decide
  choose_one := by decide

/-- The Paley tournament on 7 vertices: S = {1,2,4}. -/
def paley7Connector : CyclicConnector 7 where
  positive := by decide
  odd := ⟨3, by decide⟩
  S := {d | d = 1 ∨ d = 2 ∨ d = 4}
  zero_not_mem := by decide
  choose_one := by decide

/-- Actual small graph objects, with vertices ZMod 3 and ZMod 7 respectively. -/
def cycle3 : Tournament (ZMod 3) := cycle3Connector.tournament

def paley7 : Tournament (ZMod 7) := paley7Connector.tournament

end AlbertsonCollins
