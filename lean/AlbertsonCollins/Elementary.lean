import Std

/-!
# Elementary foundation (UNCOMPILED DRAFT)

This module uses only Lean's standard library. It contains complete proof
terms for elementary parts of the argument, but no Lean executable was
available when it was written. Do not describe it as kernel-checked.
The universal canonical-half theorem is NOT proved here.
-/

namespace AlbertsonCollins

universe u

/-- A tournament has one directed arc between every pair of distinct vertices. -/
structure Tournament (V : Type u) where
  Arc : V → V → Prop
  loopless : ∀ x, ¬ Arc x x
  asymmetric : ∀ {x y}, Arc x y → ¬ Arc y x
  complete : ∀ {x y}, x ≠ y → Arc x y ∨ Arc y x

/-- The direction of every arc is preserved and reflected. -/
def ArcPreserving {V : Type u} (T : Tournament V) (f : V → V) : Prop :=
  ∀ x y, T.Arc (f x) (f y) ↔ T.Arc x y

/-- A function preserves a subset, represented by its membership predicate. -/
def Stabilizes {V : Type u} (S : V → Prop) (f : V → V) : Prop :=
  ∀ x, S (f x) ↔ S x

/-- Pointwise regularity for an explicitly specified collection of functions. -/
def RegularFor {V : Type u} (Allowed : (V → V) → Prop)
    (S : V → Prop) : Prop :=
  ∀ f, Allowed f → Stabilizes S f → ∀ x, f x = x

/-- The prescribed high half in the original vertex order. -/
def CanonicalHalf (q : Nat) (x : Fin (2 * q + 1)) : Prop :=
  x.val ≤ q

/-- Actual numeric labels 1 and 2; no permutation of the labels is permitted. -/
def twoColor {V : Type u} (S : V → Prop) [DecidablePred S] (x : V) : Nat :=
  if S x then 1 else 2

/-- Label preservation is exactly setwise preservation, including both directions. -/
theorem preserves_twoColor_iff {V : Type u} (S : V → Prop)
    [DecidablePred S] (f : V → V) :
    (∀ x, twoColor S (f x) = twoColor S x) ↔ Stabilizes S f := by
  constructor
  · intro h x
    constructor
    · intro hfx
      apply Classical.byContradiction
      intro hx
      have heq := h x
      simp [twoColor, hfx, hx] at heq
    · intro hx
      apply Classical.byContradiction
      intro hfx
      have heq := h x
      simp [twoColor, hfx, hx] at heq
  · intro h x
    by_cases hx : S x
    · have hfx := (h x).2 hx
      simp [twoColor, hfx, hx]
    · have hfx : ¬ S (f x) := fun hfx => hx ((h x).1 hfx)
      simp [twoColor, hfx, hx]

/-- A subset and its complement have exactly the same setwise stabilizers. -/
theorem stabilizes_complement_iff {V : Type u} (S : V → Prop)
    (f : V → V) :
    Stabilizes (fun x => ¬ S x) f ↔ Stabilizes S f := by
  classical
  constructor
  · intro h x
    constructor
    · intro hfx
      apply Classical.byContradiction
      intro hx
      exact ((h x).2 hx) hfx
    · intro hx
      apply Classical.byContradiction
      intro hfx
      exact ((h x).1 hfx) hx
  · intro h x
    constructor
    · intro hfx hx
      exact hfx ((h x).2 hx)
    · intro hx hfx
      exact hx ((h x).1 hfx)

/-- Therefore regularity passes to the complementary subset. -/
theorem regular_complement {V : Type u} (Allowed : (V → V) → Prop)
    (S : V → Prop) (hreg : RegularFor Allowed S) :
    RegularFor Allowed (fun x => ¬ S x) := by
  intro f hf hstab
  exact hreg f hf ((stabilizes_complement_iff S f).1 hstab)

/--
Regularity transports under a bijective change of coordinates, provided the
allowed collection is closed under the required conjugation.
This is the elementary mechanism behind using translates of the high half.
-/
theorem regular_transport {V : Type u} (Allowed : (V → V) → Prop)
    (S : V → Prop) (hreg : RegularFor Allowed S)
    (c cinv : V → V)
    (hleft : ∀ x, cinv (c x) = x)
    (hright : ∀ x, c (cinv x) = x)
    (hconj : ∀ f, Allowed f → Allowed (fun x => cinv (f (c x)))) :
    RegularFor Allowed (fun x => S (cinv x)) := by
  intro f hf hstab y
  have hstab' : Stabilizes S (fun x => cinv (f (c x))) := by
    intro x
    have h := hstab (c x)
    simpa only [hleft] using h
  have hfix := hreg (fun x => cinv (f (c x))) (hconj f hf) hstab'
  have h := congrArg c (hfix (cinv y))
  simpa only [hright] using h

/--
No nonidentity involution preserves a tournament.
No finiteness, group theory, Cauchy theorem, or classification is used here.
-/
theorem involutive_automorphism_fixed {V : Type u} (T : Tournament V)
    (f : V → V) (haut : ArcPreserving T f)
    (hinv : ∀ x, f (f x) = x) : ∀ x, f x = x := by
  classical
  intro x
  by_cases hx : f x = x
  · exact hx
  · have hne : x ≠ f x := fun h => hx h.symm
    cases T.complete hne with
    | inl hforward =>
      have h := (haut x (f x)).2 hforward
      have h' : T.Arc (f x) x := by
        simpa only [hinv x] using h
      exact False.elim (T.asymmetric hforward h')
    | inr hbackward =>
      have h := (haut (f x) x).2 hbackward
      have h' : T.Arc x (f x) := by
        simpa only [hinv x] using h
      exact False.elim (T.asymmetric h' hbackward)

end AlbertsonCollins
