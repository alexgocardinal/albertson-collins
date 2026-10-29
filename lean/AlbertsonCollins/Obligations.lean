import AlbertsonCollins.GroupInterface

/-!
# Precise arithmetic subgoals (UNPROVED)

Each declaration below DEFINES a proposition. None proves or assumes it.
The intended next step is a separately named theorem giving a term of each
type. See README.md for the group-action obligations that remain as well.
-/

namespace AlbertsonCollins

/-- Count the points of the high half in residue block r modulo a. -/
def blockHalfCount (a b r : Nat) : Nat :=
  ((Finset.range b).filter
    (fun t => r + a * t ≤ (a * b - 1) / 2)).card

/-- The exact high/low count used in the imprimitive induction. -/
def BlockHalfCountStatement : Prop :=
  ∀ a b : Nat, Odd a → Odd b → ∀ r : Nat, r < a →
    blockHalfCount a b r =
      if r ≤ (a - 1) / 2 then (b + 1) / 2 else (b - 1) / 2

/-- Number of points of I whose translate backwards by d is also in I. -/
def intervalCorrelation (q : Nat) (d : Fin (2 * q + 1)) : Nat :=
  ((Finset.univ : Finset (Fin (2 * q + 1))).filter
    (fun x => x.val ≤ q ∧
      (x.val + (2 * q + 1) - d.val) % (2 * q + 1) ≤ q)).card

/-- Exact correlation formula, including d = 0. -/
def IntervalCorrelationStatement : Prop :=
  ∀ q : Nat, ∀ d : Fin (2 * q + 1),
    intervalCorrelation q d =
      q + 1 - min d.val (2 * q + 1 - d.val)

/--
Prime-degree affine subgoal. The canonical half is measured in the original
residue representatives, not an arbitrary permutation of field elements.
-/
def AffineHalfMultiplierStatement : Prop :=
  ∀ p : Nat, Nat.Prime p → ∀ a b : ZMod p, a ≠ 0 →
    (∀ x : ZMod p,
      (a * x + b).val ≤ (p - 1) / 2 ↔ x.val ≤ (p - 1) / 2) →
    a = 1 ∨ a = -1

end AlbertsonCollins
