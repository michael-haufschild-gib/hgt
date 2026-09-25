import Mathlib

/-!
# Finite Euler deletion reflected about its moving cusp

For a finite list of shifts, reflection around the negative sum of the shifts
turns each one-sided deletion operator into its opposite-order dual.  Applied
to an even completed-theta source and shifts `log p`, this is the algebraic
core of the exact moving-cusp identity.  Arithmetic coefficients, cofinal
convergence, and the sign-changing limit are paper-proved separately.
-/

namespace RHTower

def affineDelete (a : ℝ) (r : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f x - r * f (x + a)

def affineDual (a : ℝ) (r : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f (x + a) - r * f x

def affineShiftSum : List (ℝ × ℂ) → ℝ
  | [] => 0
  | (a, _) :: xs => a + affineShiftSum xs

def affineDeleteList : List (ℝ × ℂ) → (ℝ → ℂ) → (ℝ → ℂ)
  | [], f => f
  | (a, r) :: xs, f => affineDelete a r (affineDeleteList xs f)

def affineDualList : List (ℝ × ℂ) → (ℝ → ℂ) → (ℝ → ℂ)
  | [], f => f
  | (a, r) :: xs, f => affineDual a r (affineDualList xs f)

/-- Reflection about the negative total shift exchanges finite deletion and dual action. -/
theorem affineDeleteList_reflect (xs : List (ℝ × ℂ)) (f : ℝ → ℂ) (x : ℝ) :
    affineDeleteList xs f (-affineShiftSum xs - x) =
      affineDualList xs (fun y => f (-y)) x := by
  induction xs generalizing f x with
  | nil => simp [affineDeleteList, affineDualList, affineShiftSum]
  | cons p xs ih =>
      rcases p with ⟨a, r⟩
      simp only [affineDeleteList, affineDualList, affineShiftSum,
        affineDelete, affineDual]
      have hy1 : -(a + affineShiftSum xs) - x =
          -affineShiftSum xs - (x + a) := by ring
      have hy2 : -(a + affineShiftSum xs) - x + a =
          -affineShiftSum xs - x := by ring
      rw [hy2, hy1, ih f (x + a), ih f x]

/-- For an even source, moving-cusp reflection acts directly on that same source. -/
theorem affineDeleteList_even_reflect (xs : List (ℝ × ℂ)) (f : ℝ → ℂ)
    (hf : Function.Even f) (x : ℝ) :
    affineDeleteList xs f (-affineShiftSum xs - x) =
      affineDualList xs f x := by
  rw [affineDeleteList_reflect]
  congr 1
  funext y
  exact hf y

end RHTower
