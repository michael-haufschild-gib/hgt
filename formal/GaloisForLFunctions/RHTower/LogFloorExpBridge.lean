import Mathlib

/-!
# Logarithm/exponential floor bridge

The positive-natural logarithmic threshold `log n ≤ t` is exactly the natural-floor cutoff
`n ≤ ⌊exp t⌋ₙ`.  This small module keeps that elementary interface independent of its
original Báez--Duarte application.
-/

namespace RHTower

/-- A positive natural lies below `exp t` exactly when its logarithm lies below `t`. -/
theorem log_le_iff_le_floor {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    Real.log n ≤ t ↔ n ≤ ⌊Real.exp t⌋₊ := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Nat.le_floor_iff (Real.exp_pos t).le]
  constructor
  · intro h
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr h
  · intro h
    have := Real.log_le_log hn0 h
    rwa [Real.log_exp] at this

end RHTower
