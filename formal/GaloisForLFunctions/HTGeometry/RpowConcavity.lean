import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary concavity bound for real powers

This small module isolates the one-sided secant estimate for `x ↦ x^β`, `β ≤ 1`, so analytic
modules can use it without importing arithmetic sieve infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A one-sided concavity bound for a real power. -/
theorem rpow_sub_rpow_le {A c β : ℝ} (hβ1 : β ≤ 1) (hc : 0 ≤ c) (hB : 0 < A - c) :
    A ^ β - (A - c) ^ β ≤ c * (A - c) ^ (β - 1) := by
  set B : ℝ := A - c with hBdef
  have hA : A = B + c := by rw [hBdef]; ring
  have hA0 : (0 : ℝ) < A := by rw [hA]; linarith
  have ht : (1 : ℝ) ≤ A / B := by
    rw [le_div_iff₀ hB]
    linarith
  have hsplit : A ^ β = B ^ β * (A / B) ^ β := by
    rw [← Real.mul_rpow hB.le (by positivity)]
    congr 1
    field_simp
  have hpow : (A / B) ^ β ≤ A / B := by
    have := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rwa [Real.rpow_one] at this
  have hB0 : (0 : ℝ) < B ^ β := Real.rpow_pos_of_pos hB β
  have hstep : A ^ β ≤ B ^ β * (A / B) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hpow hB0.le
  have hval : B ^ β * (A / B) - B ^ β = c * B ^ (β - 1) := by
    rw [Real.rpow_sub hB, Real.rpow_one]
    field_simp
    rw [hA]
    ring
  linarith [hstep, hval]

end GaloisForLFunctions.HTGeometry
