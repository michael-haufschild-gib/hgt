import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLogarithmicCenterRowCancelsThePole
import GaloisForLFunctions.HTGeometry.HarmonicCenterBoundaryBounds

/-!
# Bounded ground residual of the complete center correction

The two pole rows cancel the harmonic bulk of the archimedean center row.
The exact harmonic boundary square bound then controls the remaining residual
uniformly in the horizon.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

/-- The center correction shifts the pole by its charge, with a bounded square residual. -/
theorem sum_sq_centerCorrection_pole_residual_le (α : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N,
      ((α / N) * (∑ j ∈ Icc 1 N,
        ((Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) - archimedeanCenterKernel n j) /
          Real.sqrt j) - α / Real.sqrt n) ^ 2) ≤ 6 * α ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Icc_eq_empty_of_lt (by omega : 0 < 1), sum_empty]
    positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((α / N) * (∑ j ∈ Icc 1 N,
        ((Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) - archimedeanCenterKernel n j) /
          Real.sqrt j) - α / Real.sqrt n) ^ 2 =
      (α / N) ^ 2 * ((n : ℝ) *
        ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
          3 / (4 * (n : ℝ))) ^ 2) := by
    rw [sum_pole_minus_center_div_sqrt hn]
    have heq : (α / N) * ((N : ℝ) / Real.sqrt n + Real.sqrt n *
        ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
          3 / (4 * (n : ℝ)))) - α / Real.sqrt n =
      (α / N) * Real.sqrt n *
        ((harmonic N : ℝ) - ((harmonic (N - n) : ℝ) + harmonic (N + n)) / 2 +
          3 / (4 * (n : ℝ))) := by
      rw [mul_add, div_mul_div_cancel₀ hN0.ne']
      ring
    rw [heq, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    ring
  rw [sum_congr rfl hterm, ← mul_sum]
  calc
    _ ≤ (α / N) ^ 2 * (6 * (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_weighted_sq_harmonic_center_boundary_le N)
        (sq_nonneg _)
    _ = _ := by field_simp [hN0.ne']

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
