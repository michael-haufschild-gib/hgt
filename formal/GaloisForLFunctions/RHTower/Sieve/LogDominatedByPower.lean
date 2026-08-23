import GaloisForLFunctions.RHTower.Sieve.PerronContourAssembly

/-!
# The square of a logarithm is dominated by every power

Mathlib's `Real.log_le_rpow_div` gives `log y ≤ y^δ/δ`; squaring it at half the exponent absorbs a
`log²` into an arbitrarily small power, which is what turns `x^{1/2+ε/2} log²x` into `x^{1/2+ε}`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The square of a logarithm is dominated by every power. -/
theorem log_sq_le_rpow_div {y δ : ℝ} (hy : 1 ≤ y) (hδ : 0 < δ) :
    (Real.log y) ^ 2 ≤ y ^ δ / (δ / 2) ^ 2 := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hbase := Real.log_le_rpow_div hy0.le hδ2
  have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  have hsq : (Real.log y) ^ 2 ≤ (y ^ (δ / 2) / (δ / 2)) ^ 2 := by
    have hnn : (0 : ℝ) ≤ y ^ (δ / 2) / (δ / 2) := by positivity
    nlinarith [hbase, hlog0]
  refine hsq.trans (le_of_eq ?_)
  rw [div_pow, ← Real.rpow_natCast (y ^ (δ / 2)) 2, ← Real.rpow_mul hy0.le]
  congr 2
  push_cast
  ring

end

end RHTower.Sieve
