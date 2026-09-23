import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanMinorProduct
import GaloisForLFunctions.HTGeometry.RealComplexSiegelSelectedMinor

/-!
# Weighted logarithmic aggregation for archimedean frame minors

Local selected-minor inequalities become additive after taking logarithms.  The weighted finite
sum below retains the global minor term with coefficient two; any nonnegative product-formula
lower bound for that term can then be discarded.  This isolates the exact scalar mechanism used
to pass from real and complex Siegel estimates to a global number-field inequality.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- A positive multiplicative selected-minor bound implies its additive logarithmic form. -/
theorem log_mul_sq_le_log_mul
    {a p z b y : ℝ} (ha : 0 < a) (hp : 0 < p) (hz : 0 < z)
    (hb : 0 < b) (hy : 0 < y)
    (hlocal : a * p * z ^ (2 : ℕ) ≤ b * y) :
    Real.log a + Real.log p + 2 * Real.log z ≤
      Real.log b + Real.log y := by
  have hleft : 0 < a * p * z ^ (2 : ℕ) := mul_pos (mul_pos ha hp) (sq_pos_of_pos hz)
  have hlog := Real.log_le_log hleft hlocal
  rw [Real.log_mul (mul_ne_zero ha.ne' hp.ne') (pow_ne_zero 2 hz.ne'),
    Real.log_mul ha.ne' hp.ne', Real.log_pow, Real.log_mul hb.ne' hy.ne'] at hlog
  simpa [two_mul] using hlog

/-- Weighted local logarithmic inequalities aggregate globally; a nonnegative total minor log
term contributes with the correct sign and therefore needs no placewise lower bound. -/
theorem weighted_log_sum_le
    {ι : Type*} [Fintype ι]
    (m p z y : ι → ℝ) {a b : ℝ}
    (hm : ∀ i, 0 ≤ m i)
    (hlocal : ∀ i,
      Real.log a + Real.log (p i) + 2 * Real.log (z i) ≤
        Real.log b + Real.log (y i))
    (hz : 0 ≤ ∑ i, m i * Real.log (z i)) :
    ∑ i, m i * Real.log (p i) ≤
      (∑ i, m i) * (Real.log b - Real.log a) +
        ∑ i, m i * Real.log (y i) := by
  classical
  have hterm (i : ι) :
      m i * (Real.log a + Real.log (p i) + 2 * Real.log (z i)) ≤
        m i * (Real.log b + Real.log (y i)) :=
    mul_le_mul_of_nonneg_left (hlocal i) (hm i)
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hterm i
  simp_rw [mul_add] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.sum_mul, ← Finset.sum_mul] at hsum
  have hz2 : 0 ≤ ∑ i, m i * (2 * Real.log (z i)) := by
    simpa [Finset.mul_sum, mul_assoc, mul_left_comm] using
      mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hz
  linarith

end GaloisForLFunctions.HTGeometry
