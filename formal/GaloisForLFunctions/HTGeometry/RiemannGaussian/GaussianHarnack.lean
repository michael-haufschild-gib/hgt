import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianHeat
import GaloisForLFunctions.HilbertMetric.GaussianHarnack

/-!
# Harnack transport of Gaussian test functions

The existing translated and reflected Gaussian tests satisfy sharp positive-time
transport bounds. Equality for the reflected pair forces its two source centres
to coincide, as well as the straight-characteristic relation. Thus reflection
strictly improves the one-source bound away from the merged centre.
-/

namespace RiemannGaussian

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Pointwise heat transport for the translated Gaussian test. -/
theorem translatedGaussian_harnack (s r x y z : ℝ) :
    translatedGaussian (1 / (4 * Real.exp s)) x z ≤
      Real.exp ((x - y) ^ 2 / (4 * Real.exp r)) *
        translatedGaussian (1 / (4 * (Real.exp s + Real.exp r))) y z := by
  have h := gaussianHarnack s r x y z
  simpa only [translatedGaussian, Real.norm_eq_abs, sq_abs, neg_div, one_div,
    neg_mul, div_eq_mul_inv, sub_sq_comm z x, sub_sq_comm z y, mul_comm,
    one_mul, mul_neg] using h

/-- Reflection preserves the full Harnack comparison without regularity premises. -/
theorem symmetricGaussian_harnack (s r x y z : ℝ) :
    symmetricGaussian (1 / (4 * Real.exp s)) x z ≤
      Real.exp ((x - y) ^ 2 / (4 * Real.exp r)) *
        symmetricGaussian (1 / (4 * (Real.exp s + Real.exp r))) y z := by
  simpa only [symmetricGaussian, mul_add] using
    add_le_add (translatedGaussian_harnack s r x y z)
      (translatedGaussian_harnack s r x y (-z))

/-- Equality in a single translated test is precisely the characteristic relation. -/
theorem translatedGaussian_harnack_eq_iff (s r x y z : ℝ) :
    translatedGaussian (1 / (4 * Real.exp s)) x z =
        Real.exp ((x - y) ^ 2 / (4 * Real.exp r)) *
          translatedGaussian (1 / (4 * (Real.exp s + Real.exp r))) y z ↔
      Real.exp r * (x - z) = Real.exp s * (y - x) := by
  simpa only [translatedGaussian, Real.norm_eq_abs, sq_abs, neg_div, one_div,
    neg_mul, div_eq_mul_inv, sub_sq_comm z x, sub_sq_comm z y, mul_comm, smul_eq_mul,
    one_mul, mul_neg]
    using gaussianHarnack_eq_iff s r x y z

/-- The reflected bound is sharp only at a merged source centre. -/
theorem symmetricGaussian_harnack_eq_iff (s r x y z : ℝ) :
    symmetricGaussian (1 / (4 * Real.exp s)) x z =
        Real.exp ((x - y) ^ 2 / (4 * Real.exp r)) *
          symmetricGaussian (1 / (4 * (Real.exp s + Real.exp r))) y z ↔
      z = 0 ∧ (Real.exp s + Real.exp r) * x = Real.exp s * y := by
  have hp := translatedGaussian_harnack s r x y z
  have hm := translatedGaussian_harnack s r x y (-z)
  simp only [symmetricGaussian]
  constructor
  · intro h
    have ep := (translatedGaussian_harnack_eq_iff s r x y z).mp (by linarith)
    have em := (translatedGaussian_harnack_eq_iff s r x y (-z)).mp (by linarith)
    have hz : z = 0 := by nlinarith [Real.exp_pos r]
    exact ⟨hz, by rw [hz] at ep; nlinarith⟩
  · rintro ⟨rfl, h⟩
    have ep := (translatedGaussian_harnack_eq_iff s r x y 0).mpr (by nlinarith)
    rw [neg_zero, ep]
    ring

/-- Logarithmic transport cost for the positive reflected test. -/
theorem log_symmetricGaussian_harnack (s r x y z : ℝ) :
    Real.log (symmetricGaussian (1 / (4 * Real.exp s)) x z) -
      Real.log (symmetricGaussian (1 / (4 * (Real.exp s + Real.exp r))) y z) ≤
        (x - y) ^ 2 / (4 * Real.exp r) := by
  have h := Real.log_le_log (symmetricGaussian_pos _ _ _)
    (symmetricGaussian_harnack s r x y z)
  rw [Real.log_mul (Real.exp_ne_zero _) (symmetricGaussian_pos _ _ _).ne',
    Real.log_exp] at h
  linarith

end

end RiemannGaussian
