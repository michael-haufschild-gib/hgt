import GaloisForLFunctions.RHTower.TiltedHeatSaddleGaussian
import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments

/-! The corpus Gaussian Fourier moment yields the normalized probability fourth moment. -/

open MeasureTheory ProbabilityTheory

namespace RHTower

theorem gaussMoment_zero_eq_ofReal_integral (a : ℝ) (n : ℕ) :
    gaussMoment a n 0 = ↑(∫ x : ℝ, x ^ n * Real.exp (-a * x ^ 2)) := by
  rw [gaussMoment, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  simp only [gaussPhase, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_neg]

theorem gaussianZero_integral_fourth (v : NNReal) :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v)) = 3 * (v : ℝ) ^ 2 := by
  by_cases hv : v = 0
  · subst v
    simp [gaussianReal_zero_var]
  have hvpos : (0 : ℝ) < v := by
    exact_mod_cast (pos_iff_ne_zero.mpr hv : 0 < v)
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvpos
  let a : ℝ := 1 / (2 * (v : ℝ))
  let C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hpdf (x : ℝ) : gaussianPDFReal 0 v x = C * Real.exp (-a * x ^ 2) := by
    dsimp [C, a]
    rw [gaussianPDFReal, sub_zero]
    congr 2
    ring
  have hnorm : C * (∫ x : ℝ, Real.exp (-a * x ^ 2)) = 1 := by
    have h := integral_gaussianPDFReal_eq_one 0 hv
    simp_rw [hpdf] at h
    rw [integral_const_mul] at h
    exact h
  have hfour := congrArg Complex.re (gaussMoment_four_eq ha)
  simp only [gaussMoment_zero_eq_ofReal_integral, ← Complex.ofReal_mul,
    Complex.ofReal_re, pow_zero, one_mul] at hfour
  have hcoef : 3 / (4 * a ^ 2) = 3 * (v : ℝ) ^ 2 := by
    dsimp [a]
    field_simp [hvne]
    ring
  have hf (x : ℝ) : gaussianPDFReal 0 v x * x ^ 4 =
      C * (x ^ 4 * Real.exp (-a * x ^ 2)) := by
    rw [hpdf]
    ring
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul, hf]
  rw [integral_const_mul, hfour, hcoef]
  calc
    C * (3 * (v : ℝ) ^ 2 * (∫ x : ℝ, Real.exp (-a * x ^ 2))) =
        3 * (v : ℝ) ^ 2 * (C * (∫ x : ℝ, Real.exp (-a * x ^ 2))) := by ring
    _ = 3 * (v : ℝ) ^ 2 := by rw [hnorm, mul_one]

end RHTower
