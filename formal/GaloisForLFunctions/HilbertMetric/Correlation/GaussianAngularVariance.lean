import GaloisForLFunctions.HTGeometry.GaussianSpectralPacketActionLaw
import Mathlib.Tactic

/-!
# Angular Gaussian variance

The Gaussian spectral action kernel gives the first two moments of
`cos (θ + sX)` for a standard Gaussian `X`. Its variance factors into two
nonnegative terms, with exact minimum and maximum over the viewing direction.
This is the Doppler-spread mechanism in Lemma 1 of Rivetti–Fodor–Björnson–Skoglund,
arXiv:2611.08007, including zero angular spread.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open GaloisForLFunctions.HTGeometry

namespace HilbertMetric.Correlation

private theorem integrable_angular_cos (θ s : ℝ) :
    Integrable (fun x : ℝ => Real.cos (θ + s * x)) (gaussianReal 0 1) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards with x
  exact Real.abs_cos_le_one _

private theorem integrable_angular_cos_sq (θ s : ℝ) :
    Integrable (fun x : ℝ => Real.cos (θ + s * x) ^ 2) (gaussianReal 0 1) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards with x
  simp only [Real.norm_eq_abs, abs_pow]
  nlinarith only [Real.abs_cos_le_one (θ + s * x), abs_nonneg (Real.cos (θ + s * x))]

/-- The Gaussian characteristic function gives the directional mean. -/
theorem integral_angular_cos (θ s : ℝ) :
    (∫ x : ℝ, Real.cos (θ + s * x) ∂gaussianReal 0 1) =
      Real.exp (-s ^ 2 / 2) * Real.cos θ := by
  have hi : Integrable (fun x : ℝ => Complex.exp ((θ + s * x : ℝ) * Complex.I))
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero, le_refl]
  have he : (∫ x : ℝ, Complex.exp ((θ + s * x : ℝ) * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp ((θ : ℂ) * Complex.I) * (Real.exp (-s ^ 2 / 2) : ℂ) := by
    have hf : (fun x : ℝ => Complex.exp ((θ + s * x : ℝ) * Complex.I)) =
        fun x : ℝ => Complex.exp ((θ : ℂ) * Complex.I) *
          Complex.exp (((s * x : ℝ) : ℂ) * Complex.I) := by
      funext x
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hf, integral_const_mul, integral_gaussian_observer_character]
    congr 1
    rw [gaussianObserverActionKernel, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  calc
    _ = ∫ x : ℝ, (Complex.exp ((θ + s * x : ℝ) * Complex.I)).re ∂gaussianReal 0 1 := by
      simp only [Complex.exp_ofReal_mul_I_re]
    _ = (∫ x : ℝ, Complex.exp ((θ + s * x : ℝ) * Complex.I) ∂gaussianReal 0 1).re :=
      integral_re hi
    _ = _ := by rw [he, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, mul_comm]

/-- The doubled frequency determines the second moment. -/
theorem integral_angular_cos_sq (θ s : ℝ) :
    (∫ x : ℝ, Real.cos (θ + s * x) ^ 2 ∂gaussianReal 0 1) =
      (1 + Real.exp (-(2 * s) ^ 2 / 2) * Real.cos (2 * θ)) / 2 := by
  have hf : (fun x : ℝ => Real.cos (θ + s * x) ^ 2) =
      fun x : ℝ => (1 + Real.cos (2 * θ + (2 * s) * x)) * (1 / 2) := by
    funext x
    rw [show 2 * θ + (2 * s) * x = 2 * (θ + s * x) by ring, Real.cos_two_mul]
    ring
  rw [hf, integral_mul_const, integral_add (integrable_const 1)
    (integrable_angular_cos (2 * θ) (2 * s)), integral_angular_cos]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- The variance of a Gaussian angular observation. -/
def angularGaussianVariance (θ s : ℝ) : ℝ :=
  ∫ x : ℝ, (Real.cos (θ + s * x) - Real.exp (-s ^ 2 / 2) * Real.cos θ) ^ 2
    ∂gaussianReal 0 1

/-- Exact factorization of the angular variance. -/
theorem angularGaussianVariance_eq (θ s : ℝ) :
    angularGaussianVariance θ s =
      (1 - Real.exp (-s ^ 2)) * (1 - Real.exp (-s ^ 2) * Real.cos (2 * θ)) / 2 := by
  let m := Real.exp (-s ^ 2 / 2) * Real.cos θ
  have hf : (fun x : ℝ => (Real.cos (θ + s * x) - m) ^ 2) =
      fun x : ℝ => Real.cos (θ + s * x) ^ 2 - 2 * m * Real.cos (θ + s * x) + m ^ 2 := by
    funext x
    ring
  change (∫ x : ℝ, (Real.cos (θ + s * x) - m) ^ 2 ∂gaussianReal 0 1) = _
  have hadd := integral_add ((integrable_angular_cos_sq θ s).sub
    ((integrable_angular_cos θ s).const_mul (2 * m))) (integrable_const (m ^ 2))
  simp only [Pi.sub_apply] at hadd
  rw [hf, hadd,
    integral_sub (integrable_angular_cos_sq θ s)
      ((integrable_angular_cos θ s).const_mul (2 * m)), integral_const_mul,
    integral_angular_cos_sq, integral_angular_cos]
  simp only [integral_const, probReal_univ, one_smul]
  have h1 : Real.exp (-s ^ 2 / 2) ^ 2 = Real.exp (-s ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-(2 * s) ^ 2 / 2) = Real.exp (-s ^ 2) ^ 2 := by
    rw [show Real.exp (-s ^ 2) ^ 2 =
      Real.exp (-s ^ 2) * Real.exp (-s ^ 2) from pow_two _, ← Real.exp_add]
    congr 1
    ring
  dsimp only [m]
  rw [h2, Real.cos_two_mul]
  linear_combination -(Real.cos θ) ^ 2 * h1

/-- Exact variance range over all viewing directions. -/
theorem angularGaussianVariance_bounds (θ s : ℝ) :
    (1 - Real.exp (-s ^ 2)) ^ 2 / 2 ≤ angularGaussianVariance θ s ∧
      angularGaussianVariance θ s ≤ (1 - Real.exp (-s ^ 2) ^ 2) / 2 := by
  have hA := (Real.exp_pos (-s ^ 2)).le
  have hA1 : Real.exp (-s ^ 2) ≤ 1 := by
    simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg s))
  obtain ⟨hlo, hhi⟩ := abs_le.mp (Real.abs_cos_le_one (2 * θ))
  rw [angularGaussianVariance_eq]
  constructor
  · have h := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hA1)) (sub_nonneg.mpr hhi)
    nlinarith only [h]
  · have h := mul_nonneg (mul_nonneg hA (sub_nonneg.mpr hA1))
      (show 0 ≤ 1 + Real.cos (2 * θ) by linarith only [hlo])
    nlinarith only [h]

/-- Parallel viewing attains the lower variance endpoint. -/
theorem angularGaussianVariance_parallel (s : ℝ) :
    angularGaussianVariance 0 s = (1 - Real.exp (-s ^ 2)) ^ 2 / 2 := by
  rw [angularGaussianVariance_eq]
  simp only [mul_zero, Real.cos_zero, mul_one, pow_two]

/-- Perpendicular viewing attains the upper variance endpoint. -/
theorem angularGaussianVariance_perpendicular (s : ℝ) :
    angularGaussianVariance (Real.pi / 2) s = (1 - Real.exp (-s ^ 2) ^ 2) / 2 := by
  rw [angularGaussianVariance_eq, show 2 * (Real.pi / 2) = Real.pi by ring,
    Real.cos_pi]
  ring

/-- Positive angular spread always yields positive variance in every direction. -/
theorem angularGaussianVariance_eq_zero_iff (θ s : ℝ) :
    angularGaussianVariance θ s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hb := (angularGaussianVariance_bounds θ s).1
    rw [h] at hb
    have hA : Real.exp (-s ^ 2) = 1 := by
      nlinarith only [hb, sq_nonneg (1 - Real.exp (-s ^ 2))]
    have hs := Real.exp_injective (hA.trans Real.exp_zero.symm)
    nlinarith only [hs, sq_nonneg s]
  · rintro rfl
    simp only [angularGaussianVariance_eq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, neg_zero, Real.exp_zero, sub_self, zero_mul, zero_div]

end HilbertMetric.Correlation

#print axioms HilbertMetric.Correlation.integral_angular_cos
#print axioms HilbertMetric.Correlation.integral_angular_cos_sq
#print axioms HilbertMetric.Correlation.angularGaussianVariance_eq
#print axioms HilbertMetric.Correlation.angularGaussianVariance_bounds
#print axioms HilbertMetric.Correlation.angularGaussianVariance_parallel
#print axioms HilbertMetric.Correlation.angularGaussianVariance_perpendicular
#print axioms HilbertMetric.Correlation.angularGaussianVariance_eq_zero_iff
