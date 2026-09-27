import GaloisForLFunctions.RHTower.XiGaussianRootOrientationBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Keeping polynomial and Gaussian phase together under differentiation

The vertical mean-value estimate acts on the entire Gaussian amplitude.
Its derivative is formed before coefficient norms are taken, retaining the
signed cancellation between adjacent coefficients.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiGaussianDerivativePolynomial (Q : Polynomial ℝ) (t : ℝ) : Polynomial ℝ :=
  Q.derivative - Polynomial.C (t / 2) * Q

theorem xiGaussianDerivativePolynomial_coeff (Q : Polynomial ℝ) (t : ℝ) (j : ℕ) :
    (xiGaussianDerivativePolynomial Q t).coeff j =
      (j + 1 : ℝ) * Q.coeff (j + 1) - t / 2 * Q.coeff j := by
  simp only [xiGaussianDerivativePolynomial, Polynomial.coeff_sub,
    Polynomial.coeff_derivative, Polynomial.coeff_C_mul]
  ring

theorem hasDerivAt_xiGaussianPolynomialAmplitude (Q : Polynomial ℝ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => heatPhaseAmplitude (evalRealPolynomial Q w) t w)
      (heatPhaseAmplitude (evalRealPolynomial (xiGaussianDerivativePolynomial Q t) z) t z) z := by
  have hp : HasDerivAt (fun w => evalRealPolynomial Q w)
      (evalRealPolynomial Q.derivative z) z := by
    simpa only [evalRealPolynomial, Polynomial.derivative_map] using
      (Q.map (algebraMap ℝ ℂ)).hasDerivAt z
  have he := ((hasDerivAt_id z).const_mul (-((t / 2 : ℝ) : ℂ))).cexp
  apply (hp.mul he).congr_deriv
  simp only [heatPhaseAmplitude, xiGaussianDerivativePolynomial, evalRealPolynomial,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, coe_algebraMap, id_eq]
  ring

theorem xiGaussianVerticalSegment_geometry (z : ℂ)
    (w : {w : ℂ // w ∈ segment ℝ (z.re : ℂ) z}) :
    (w : ℂ).re = z.re ∧ ‖(w : ℂ)‖ ≤ ‖z‖ := by
  obtain ⟨a, b, ha, hb, hab, hw⟩ := w.property
  rw [← hw]
  constructor
  · simp only [Complex.add_re, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · calc
      _ ≤ ‖a • (z.re : ℂ)‖ + ‖b • z‖ := norm_add_le _ _
      _ = a * |z.re| + b * ‖z‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ a * ‖z‖ + b * ‖z‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z) ha) le_rfl
      _ = ‖z‖ := by rw [← add_mul, hab, one_mul]

/-- The complete amplitude is bounded using the signed Gaussian derivative polynomial. -/
theorem abs_xiGaussianPolynomialAmplitude_im_le_derivative
    (Q : Polynomial ℝ) (t : ℝ) (z : ℂ) :
    |(heatPhaseAmplitude (evalRealPolynomial Q z) t z).im| ≤
      |z.im| * Real.exp (-(t / 2 * z.re)) *
        evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t) ‖z‖ := by
  let D := xiGaussianDerivativePolynomial Q t
  let f : ℂ → ℂ := fun w => heatPhaseAmplitude (evalRealPolynomial Q w) t w
  let f' : ℂ → ℂ := fun w => heatPhaseAmplitude (evalRealPolynomial D w) t w
  let E := Real.exp (-(t / 2 * z.re))
  let B := evalRealPolynomialNormBound D ‖z‖
  have hb (w : ℂ) (hw : w ∈ segment ℝ (z.re : ℂ) z) : ‖f' w‖ ≤ E * B := by
    obtain ⟨hre, hn⟩ := xiGaussianVerticalSegment_geometry z ⟨w, hw⟩
    change w.re = z.re at hre
    have hp := norm_evalRealPolynomial_le D hn
    change ‖heatPhaseAmplitude (evalRealPolynomial D w) t w‖ ≤ _
    rw [heatPhaseAmplitude, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hre, neg_mul]
    exact (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans_eq (mul_comm B E)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w (_ : w ∈ segment ℝ (z.re : ℂ) z) =>
      (hasDerivAt_xiGaussianPolynomialAmplitude Q t w).hasDerivWithinAt)
    hb (convex_segment _ _) (left_mem_segment ℝ (z.re : ℂ) z)
      (right_mem_segment ℝ (z.re : ℂ) z)
  have hreal : (f (z.re : ℂ)).im = 0 := by
    dsimp only [f]
    rw [heatPhaseAmplitude_im, evalRealPolynomial_ofReal]
    simp
  have him := Complex.abs_im_le_norm (f z - f (z.re : ℂ))
  rw [Complex.sub_im, hreal, sub_zero] at him
  have hn : ‖z - (z.re : ℂ)‖ = |z.im| := by
    rw [show z - (z.re : ℂ) = (z.im : ℂ) * Complex.I by apply Complex.ext <;> simp,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hm
  exact (him.trans hm).trans_eq (by dsimp only [E, B]; ring)

/-- Squaring the signed derivative estimate keeps the transverse zero exactly. -/
theorem xiGaussianPolynomialAmplitude_im_sq_le_derivative
    (Q : Polynomial ℝ) (t : ℝ) (z : ℂ) :
    (heatPhaseAmplitude (evalRealPolynomial Q z) t z).im ^ 2 ≤
      z.im ^ 2 * Real.exp (-(t * z.re)) *
        evalRealPolynomialNormBound (xiGaussianDerivativePolynomial Q t) ‖z‖ ^ 2 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
      (evalRealPolynomialNormBound_nonneg _ (norm_nonneg _)))).mpr
        (abs_xiGaussianPolynomialAmplitude_im_le_derivative Q t z)
  have he : Real.exp (-(t / 2 * z.re)) ^ 2 = Real.exp (-(t * z.re)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, sq_abs, he] using h

end RHTower
