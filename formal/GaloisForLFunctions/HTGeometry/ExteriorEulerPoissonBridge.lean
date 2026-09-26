import GaloisForLFunctions.HTGeometry.ExteriorEulerVelocity
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGroupDelay

/-!
# Euler factor velocity, reciprocal Poisson mass, and all-pass delay

An exterior linear factor and an interior Blaschke factor at the reciprocal
radius carry the same phase information, up to a half-unit baseline.  The
identities below connect the real velocity formula to the actual complex
logarithmic derivatives and the existing disk Poisson kernel.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

theorem normSq_exteriorEuler_factor (x θ : ℝ) :
    Complex.normSq (1 - (exteriorEulerRadius x : ℂ) * Complex.exp (θ * I)) =
      exteriorEulerDenom x θ := by
  simp only [Complex.normSq_apply, sub_re, one_re, mul_re, ofReal_re, exp_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, mul_one,
    Real.exp_zero, one_mul, sub_im, one_im, mul_im, exp_im, add_zero]
  unfold exteriorEulerDenom
  nlinarith [Real.cos_sq_add_sin_sq θ]

theorem exteriorEuler_factor_ne_zero (x θ : ℝ) :
    1 - (exteriorEulerRadius x : ℂ) * Complex.exp (θ * I) ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [normSq_exteriorEuler_factor]
  exact exteriorEulerDenom_pos x θ

/-- The complex resolvent has exactly the real radial speed used in the
phase-independent inequalities. -/
theorem re_exteriorEuler_resolvent (x θ : ℝ) :
    (((exteriorEulerRadius x : ℂ) * Complex.exp (θ * I)) /
      (1 - (exteriorEulerRadius x : ℂ) * Complex.exp (θ * I))).re =
      -exteriorEulerSpeed x θ := by
  rw [Complex.div_re, normSq_exteriorEuler_factor]
  simp only [sub_re, one_re, mul_re, ofReal_re, exp_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, mul_one, Real.exp_zero, one_mul,
    sub_im, one_im, mul_im, exp_im, add_zero]
  unfold exteriorEulerSpeed
  field_simp [(exteriorEulerDenom_pos x θ).ne']
  nlinarith [congrArg (fun u : ℝ => exteriorEulerRadius x ^ 2 * u)
    (Real.cos_sq_add_sin_sq θ)]

/-- The reciprocal radius is a genuine disk parameter for every real input. -/
theorem norm_inv_exteriorEulerRadius_lt_one (x : ℝ) :
    ‖((exteriorEulerRadius x)⁻¹ : ℂ)‖ < 1 := by
  have hr := exteriorEulerRadius_gt_one x
  rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (show 0 < exteriorEulerRadius x by linarith))]
  exact (inv_lt_one₀ (by linarith)).mpr hr

/-- The paper's surplus over a half-unit is literally disk Poisson mass at
the reciprocal point. -/
theorem poissonKernel_inv_exteriorEulerRadius (x θ : ℝ) :
    poissonKernel 0 ((exteriorEulerRadius x)⁻¹ : ℂ) (Complex.exp (θ * I)) =
      exteriorEulerPoisson x θ := by
  rw [poissonKernel_zero_eq_normSq_ratio (Complex.norm_exp_ofReal_mul_I θ)]
  have hr := exteriorEulerRadius_gt_one x
  have hden : Complex.normSq (Complex.exp (θ * I) -
      ((exteriorEulerRadius x)⁻¹ : ℂ)) =
      exteriorEulerDenom x θ / exteriorEulerRadius x ^ 2 := by
    rw [← Complex.ofReal_inv]
    simp only [Complex.normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im,
      exp_re, exp_im, mul_re, mul_im, I_re, I_im, mul_zero,
      sub_zero, mul_one, Real.exp_zero, one_mul, add_zero]
    unfold exteriorEulerDenom
    field_simp [show exteriorEulerRadius x ≠ 0 by linarith]
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [hden, ← Complex.ofReal_inv]
  simp only [Complex.normSq_ofReal]
  unfold exteriorEulerPoisson
  field_simp [(exteriorEulerDenom_pos x θ).ne',
    show exteriorEulerRadius x ≠ 0 by linarith]

/-- Exact conversion between the exterior Euler speed and the interior
all-pass group delay already present in the corpus. -/
theorem exteriorEulerSpeed_eq_half_add_blaschke_delay (x θ : ℝ) :
    exteriorEulerSpeed x θ =
      (1 + (Complex.exp (θ * I) * logDeriv
        (fun z : ℂ => (z - ((exteriorEulerRadius x)⁻¹ : ℂ)) /
          (1 - star ((exteriorEulerRadius x)⁻¹ : ℂ) * z))
        (Complex.exp (θ * I))).re) / 2 := by
  rw [mul_logDeriv_blaschkeFactor_eq_poissonKernel
    (norm_inv_exteriorEulerRadius_lt_one x) (Complex.norm_exp_ofReal_mul_I θ)]
  simp only [ofReal_re, poissonKernel_inv_exteriorEulerRadius]
  exact exteriorEulerSpeed_eq_half_add_poisson x θ

/-- An actual exterior linear Euler factor has strictly positive angular
logarithmic speed, uniformly above one half. -/
theorem re_mul_logDeriv_exteriorEulerFactor (x θ : ℝ) :
    (Complex.exp (θ * I) * logDeriv
      (fun z : ℂ => 1 - (exteriorEulerRadius x : ℂ) * z)
      (Complex.exp (θ * I))).re = exteriorEulerSpeed x θ := by
  have hd : HasDerivAt (fun z : ℂ => 1 - (exteriorEulerRadius x : ℂ) * z)
      (-(exteriorEulerRadius x : ℂ)) (Complex.exp (θ * I)) := by
    simpa using! (hasDerivAt_const (Complex.exp (θ * I)) (1 : ℂ)).sub
      ((hasDerivAt_id (Complex.exp (θ * I))).const_mul (exteriorEulerRadius x : ℂ))
  rw [logDeriv_apply, hd.deriv]
  have halg : Complex.exp (θ * I) *
      (-(exteriorEulerRadius x : ℂ) /
        (1 - (exteriorEulerRadius x : ℂ) * Complex.exp (θ * I))) =
      -((exteriorEulerRadius x : ℂ) * Complex.exp (θ * I) /
        (1 - (exteriorEulerRadius x : ℂ) * Complex.exp (θ * I))) := by ring
  rw [halg, neg_re, re_exteriorEuler_resolvent, neg_neg]

end

end GaloisForLFunctions.HTGeometry
