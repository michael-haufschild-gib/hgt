import GaloisForLFunctions.RHTower.FiniteExponentialSumMellin
import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel
import GaloisForLFunctions.HTGeometry.LogarithmicGaussianMellin
import GaloisForLFunctions.RHTower.MobiusAbelPrefixFourierMultiplier

/-!
# Mellin transforms of regularization filters

The squared resolvent filter has a beta Mellin kernel on its full convergence strip.
The inverse-power exponential filter has a gamma kernel. Exponential parameters cover
all positive powers; the central beta value removes an apparent singularity.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.CubicGamma
namespace GaloisForLFunctions.BiScaleUncertainty.Spectral
noncomputable section

def squaredResolventFilter (t u : ℝ) : ℂ := (1 + (u ^ (-Real.exp t) : ℝ) : ℂ) ^ (-(2 : ℂ))
def gradientFlowFilter (t u : ℝ) : ℂ := Real.exp (-(2 * u ^ (-Real.exp t)))
def filterStripShape (r v : ℝ) : ℂ := (2 / (1 + Real.exp r) : ℝ) + I * v

private theorem filterStripShape_re (r v : ℝ) : (filterStripShape r v).re = 2 / (1 + Real.exp r) := by
  simp only [filterStripShape, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem filterStripShape_bounds (r v : ℝ) :
    0 < (filterStripShape r v).re ∧ (filterStripShape r v).re < 2 := by
  rw [filterStripShape_re]
  have hd : 0 < 1 + Real.exp r := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hd).mpr
    nlinarith only [Real.exp_pos r]


/-- The parametrization covers exactly the entire beta convergence strip. -/
theorem filterStripShape_range (z : ℂ) :
    (∃ r v : ℝ, filterStripShape r v = z) ↔ 0 < z.re ∧ z.re < 2 := by
  constructor
  · rintro ⟨r, v, rfl⟩; exact filterStripShape_bounds r v
  · rintro ⟨h0, h2⟩
    have hp : 0 < 2 / z.re - 1 := by
      apply sub_pos.mpr
      exact (lt_div_iff₀ h0).mpr (by simpa using h2)
    refine ⟨Real.log (2 / z.re - 1), z.im, ?_⟩
    apply Complex.ext
    · rw [filterStripShape_re, Real.exp_log hp]
      field_simp
      ring
    · simp only [filterStripShape, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]

private theorem mellinConvergent_base {z : ℂ} (hz : 0 < z.re) (h2 : z.re < 2) :
    MellinConvergent (fun u : ℝ => (1 + (u : ℂ)) ^ (-(2 : ℂ))) z := by
  rw [mellinConvergent_iff_integrable_exp_two]
  have hbeta := integrable_exp_mul_one_add_exp_cpow (u := z) (v := 2 - z) hz (by
    rw [Complex.sub_re]; norm_num; linarith only [h2])
  have hscale := (integrable_comp_mul_left_iff
    (fun u : ℝ => Complex.exp (z * (u : ℂ)) *
      ((1 + Real.exp u : ℝ) : ℂ) ^ (-(z + (2 - z)))) (by norm_num : (2 : ℝ) ≠ 0)).mpr hbeta
  convert hscale using 1
  ext u
  push_cast
  ring_nf

private theorem mellin_base {z : ℂ} (hz : 0 < z.re) (h2 : z.re < 2) :
    mellin (fun u : ℝ => (1 + (u : ℂ)) ^ (-(2 : ℂ))) z =
      Complex.Gamma z * Complex.Gamma (2 - z) := by
  rw [mellin]
  simp only [smul_eq_mul]
  rw [integral_halfLine_beta hz (by norm_num; exact h2)]
  norm_num [Complex.Gamma_nat_eq_factorial]

theorem squaredResolventFilter_convergent (t r v : ℝ) :
    MellinConvergent (squaredResolventFilter t) (-(Real.exp t : ℂ) * filterStripShape r v) := by
  have he : (-(Real.exp t : ℂ) * filterStripShape r v) / (-Real.exp t : ℝ) =
      filterStripShape r v := by
    push_cast
    field_simp
  change MellinConvergent (fun u : ℝ => (fun x : ℝ => (1 + (x : ℂ)) ^ (-(2 : ℂ)))
    (u ^ (-Real.exp t))) _
  rw [MellinConvergent.comp_rpow (f := (fun x : ℝ => (1 + (x : ℂ)) ^ (-(2 : ℂ)))) (neg_ne_zero.mpr (Real.exp_ne_zero t)), he]
  exact mellinConvergent_base (filterStripShape_bounds r v).1 (filterStripShape_bounds r v).2

theorem squaredResolventFilter_mellin (t r v : ℝ) :
    mellin (squaredResolventFilter t) (-(Real.exp t : ℂ) * filterStripShape r v) =
      (Real.exp t : ℂ)⁻¹ * (Complex.Gamma (filterStripShape r v) *
        Complex.Gamma (2 - filterStripShape r v)) := by
  have he : (-(Real.exp t : ℂ) * filterStripShape r v) / (-Real.exp t : ℝ) =
      filterStripShape r v := by
    push_cast
    field_simp
  change mellin (fun u : ℝ => (fun x : ℝ => (1 + (x : ℂ)) ^ (-(2 : ℂ)))
    (u ^ (-Real.exp t))) _ = _
  rw [mellin_comp_rpow (fun x : ℝ => (1 + (x : ℂ)) ^ (-(2 : ℂ))) _ (-Real.exp t), he, mellin_base (filterStripShape_bounds r v).1 (filterStripShape_bounds r v).2]
  simp only [abs_neg, abs_of_pos (Real.exp_pos t), Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

theorem squaredResolventFilter_cancellation (t : ℝ) :
    mellin (squaredResolventFilter t) (-(Real.exp t : ℂ)) = (Real.exp t : ℂ)⁻¹ := by
  have h := squaredResolventFilter_mellin t 0 0
  have hz : filterStripShape 0 0 = 1 := by norm_num [filterStripShape]
  simpa only [hz, mul_one, show (2 : ℂ) - 1 = 1 by norm_num, Complex.Gamma_one,
    one_mul] using h

theorem gradientFlowFilter_convergent (t r v : ℝ) :
    MellinConvergent (gradientFlowFilter t)
      (-(Real.exp t : ℂ) * ((Real.exp r : ℂ) + I * v)) := by
  have he : (-(Real.exp t : ℂ) * ((Real.exp r : ℂ) + I * v)) / (-Real.exp t : ℝ) =
      (Real.exp r : ℂ) + I * v := by
    push_cast
    field_simp
  change MellinConvergent (fun u : ℝ => (fun x : ℝ => (Real.exp (-(2 * x)) : ℂ))
    (u ^ (-Real.exp t))) _
  rw [MellinConvergent.comp_rpow (f := (fun x : ℝ => (Real.exp (-(2 * x)) : ℂ))) (neg_ne_zero.mpr (Real.exp_ne_zero t)), he]
  apply mellinConvergent_exp_neg_mul (by norm_num)
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using Real.exp_pos r

theorem gradientFlowFilter_mellin (t r v : ℝ) :
    mellin (gradientFlowFilter t) (-(Real.exp t : ℂ) * ((Real.exp r : ℂ) + I * v)) =
      (Real.exp t : ℂ)⁻¹ *
        ((2 : ℂ) ^ (-((Real.exp r : ℂ) + I * v)) *
          Complex.Gamma ((Real.exp r : ℂ) + I * v)) := by
  have he : (-(Real.exp t : ℂ) * ((Real.exp r : ℂ) + I * v)) / (-Real.exp t : ℝ) =
      (Real.exp r : ℂ) + I * v := by
    push_cast
    field_simp
  change mellin (fun u : ℝ => (fun x : ℝ => (Real.exp (-(2 * x)) : ℂ))
    (u ^ (-Real.exp t))) _ = _
  rw [mellin_comp_rpow (fun x : ℝ => (Real.exp (-(2 * x)) : ℂ)) _ (-Real.exp t), he,
    mellin_exp_neg_mul_finiteExponentialSumMellin (by norm_num) (by simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using Real.exp_pos r)]
  simp only [abs_neg, abs_of_pos (Real.exp_pos t), Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

#print axioms filterStripShape_range
#print axioms squaredResolventFilter_convergent
#print axioms squaredResolventFilter_mellin
#print axioms squaredResolventFilter_cancellation
#print axioms gradientFlowFilter_convergent
#print axioms gradientFlowFilter_mellin

end
end GaloisForLFunctions.BiScaleUncertainty.Spectral
