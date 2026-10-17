import GaloisForLFunctions.RHTower.ThetaRenewalCausalKernel
import Mathlib.MeasureTheory.Function.LpOrder

/-! # Every complex exponential tilt of the theta half-density belongs to L² -/

noncomputable section
open MeasureTheory Set Complex
open scoped ComplexOrder

namespace RHTower

local notation "μ₊" => Measure.restrict (volume : Measure ℝ) (Ioi 0)

def thetaRenewalModeFn (z : ℂ) (t : ℝ) : ℂ :=
  (thetaRenewalHalfDensity t : ℂ) * Complex.exp (-(z * (t : ℂ)))

theorem continuous_thetaRenewalModeFn (z : ℂ) : Continuous (thetaRenewalModeFn z) := by
  unfold thetaRenewalModeFn
  exact (Complex.continuous_ofReal.comp continuous_thetaRenewalHalfDensity).mul
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg))

theorem thetaRenewalModeFn_norm_sq (z : ℂ) (t : ℝ) :
    ‖thetaRenewalModeFn z t‖ ^ 2 =
      Real.exp (-((2 * z.re) * t)) * thetaRenewalIncrement t := by
  have he : ‖Complex.exp (-(z * (t : ℂ)))‖ ^ 2 = Real.exp (-((2 * z.re) * t)) := by
    rw [Complex.norm_exp, pow_two, ← Real.exp_add]
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    ring
  rw [thetaRenewalModeFn, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalHalfDensity_pos t), thetaRenewalHalfDensity_sq, he, mul_comm]

theorem memLp_thetaRenewalModeFn (z : ℂ) : MemLp (thetaRenewalModeFn z) 2 μ₊ := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_thetaRenewalModeFn z).aestronglyMeasurable).mpr ?_
  simp_rw [thetaRenewalModeFn_norm_sq]
  exact integrableOn_exp_mul_thetaRenewalIncrement (2 * z.re)

def thetaRenewalMode (z : ℂ) : ThetaRenewalL2 :=
  (memLp_thetaRenewalModeFn z).toLp (thetaRenewalModeFn z)

theorem thetaRenewalMode_ae (z : ℂ) :
    (thetaRenewalMode z : ℝ → ℂ) =ᵐ[μ₊] thetaRenewalModeFn z :=
  (memLp_thetaRenewalModeFn z).coeFn_toLp

theorem thetaRenewalModeFn_zero (t : ℝ) :
    thetaRenewalModeFn 0 t = (thetaRenewalHalfDensity t : ℂ) := by
  simp [thetaRenewalModeFn]

theorem thetaRenewalMode_zero_nonneg : 0 ≤ thetaRenewalMode 0 := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [thetaRenewalMode_ae 0] with t ht
  rw [ht, thetaRenewalModeFn_zero]
  exact Complex.zero_le_real.mpr (thetaRenewalHalfDensity_pos t).le

/-- The scalar renewal Laplace transform is a matrix coefficient of the actual L² modes. -/
theorem inner_thetaRenewalMode_zero (z : ℂ) :
    inner ℂ (thetaRenewalMode 0) (thetaRenewalMode z) = thetaRenewalLaplace z := by
  rw [L2.inner_def, thetaRenewalLaplace]
  apply integral_congr_ae
  filter_upwards [thetaRenewalMode_ae 0, thetaRenewalMode_ae z] with t h0 hz
  rw [h0, hz, thetaRenewalModeFn_zero, RCLike.inner_apply, thetaRenewalModeFn]
  simp only [Complex.conj_ofReal]
  calc (thetaRenewalHalfDensity t : ℂ) * Complex.exp (-(z * (t : ℂ))) *
        (thetaRenewalHalfDensity t : ℂ) =
      Complex.exp (-(z * (t : ℂ))) * (thetaRenewalHalfDensity t : ℂ) ^ 2 := by ring
    _ = _ := by rw [← Complex.ofReal_pow, thetaRenewalHalfDensity_sq]

end RHTower
