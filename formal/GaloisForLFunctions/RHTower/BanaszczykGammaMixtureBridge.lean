import GaloisForLFunctions.HTGeometry.BanaszczykRationalDensity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gamma-mixture bridge to vector balancing

Lemma 2.4 of Guo--Fang--Lu represents its rational tangent variable as a
standard Gaussian divided by the square root of an independent chi-square
variable with three degrees of freedom.  The corpus already contains the exact
Gamma-leg integral needed for this representation in
`GammaMixtureConcentration`.

This module proves the paper's displayed scalar mixture identity directly and
identifies it with `banaszczykRationalDensity`.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- Simplified product of the conditional Gaussian density and the
chi-square-three mixing density. -/
def banaszczykGaussianChiSquareKernel (t s : ℝ) : ℝ :=
  s / (2 * Real.pi) * Real.exp (-(((1 + t ^ 2) / 2) * s))

private theorem integral_gamma_leg_one {a : ℝ} (ha : 0 < a) :
    ∫ s in Ioi (0 : ℝ), s * Real.exp (-(a * s)) = 1 / a ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := a) (by norm_num) ha
  have hGamma : Real.Gamma (2 : ℝ) = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 using 1 <;> norm_num
  rw [hGamma, mul_one] at h
  calc
    (∫ s in Ioi (0 : ℝ), s * Real.exp (-(a * s))) = a⁻¹ ^ 2 := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
        one_div] using h
    _ = 1 / a ^ 2 := by rw [one_div, inv_pow]

/-- The paper's displayed Gamma mixture integrates to its rational density. -/
@[simp]
theorem integral_banaszczykGaussianChiSquareKernel (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), banaszczykGaussianChiSquareKernel t s =
      GaloisForLFunctions.HTGeometry.banaszczykRationalDensity t := by
  have ha : 0 < (1 + t ^ 2) / 2 := by positivity
  have hgamma := integral_gamma_leg_one ha
  have hfun : banaszczykGaussianChiSquareKernel t = fun s : ℝ =>
      (1 / (2 * Real.pi)) *
        (s ^ 1 * Real.exp (-(((1 + t ^ 2) / 2) * s))) := by
    funext s
    unfold banaszczykGaussianChiSquareKernel
    ring
  rw [hfun, integral_const_mul]
  simp only [pow_one]
  rw [hgamma]
  unfold GaloisForLFunctions.HTGeometry.banaszczykRationalDensity
  norm_num
  field_simp [Real.pi_ne_zero, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity]

/-- Gaussian density at `t` conditional on precision `s`. -/
def banaszczykConditionalGaussianKernel (t s : ℝ) : ℝ :=
  Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s * t ^ 2 / 2))

/-- Chi-square-three density, written in the normalization used by the paper. -/
def chiSquareThreeDensity (s : ℝ) : ℝ :=
  Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s / 2))

theorem chiSquareThreeDensity_nonneg (s : ℝ) : 0 ≤ chiSquareThreeDensity s := by
  unfold chiSquareThreeDensity
  positivity

theorem continuous_chiSquareThreeDensity : Continuous chiSquareThreeDensity := by
  unfold chiSquareThreeDensity
  fun_prop

@[simp]
theorem chiSquareThreeDensity_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    chiSquareThreeDensity s = 0 := by
  unfold chiSquareThreeDensity
  rw [Real.sqrt_eq_zero_of_nonpos]
  · simp
  · exact div_nonpos_of_nonpos_of_nonneg hs (by positivity)

private theorem integrableOn_rpow_mul_exp_neg_half (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s ^ (a - 1) * Real.exp (-((1 / 2) * s))) (Ioi 0) := by
  have hGamma : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent ha
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (a - 1)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by simpa using hGamma)
  have hc : (1 / 2 : ℝ) ^ (a - 1) ≠ 0 := by positivity
  have hmul := hscale.const_mul ((1 / 2 : ℝ) ^ (a - 1))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun hmul ?_ measurableSet_Ioi
  intro s hs
  have hs0 : 0 < s := hs
  change ((1 / 2 : ℝ) ^ (a - 1))⁻¹ *
      (Real.exp (-((1 / 2) * s)) * ((1 / 2) * s) ^ (a - 1)) =
    s ^ (a - 1) * Real.exp (-((1 / 2) * s))
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hs0.le]
  field_simp

theorem integrableOn_chiSquareThreeDensity :
    IntegrableOn chiSquareThreeDensity (Ioi (0 : ℝ)) := by
  have h := (integrableOn_rpow_mul_exp_neg_half (3 / 2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro s hs
  unfold chiSquareThreeDensity
  change (Real.sqrt (2 * Real.pi))⁻¹ *
      (s ^ (3 / 2 - 1 : ℝ) * Real.exp (-((1 / 2) * s))) =
    Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s / 2))
  rw [Real.sqrt_div hs.le]
  simp only [Real.sqrt_eq_rpow]
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num]
  rw [show -(s / 2) = -((1 / 2) * s) by ring]
  ring

theorem integrableOn_inv_mul_chiSquareThreeDensity :
    IntegrableOn (fun s : ℝ => s⁻¹ * chiSquareThreeDensity s) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_rpow_mul_exp_neg_half (1 / 2) (by norm_num)).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro s hs
  unfold chiSquareThreeDensity
  change (Real.sqrt (2 * Real.pi))⁻¹ *
      (s ^ (1 / 2 - 1 : ℝ) * Real.exp (-((1 / 2) * s))) =
    s⁻¹ * (Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s / 2)))
  rw [Real.sqrt_div hs.le]
  simp only [Real.sqrt_eq_rpow]
  rw [show s⁻¹ = s ^ (-1 : ℝ) by exact (Real.rpow_neg_one s).symm]
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
  rw [show -(s / 2) = -((1 / 2) * s) by ring]
  calc
    ((2 * Real.pi) ^ (1 / 2 : ℝ))⁻¹ *
          (s ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s))) =
        ((2 * Real.pi) ^ (1 / 2 : ℝ))⁻¹ *
          ((s ^ (-1 : ℝ) * s ^ (1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s))) := by
      rw [← Real.rpow_add hs]
      norm_num
    _ = s ^ (-1 : ℝ) *
          (s ^ (1 / 2 : ℝ) / (2 * Real.pi) ^ (1 / 2 : ℝ) *
            Real.exp (-((1 / 2) * s))) := by ring

private theorem gamma_three_halves :
    Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  ring

/-- The chi-square-three mixing density has total mass one. -/
@[simp]
theorem integral_chiSquareThreeDensity :
    ∫ s in Ioi (0 : ℝ), chiSquareThreeDensity s = 1 := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hgamma' :
      (∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-((1 / 2) * s))) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * Real.Gamma (3 / 2) := by
    simpa only [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num,
      show (1 / (1 / 2 : ℝ)) = 2 by norm_num] using hgamma
  have hfun : (∫ s in Ioi (0 : ℝ), chiSquareThreeDensity s) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ s in Ioi (0 : ℝ), s ^ (1 / 2 : ℝ) * Real.exp (-((1 / 2) * s)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs => by
      unfold chiSquareThreeDensity
      rw [Real.sqrt_div hs.le, Real.sqrt_eq_rpow]
      rw [show -(s / 2) = -((1 / 2) * s) by ring]
      ring
  rw [hfun, hgamma', gamma_three_halves]
  norm_num
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [h2, hpi]

/-- Exact inverse moment used by the paper's Jensen step: `E S⁻¹ = 1`. -/
@[simp]
theorem integral_inv_mul_chiSquareThreeDensity :
    ∫ s in Ioi (0 : ℝ), s⁻¹ * chiSquareThreeDensity s = 1 := by
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hgamma' :
      (∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s))) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
    simpa only [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num,
      show (1 / (1 / 2 : ℝ)) = 2 by norm_num] using hgamma
  have hfun : (∫ s in Ioi (0 : ℝ), s⁻¹ * chiSquareThreeDensity s) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ s in Ioi (0 : ℝ), s ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs => by
      unfold chiSquareThreeDensity
      rw [Real.sqrt_div hs.le, Real.sqrt_eq_rpow]
      rw [show s⁻¹ = s ^ (-1 : ℝ) by exact (Real.rpow_neg_one s).symm]
      rw [show -(s / 2) = -((1 / 2) * s) by ring]
      calc
        s ^ (-1 : ℝ) *
              (s ^ (1 / 2 : ℝ) / Real.sqrt (2 * Real.pi) *
                Real.exp (-((1 / 2) * s))) =
            (Real.sqrt (2 * Real.pi))⁻¹ *
              ((s ^ (-1 : ℝ) * s ^ (1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s))) := by
          ring
        _ = (Real.sqrt (2 * Real.pi))⁻¹ *
              (s ^ (-(1 / 2 : ℝ)) * Real.exp (-((1 / 2) * s))) := by
          rw [← Real.rpow_add hs]
          norm_num
  rw [hfun, hgamma', Real.Gamma_one_half_eq]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hpi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [h2, hpi]

/-- Pointwise factorization of the simplified mixture kernel on the positive
mixing ray. -/
theorem conditionalGaussian_mul_chiSquareThree {t s : ℝ} (hs : 0 ≤ s) :
    banaszczykConditionalGaussianKernel t s * chiSquareThreeDensity s =
      banaszczykGaussianChiSquareKernel t s := by
  unfold banaszczykConditionalGaussianKernel chiSquareThreeDensity
    banaszczykGaussianChiSquareKernel
  have hq : 0 ≤ s / (2 * Real.pi) := by positivity
  calc
    Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s * t ^ 2 / 2)) *
          (Real.sqrt (s / (2 * Real.pi)) * Real.exp (-(s / 2))) =
        (Real.sqrt (s / (2 * Real.pi)) * Real.sqrt (s / (2 * Real.pi))) *
          (Real.exp (-(s * t ^ 2 / 2)) * Real.exp (-(s / 2))) := by ring
    _ = (s / (2 * Real.pi)) *
          Real.exp (-(s * t ^ 2 / 2) + -(s / 2)) := by
      rw [Real.mul_self_sqrt hq, ← Real.exp_add]
    _ = s / (2 * Real.pi) * Real.exp (-(((1 + t ^ 2) / 2) * s)) := by
      congr 2
      ring

/-- Unsimplified Gaussian-times-chi-square form of the same mixture identity. -/
@[simp]
theorem integral_conditionalGaussian_mul_chiSquareThree (t : ℝ) :
    ∫ s in Ioi (0 : ℝ),
        banaszczykConditionalGaussianKernel t s * chiSquareThreeDensity s =
      GaloisForLFunctions.HTGeometry.banaszczykRationalDensity t := by
  calc
    (∫ s in Ioi (0 : ℝ),
        banaszczykConditionalGaussianKernel t s * chiSquareThreeDensity s) =
        ∫ s in Ioi (0 : ℝ), banaszczykGaussianChiSquareKernel t s := by
      exact setIntegral_congr_fun measurableSet_Ioi fun s hs =>
        conditionalGaussian_mul_chiSquareThree hs.le
    _ = GaloisForLFunctions.HTGeometry.banaszczykRationalDensity t :=
      integral_banaszczykGaussianChiSquareKernel t

end RHTower
