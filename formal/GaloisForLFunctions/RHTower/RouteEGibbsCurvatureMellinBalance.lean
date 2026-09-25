import GaloisForLFunctions.RHTower.RouteEGibbsProductSwitchCriticalChamber
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Mellin balance of the two Gibbs curvature chambers

The mixed product curvature has an exact Gamma-recursion marginal. At exponent one
its positive and negative chambers cancel in the continuum. No arithmetic sampling
or RH-scale cancellation is inferred from this identity.
-/

open MeasureTheory Set Real

namespace RHTower

theorem routeEGibbsCurvatureMellinIntegral
    {β a σ : ℝ} (hβ : 0 < β) (ha : 0 < a) (hσ : 0 < σ) :
    (∫ b in Ioi (0 : ℝ),
      b ^ (σ - 1) * (β * ((β * a) * b - 1) * Real.exp (-((β * a) * b)))) =
      β * (1 / (β * a)) ^ σ * (σ - 1) * Real.Gamma σ := by
  let c := β * a
  have hc : 0 < c := mul_pos hβ ha
  have h0 : IntegrableOn (fun b : ℝ => b ^ (σ - 1) * Real.exp (-(c * b))) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := σ - 1) (b := c) (by linarith) le_rfl hc)
  have h1 : IntegrableOn (fun b : ℝ => b ^ σ * Real.exp (-(c * b))) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := σ) (b := c) (by linarith) le_rfl hc)
  have hi0 : (∫ b in Ioi (0 : ℝ), b ^ (σ - 1) * Real.exp (-(c * b))) =
      (1 / c) ^ σ * Real.Gamma σ := by
    simpa using (integral_rpow_mul_exp_neg_mul_Ioi hσ hc)
  have hi1 : (∫ b in Ioi (0 : ℝ), b ^ σ * Real.exp (-(c * b))) =
      (1 / c) ^ (σ + 1) * Real.Gamma (σ + 1) := by
    simpa only [add_sub_cancel_right] using
      (integral_rpow_mul_exp_neg_mul_Ioi (a := σ + 1) (r := c)
        (by linarith) hc)
  have hrpow : c * (1 / c) ^ (σ + 1) = (1 / c) ^ σ := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
    have hcinv : c * (1 / c) = 1 := by field_simp [hc.ne']
    calc c * ((1 / c) ^ σ * (1 / c)) = (1 / c) ^ σ * (c * (1 / c)) := by ring
      _ = (1 / c) ^ σ := by rw [hcinv, mul_one]
  have hint :
      (∫ b in Ioi (0 : ℝ),
        b ^ (σ - 1) * (β * (c * b - 1) * Real.exp (-(c * b)))) =
      β * c * (∫ b in Ioi (0 : ℝ), b ^ σ * Real.exp (-(c * b))) -
        β * (∫ b in Ioi (0 : ℝ), b ^ (σ - 1) * Real.exp (-(c * b))) := by
    have hfun : Set.EqOn
        (fun b : ℝ => b ^ (σ - 1) * (β * (c * b - 1) * Real.exp (-(c * b))))
        (fun b : ℝ => β * c * (b ^ σ * Real.exp (-(c * b))) -
          β * (b ^ (σ - 1) * Real.exp (-(c * b)))) (Ioi 0) := by
      intro b hb
      dsimp only
      have hbpos : 0 < b := hb
      have hpow : b ^ σ = b ^ (σ - 1) * b := by
        conv_lhs => rw [show σ = (σ - 1) + 1 by ring]
        rw [Real.rpow_add hbpos, Real.rpow_one]
      rw [hpow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun]
    rw [integral_sub (h1.const_mul _) (h0.const_mul _), integral_const_mul,
      integral_const_mul]
  change (∫ b in Ioi (0 : ℝ),
    b ^ (σ - 1) * (β * (c * b - 1) * Real.exp (-(c * b)))) = _
  rw [hint, hi0, hi1, Real.Gamma_add_one hσ.ne']
  calc
    β * c * ((1 / c) ^ (σ + 1) * (σ * Real.Gamma σ)) -
        β * ((1 / c) ^ σ * Real.Gamma σ) =
      β * (c * (1 / c) ^ (σ + 1)) * σ * Real.Gamma σ -
        β * (1 / c) ^ σ * Real.Gamma σ := by ring
    _ = β * (1 / c) ^ σ * (σ - 1) * Real.Gamma σ := by rw [hrpow]; ring
    _ = β * (1 / (β * a)) ^ σ * (σ - 1) * Real.Gamma σ := rfl

theorem routeEGibbsCurvatureMellinIntegral_one_zero
    {β a : ℝ} (hβ : 0 < β) (ha : 0 < a) :
    (∫ b in Ioi (0 : ℝ),
      β * ((β * a) * b - 1) * Real.exp (-((β * a) * b))) = 0 := by
  simpa using (routeEGibbsCurvatureMellinIntegral hβ ha (show 0 < (1 : ℝ) by norm_num))

end RHTower
