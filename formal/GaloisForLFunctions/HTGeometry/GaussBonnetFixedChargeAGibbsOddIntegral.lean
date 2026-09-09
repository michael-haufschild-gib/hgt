import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsOddIntegrand
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorGibbsIntegral

/-!
# Exact energy identity for the first odd Gibbs correction

The divided difference of the actual normalized energy profile is the
integral of its divided force difference. Its limiting primitive is the
odd quintic polynomial C₁ t (t² - 1)².
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAGibbsOddGap_integral (w φ τ l ψ : ℝ) :
    (egbFixedChargeAInteriorGibbsGap w φ τ l ψ / egbCoexistenceASymmetricRatio τ ^ 4 -
      egbFixedChargeAGibbsBarrierCoefficient w φ * cos ψ ^ 4) / egbCoexistenceASymmetricRatio τ =
        ∫ u in (0 : ℝ)..1, egbFixedChargeAGibbsOddIntegrand w φ τ ψ u := by
  have hint : IntervalIntegrable (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ) volume 0 1 := by
    have hc : Continuous (egbFixedChargeAInteriorGibbsLimitIntegrand w φ ψ) := by
      unfold egbFixedChargeAInteriorGibbsLimitIntegrand egbFixedChargeAInteriorPathCoordinate
      fun_prop
    exact hc.intervalIntegrable 0 1
  simp only [egbFixedChargeAGibbsOddIntegrand_difference, intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub (egbFixedChargeAInteriorGibbsIntegrand_intervalIntegrable w φ τ ψ) hint,
    egbFixedChargeAInteriorGibbsLimitIntegrand_integral, ← egbFixedChargeAInteriorGibbsGap_integral w φ τ l ψ]

theorem egbFixedChargeAGibbsOddLimitIntegrand_antiderivative (w φ ψ u : ℝ) :
    HasDerivAt (fun x => egbFixedChargeAGibbsOddCoefficient w φ *
      (egbFixedChargeAInteriorPathCoordinate ψ x * (egbFixedChargeAInteriorPathCoordinate ψ x ^ 2 - 1) ^ 2))
      (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ u) u := by
  have hc := egbFixedChargeAInteriorPathCoordinate_hasDerivAt ψ u
  have h := (hc.mul (((hc.pow 2).sub_const 1).pow 2)).const_mul (egbFixedChargeAGibbsOddCoefficient w φ)
  apply h.congr_deriv
  unfold egbFixedChargeAGibbsOddLimitIntegrand egbFixedChargeAGibbsOddLimitKernel
  simp only [Pi.pow_apply]
  ring

theorem egbFixedChargeAGibbsOddLimitIntegrand_integral (w φ ψ : ℝ) :
    (∫ u in (0 : ℝ)..1, egbFixedChargeAGibbsOddLimitIntegrand w φ ψ u) =
      egbFixedChargeAGibbsOddCoefficient w φ * sin ψ * cos ψ ^ 4 := by
  have hint : IntervalIntegrable (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ) volume 0 1 := by
    have hc : Continuous (egbFixedChargeAGibbsOddLimitIntegrand w φ ψ) := by
      unfold egbFixedChargeAGibbsOddLimitIntegrand egbFixedChargeAGibbsOddLimitKernel egbFixedChargeAInteriorPathCoordinate
      fun_prop
    exact hc.intervalIntegrable 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => egbFixedChargeAGibbsOddLimitIntegrand_antiderivative w φ ψ u) hint
  have hs : sin ψ ^ 2 - 1 = -(cos ψ ^ 2) := by linarith [sin_sq_add_cos_sq ψ]
  calc
    _ = egbFixedChargeAGibbsOddCoefficient w φ * (sin ψ * (sin ψ ^ 2 - 1) ^ 2) := by
      simpa only [egbFixedChargeAInteriorPathCoordinate_end, egbFixedChargeAInteriorPathCoordinate_start,
        one_pow, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, sub_zero] using h
    _ = _ := by rw [hs]; ring

end GaloisForLFunctions.HTGeometry
