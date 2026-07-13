import GaloisForLFunctions.HTGeometry.SzegoLowerBound
import GaloisForLFunctions.HTGeometry.RieszBrothersReduction
import GaloisForLFunctions.HTGeometry.SzegoConcretePolynomial

/-!
# Transporting the Szegő lower bound to `circleLebesgue`

The classical Szegő/Jensen machinery of `SzegoLowerBound` is phrased with `Real.circleAverage` over
the angular parametrization.  This module bridges those angular averages to Bochner integrals
against `circleLebesgue`, the normalized Haar probability measure used as the reference measure `m`
in the first Szegő limit theorem, so that the lower bound can be run against a general finite circle
measure and its Radon–Nikodym density.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real
open scoped ComplexConjugate

/-- **Circle-measure ↔ angular-average bridge.**  Integrating a function of `z ∈ Circle` against the
normalized Haar (Lebesgue) probability measure equals its `circleAverage` over the angular
parametrization. -/
theorem integral_circleLebesgue_eq_circleAverage (F : ℂ → ℝ)
    (hF : AEStronglyMeasurable (fun z : Circle => F (z : ℂ)) circleLebesgue) :
    ∫ z : Circle, F (z : ℂ) ∂circleLebesgue = circleAverage F 0 1 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  rw [circleLebesgue] at hF ⊢
  rw [integral_map (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).continuous.aemeasurable hF]
  simp only [AddCircle.homeomorphCircle_apply]
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  have hcv : (fun a : ℝ => F ((AddCircle.toCircle (↑a : AddCircle (1 : ℝ)) : Circle) : ℂ))
      = fun a : ℝ => F (circleMap 0 1 (2 * Real.pi * a)) := by
    funext a
    congr 1
    rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, circleMap]
    simp
  rw [hcv]
  have hcomp := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun θ => F (circleMap 0 1 θ)) (show (2 * Real.pi) ≠ 0 by positivity)
  simp only [mul_zero, mul_one] at hcomp
  rw [hcomp, Real.circleAverage]

/-- **Transported sub-mean-value inequality.**  The `circleLebesgue`-average of `log‖q*‖` is
nonnegative, because `q* = revPoly` is a polynomial with `q*(0) = 1`: Jensen's inequality gives
`log‖q*(0)‖ = 0 ≤ average of log‖q*‖`.  This is the factor that makes `exp(∫ log‖q*‖²) ≥ 1` in the
Szegő lower bound. -/
theorem integral_log_revPoly_nonneg (c : ℕ → ℂ) (N : ℕ) :
    (0 : ℝ) ≤ ∫ z : Circle, Real.log ‖revPoly c N (z : ℂ)‖ ∂circleLebesgue := by
  have hd : Differentiable ℂ (revPoly c N) := by unfold revPoly; fun_prop
  have hana : AnalyticOnNhd ℂ (revPoly c N) (Metric.closedBall 0 |(1 : ℝ)|) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd).mono (Set.subset_univ _)
  have h0 : revPoly c N 0 ≠ 0 := by rw [revPoly_zero]; exact one_ne_zero
  have hsub := log_norm_center_le_circleAverage_log_norm (revPoly c N) hana h0
  rw [revPoly_zero, norm_one, Real.log_one] at hsub
  have hcont : Continuous (fun z : Circle => revPoly c N (z : ℂ)) :=
    hd.continuous.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun z : Circle => Real.log ‖revPoly c N (z : ℂ)‖) circleLebesgue :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  rwa [← integral_circleLebesgue_eq_circleAverage (fun w => Real.log ‖revPoly c N w‖) hmeas] at hsub

end GaloisForLFunctions.HTGeometry
