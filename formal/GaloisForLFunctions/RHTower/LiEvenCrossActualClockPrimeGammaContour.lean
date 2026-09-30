import GaloisForLFunctions.RHTower.InverseTiltedPrimeGammaCentralSource
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.DiffContOnCl

import GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra
import Mathlib.MeasureTheory.Integral.CircleIntegral
import GaloisForLFunctions.RHTower.LiClockCentralSineContour

/-!
# Exact central prime–Gamma circle functional for the literal clock response

One source-side analytic radius works for every real clock.  The generic Cauchy–sine
transform reads the complete complex central coefficients, preserving all multiplicities
through the literal response.  The odd-trace formula uses the filled divided difference
at the center and keeps its exact negative sign.
-/

open Complex Filter Set Metric Topology
open scoped Real
namespace RHTower
noncomputable section

private theorem inverseTiltedPrimeGammaSourceTrace_zero :
    inverseTiltedPrimeGammaSourceTrace 0 = 0 := by
  exact inverseTiltedPrimeGammaSourceTrace_eventuallyEq_continuedPrimeArchSourceRelativeTrace.eq_of_nhds.trans
    continuedPrimeArchSourceRelativeTrace_zero

private theorem inverseTiltedPrimeGammaSourceTrace_eq_neg_mul_germ (z : ℂ) :
    inverseTiltedPrimeGammaSourceTrace z =
      -z * normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z := by
  simpa only [oddTracePreimage] using
    (congrFun (oddTracePreimage_normalizedTraceMomentGerm_eq
      inverseTiltedPrimeGammaSourceTrace inverseTiltedPrimeGammaSourceTrace_zero) z).symm

private theorem iteratedDeriv_inverseTiltedPrimeGammaSourceGerm_two_mul (j : ℕ) :
    iteratedDeriv (2 * j)
      (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace) 0 =
      (((2 * j).factorial : ℕ) : ℂ) * (normalizedPrimeArchMoment j : ℂ) := by
  rw [normalizedTraceMomentGerm_inverseTiltedPrimeGammaSource_eventuallyEq.iteratedDeriv_eq (2 * j)]
  simpa only [normalizedPrimeArchMoment] using
    iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul j

private theorem exists_inverseTiltedPrimeGammaSourceGerm_central_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      DiffContOnCl ℂ (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace)
        (ball (0 : ℂ) r) := by
  have hG := analyticAt_normalizedTraceMomentGerm analyticAt_inverseTiltedPrimeGammaSourceTrace
  obtain ⟨s, hs, hA⟩ := hG.exists_mem_nhds_analyticOnNhd
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨r₀, hr₀, fun r _hr hrr₀ => ?_⟩
  exact hA.differentiableOn.diffContOnCl_ball
    ((closedBall_subset_ball hrr₀).trans hball)



private theorem trace_circle_eq_neg_germ_circle {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (∮ z in C(0, r), inverseTiltedPrimeGammaSourceTrace z * Complex.sin ((t : ℂ)/z) / z) =
      -(∮ z in C(0, r), normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
        Complex.sin ((t : ℂ)/z)) := by
  calc
    _ = ∮ z in C(0, r), (-1 : ℂ) *
        (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
          Complex.sin ((t : ℂ)/z)) := by
      apply circleIntegral.integral_congr hr.le
      intro z hz
      have hz0 : z ≠ 0 := by
        intro hz0
        subst z
        simp at hz
        linarith
      dsimp only
      rw [inverseTiltedPrimeGammaSourceTrace_eq_neg_mul_germ z]
      field_simp
    _ = _ := by
      rw [circleIntegral.integral_const_mul]
      ring

private theorem contour_unit_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero



private theorem primeGammaContourTerm_eq_responseTerm (t : ℝ) (j : ℕ) :
    liClockCentralSineContourTerm
      (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace) (t : ℂ) j =
      (liEvenCrossActualClockResponseTerm t j : ℂ) := by
  unfold liClockCentralSineContourTerm liEvenCrossActualClockResponseTerm
  rw [iteratedDeriv_inverseTiltedPrimeGammaSourceGerm_two_mul]
  push_cast
  have heven : ((2*j).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*j)
  have hodd : ((2*j+1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2*j+1)
  field_simp

/-- One source-side central radius gives both exact phase-preserving contour formulas
for every real clock, with the filled source normalization and full multiplicity. -/
theorem exists_liEvenCrossActualClockPrimeGammaContour_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ t : ℝ,
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0, r), normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
          Complex.sin ((t : ℂ)/z)) = (liEvenCrossActualClockResponse t : ℂ)) ∧
      (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0, r), inverseTiltedPrimeGammaSourceTrace z *
          Complex.sin ((t : ℂ)/z) / z) = (liEvenCrossActualClockResponse t : ℂ)) := by
  obtain ⟨r₀, hr₀, hG⟩ := exists_inverseTiltedPrimeGammaSourceGerm_central_radius
  refine ⟨min r₀ (1/2), lt_min hr₀ (by norm_num), fun r hr hrr₀ t => ?_⟩
  have hGr := hG r hr (hrr₀.trans_le (min_le_left _ _))
  have hsum : (∑' j : ℕ, liClockCentralSineContourTerm
      (normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace) (t : ℂ) j) =
        (liEvenCrossActualClockResponse t : ℂ) := by
    rw [liEvenCrossActualClockResponse_eq_tsum, Complex.ofReal_tsum]
    exact tsum_congr (fun j => primeGammaContourTerm_eq_responseTerm t j)
  have hraw := liClockCentralSineContour_eq_tsum hr hGr (t : ℂ)
  rw [hsum] at hraw
  have hfirst : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∮ z in C(0, r), normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
        Complex.sin ((t : ℂ)/z)) = (liEvenCrossActualClockResponse t : ℂ) := by
    rw [hraw]
    simp only [← mul_assoc, inv_mul_cancel₀ contour_unit_ne_zero, one_mul]
  refine ⟨hfirst, ?_⟩
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C(0, r), normalizedTraceMomentGerm inverseTiltedPrimeGammaSourceTrace z *
          Complex.sin ((t : ℂ)/z)) := by
      rw [trace_circle_eq_neg_germ_circle hr t]
      ring
    _ = _ := hfirst

end
end RHTower


