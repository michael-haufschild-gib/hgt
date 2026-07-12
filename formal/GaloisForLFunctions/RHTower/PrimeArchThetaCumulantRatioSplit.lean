import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# A two-ratio source gate for the first prime--archimedean Hankel block

The previously isolated fourth-moment concentration condition is stronger than the actual
theta-cusp source satisfies.  This module replaces it by two numerically viable, source-pure
quadratic moment-ratio inequalities.  Their weighted sum is exactly three times the cubic raw
moment expression controlling the first nonconstant prime--archimedean Hankel block.

The module proves the reduction only.  It does not assert either ratio inequality for the actual
theta-cusp source.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- A strengthened adjacent log-convexity inequality at raw moment levels `1,2,3`. -/
def ThetaCuspUpperAdjacentRatioSeparation : Prop :=
  14 * thetaCuspRawEvenMoment 2 ^ 2 ≤
    9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3

/-- A relaxed fourth-moment concentration inequality at raw moment levels `0,1,2`. -/
def ThetaCuspRelaxedFourthMomentConcentration : Prop :=
  16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ≤
    45 * thetaCuspRawEvenMoment 1 ^ 2

/-- The two quadratic ratio defects resolve the cubic raw-moment obstruction exactly:

`m₀(9m₁m₃ - 14m₂²) + m₂(45m₁² - 16m₀m₂) = 3C`,

where `C = 3m₀m₁m₃ + 15m₁²m₂ - 10m₀m₂²`. -/
theorem thetaCusp_ratioSplit_exact_identity :
    thetaCuspRawEvenMoment 0 *
          (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
            14 * thetaCuspRawEvenMoment 2 ^ 2) +
        thetaCuspRawEvenMoment 2 *
          (45 * thetaCuspRawEvenMoment 1 ^ 2 -
            16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) =
      3 *
        (3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
            thetaCuspRawEvenMoment 3 +
          15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
          10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2) := by
  ring

/-- The two source-pure quadratic ratio inequalities force the cubic raw-moment inequality. -/
theorem thetaCusp_raw_cubic_nonneg_of_ratioSplit
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration) :
    0 ≤ 3 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 1 *
          thetaCuspRawEvenMoment 3 +
        15 * thetaCuspRawEvenMoment 1 ^ 2 * thetaCuspRawEvenMoment 2 -
        10 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ^ 2 := by
  rw [ThetaCuspUpperAdjacentRatioSeparation] at hupper
  rw [ThetaCuspRelaxedFourthMomentConcentration] at hrelaxed
  have h0 := thetaCuspRawEvenMoment_nonneg 0
  have h2 := thetaCuspRawEvenMoment_nonneg 2
  have hupperWeighted :
      0 ≤ thetaCuspRawEvenMoment 0 *
        (9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 -
          14 * thetaCuspRawEvenMoment 2 ^ 2) := by
    exact mul_nonneg h0 (sub_nonneg.mpr hupper)
  have hrelaxedWeighted :
      0 ≤ thetaCuspRawEvenMoment 2 *
        (45 * thetaCuspRawEvenMoment 1 ^ 2 -
          16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2) := by
    exact mul_nonneg h2 (sub_nonneg.mpr hrelaxed)
  nlinarith [hrelaxedWeighted]

/-- The two-ratio source gate discharges the exact first nonconstant Hankel determinant. -/
theorem thetaCuspSixthMomentHankelInequality_of_ratioSplit
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration) :
    ThetaCuspSixthMomentHankelInequality := by
  have hcubic := thetaCusp_raw_cubic_nonneg_of_ratioSplit hupper hrelaxed
  rw [ThetaCuspSixthMomentHankelInequality]
  simp only [thetaCuspNormalizedEvenMoment]
  have h0 := thetaCuspRawEvenMoment_zero_pos
  field_simp [h0.ne']
  nlinarith [hcubic]

/-- Under the two ratio conditions, every real linear-polynomial prime--Gamma source Hankel test
is nonnegative. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
    (hupper : ThetaCuspUpperAdjacentRatioSeparation)
    (hrelaxed : ThetaCuspRelaxedFourthMomentConcentration) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  rw [forall_primeArchSourceTraceHankel_linear_nonneg_iff_thetaCuspSixthMomentHankelInequality]
  exact thetaCuspSixthMomentHankelInequality_of_ratioSplit hupper hrelaxed

end

end RHTower
