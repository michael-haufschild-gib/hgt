import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorQuadrature
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationOscillation
import GaloisForLFunctions.RHTower.LogarithmicSawtoothCorrelation
import GaloisForLFunctions.RHTower.LogarithmicSawtoothCorrelationBound
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationUniformBound
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDivisorSource

/-!
# Reciprocal reflection in the complete divisor-source floor work

Reflection exchanges the two factors on the reciprocal hyperbola. It
replaces the linearly weighted oscillatory work by a single unweighted
correlation, a source endpoint, and an error bounded uniformly by `3/2`.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitReciprocalErrorWork (T : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, ccmPrimeDeficitDilationForceError (T - s) *
    logarithmicCenteredSawtooth s

private theorem oscillation_integrable (T : ℝ) :
    IntervalIntegrable ccmPrimeDeficitDilationOscillation volume 0 T :=
  (intervalIntegrable_logarithmicCenteredSawtooth 0 T).mul_continuousOn (by fun_prop)

private theorem error_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable ccmPrimeDeficitDilationForceError volume 0 T :=
  (intervalIntegrable_ccmPrimeDeficitCenteredDilationForce hT).sub (oscillation_integrable T)

private theorem reverse_error_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => ccmPrimeDeficitDilationForceError (T - s)) volume 0 T := by
  simpa only [sub_zero, sub_self] using ((error_integrable hT).comp_sub_left T).symm

theorem intervalIntegrable_ccmPrimeDeficitReciprocalErrorWork {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun s => ccmPrimeDeficitDilationForceError (T - s) *
      logarithmicCenteredSawtooth s) volume 0 T := by
  have hf := intervalIntegrable_reverse_mul_fract_exp _ (error_integrable hT) hT
  have hc := (reverse_error_integrable hT).mul_const (1 / 2)
  apply (hf.sub hc).congr
  intro s _
  dsimp only [logarithmicCenteredSawtooth]
  ring

theorem ccmPrimeDeficitDivisorFloorWork_reflection {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitDivisorFloorWork T = ccmPrimeDeficitDilationRemainder T / 2 +
      (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T +
        ccmPrimeDeficitReciprocalErrorWork T := by
  let p := fun s => logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s
  have hg : IntervalIntegrable
      (fun s => ccmPrimeDeficitCenteredDilationForce (T - s)) volume 0 T := by
    simpa only [sub_zero, sub_self] using
      ((intervalIntegrable_ccmPrimeDeficitCenteredDilationForce hT).comp_sub_left T).symm
  have hp : IntervalIntegrable (fun s => (T - s - 1) * p s) volume 0 T :=
    (intervalIntegrable_logarithmicReciprocalSawtooth T 0 T).continuousOn_mul (by fun_prop)
  have he := intervalIntegrable_ccmPrimeDeficitReciprocalErrorWork hT
  have hpoint (s : ℝ) :
      ccmPrimeDeficitCenteredDilationForce (T - s) * Int.fract (Real.exp s) =
        (1 / 2) * ccmPrimeDeficitCenteredDilationForce (T - s) +
          (T - s - 1) * p s +
            ccmPrimeDeficitDilationForceError (T - s) * logarithmicCenteredSawtooth s := by
    dsimp only [p, logarithmicCenteredSawtooth, ccmPrimeDeficitDilationForceError,
      ccmPrimeDeficitDilationOscillation, ccmPrimeDeficitCenteredDilationForce]
    ring
  unfold ccmPrimeDeficitDivisorFloorWork
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add ((hg.const_mul (1 / 2)).add hp) he,
    intervalIntegral.integral_add (hg.const_mul (1 / 2)) hp,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left ccmPrimeDeficitCenteredDilationForce,
    sub_self, sub_zero]
  have hprimitive : (∫ s in (0 : ℝ)..T, ccmPrimeDeficitCenteredDilationForce s) =
      ccmPrimeDeficitDilationRemainder T := (ccmPrimeDeficitDilationRemainder_eq_integral hT).symm
  rw [hprimitive]
  change (1 / 2) * ccmPrimeDeficitDilationRemainder T +
    (∫ s in (0 : ℝ)..T, (T - s - 1) *
      (logarithmicCenteredSawtooth (T - s) * logarithmicCenteredSawtooth s)) +
        ccmPrimeDeficitReciprocalErrorWork T = _
  rw [logarithmicReciprocalSawtooth_weight_reflection]
  ring

theorem abs_ccmPrimeDeficitReciprocalErrorWork_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitReciprocalErrorWork T| ≤ 3 / 2 := by
  have hi := intervalIntegrable_ccmPrimeDeficitReciprocalErrorWork hT
  have hb : IntervalIntegrable (fun s : ℝ => (3 / 2) * Real.exp (-(T - s))) volume 0 T :=
    Continuous.intervalIntegrable (by fun_prop) 0 T
  calc
    _ ≤ ∫ s in (0 : ℝ)..T,
        |ccmPrimeDeficitDilationForceError (T - s) * logarithmicCenteredSawtooth s| :=
      intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ s in (0 : ℝ)..T, (3 / 2) * Real.exp (-(T - s)) := by
      apply intervalIntegral.integral_mono_on hT hi.abs hb
      intro s hs
      rw [abs_mul]
      calc
        _ ≤ (3 * Real.exp (-(T - s))) * (1 / 2) :=
          mul_le_mul (abs_ccmPrimeDeficitDilationForceError_le (sub_nonneg.mpr hs.2))
            (abs_logarithmicCenteredSawtooth_le s) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (3 / 2) * (1 - Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t : ℝ => Real.exp (-t)),
        sub_self, sub_zero, intervalIntegral.integral_comp_neg, integral_exp]
      simp only [neg_zero, Real.exp_zero]
    _ ≤ _ := by nlinarith only [Real.exp_pos (-T)]

theorem ccmPrimeDeficitDilationRemainder_dilation_reflection {T : ℝ} (hT : 0 ≤ T) :
    logarithmicDilationSum ccmPrimeDeficitDilationRemainder T =
      Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T -
        ccmPrimeDeficitDilationRemainder T / 2 -
          (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T -
            ccmPrimeDeficitReciprocalErrorWork T := by
  rw [ccmPrimeDeficitDilationRemainder_dilation_quadrature hT,
    ccmPrimeDeficitDivisorFloorWork_reflection hT]
  ring

theorem abs_ccmPrimeDeficitDilationRemainder_dilation_reflection_error_le
    {T : ℝ} (hT : 0 ≤ T) :
    |logarithmicDilationSum ccmPrimeDeficitDilationRemainder T -
      Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T +
        ccmPrimeDeficitDilationRemainder T / 2 +
          (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T| ≤ 3 / 2 := by
  rw [ccmPrimeDeficitDilationRemainder_dilation_reflection hT]
  convert abs_ccmPrimeDeficitReciprocalErrorWork_le hT using 1
  have heq : Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T -
      ccmPrimeDeficitDilationRemainder T / 2 -
        (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T -
          ccmPrimeDeficitReciprocalErrorWork T -
            Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T +
              ccmPrimeDeficitDilationRemainder T / 2 +
                (T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T =
      -ccmPrimeDeficitReciprocalErrorWork T := by ring
  rw [heq, abs_neg]

theorem abs_ccmPrimeDeficitDivisorFloorWork_le_linear {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorFloorWork T| ≤ 5 * T / 8 + 9 / 2 := by
  have hr := abs_ccmPrimeDeficitDilationRemainder_le_uniform hT
  have hc := abs_logarithmicReciprocalSawtoothCorrelation_le_uniform hT
  have he := abs_ccmPrimeDeficitReciprocalErrorWork_le hT
  have ht : |T - 2| ≤ T + 2 := abs_le.mpr (by constructor <;> linarith only [hT])
  have hprod : |(T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T| ≤
      (T + 2) / 2 * (5 / 4) := by
    rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2)]
    exact mul_le_mul (div_le_div_of_nonneg_right ht (by positivity)) hc (abs_nonneg _)
      (by positivity)
  rw [ccmPrimeDeficitDivisorFloorWork_reflection hT]
  calc
    _ ≤ |ccmPrimeDeficitDilationRemainder T / 2| +
        |(T - 2) / 2 * logarithmicReciprocalSawtoothCorrelation T| +
          |ccmPrimeDeficitReciprocalErrorWork T| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (7 / 2) / 2 + (T + 2) / 2 * (5 / 4) + 3 / 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2)]
      exact add_le_add (add_le_add (div_le_div_of_nonneg_right hr (by positivity)) hprod) he
    _ = _ := by ring

theorem abs_ccmPrimeDeficitDilationRemainder_dilation_centered_le_linear
    {T : ℝ} (hT : 0 ≤ T) :
    |logarithmicDilationSum ccmPrimeDeficitDilationRemainder T -
      Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T| ≤ 5 * T / 8 + 9 / 2 := by
  rw [ccmPrimeDeficitDilationRemainder_dilation_quadrature hT, sub_sub_cancel_left, abs_neg]
  exact abs_ccmPrimeDeficitDivisorFloorWork_le_linear hT

theorem ccmPrimeDeficitDivisorSource_centered_eq_dilationRemainder (T : ℝ) :
    ccmPrimeDeficitDivisorSource T - (Real.eulerMascheroniConstant + 1) *
      logarithmicDilationSum (fun t => Real.exp t - 1) T +
        Real.log (2 * Real.pi) / 2 * logarithmicDilationSum (fun t => t) T =
          logarithmicDilationSum ccmPrimeDeficitDilationRemainder T := by
  rw [← logarithmicDilationSum_dilationSource_eq_divisorSource]
  simp only [logarithmicDilationSum, logarithmicWeightedDilation, one_mul,
    ccmPrimeDeficitDilationRemainder, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

theorem abs_ccmPrimeDeficitDivisorSource_centered_le_linear {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeDeficitDivisorSource T - (Real.eulerMascheroniConstant + 1) *
      logarithmicDilationSum (fun t => Real.exp t - 1) T +
        Real.log (2 * Real.pi) / 2 * logarithmicDilationSum (fun t => t) T -
          Real.exp T * ccmPrimeDeficitDivisorMainCoefficient T| ≤ 5 * T / 8 + 9 / 2 := by
  rw [ccmPrimeDeficitDivisorSource_centered_eq_dilationRemainder]
  exact abs_ccmPrimeDeficitDilationRemainder_dilation_centered_le_linear hT

end RHTower
