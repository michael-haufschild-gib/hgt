import GaloisForLFunctions.RHTower.PaperThetaObservationEntropy
import GaloisForLFunctions.HTGeometry.ThetaHasseKMSContinuousAssembly

/-! # Source budgets for literal observed theta reflection gaps

Finite observed statistics retain their original theta integrals. The paper
Pinsker inequality bounds their native reflection gap, with optional centering
of the statistic to reduce the oscillation factor.
-/

namespace RHTower
noncomputable section
open MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
private theorem finite_expectation_contrast (P Q : Law α) (g : α → ℝ) :
    |P.Ex g - Q.Ex g| ≤ 2 * ‖g‖ * P.tv Q := by
  unfold Law.Ex
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    |∑ i, (P i - Q i) * g i| ≤ ∑ i, |(P i - Q i) * g i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |P i - Q i| * ‖g‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g i) (abs_nonneg _)
    _ = 2 * ‖g‖ * P.tv Q := by rw [← Finset.sum_mul, Law.tv]; ring

/-- The native reflection gap is exactly the difference of the observed finite expectations. -/
theorem paperThetaObservation_reflectionGap_eq (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → ℝ) :
    thetaTiltStatisticReflectionGap (fun x => g (f x)) a =
      (paperThetaObservationLaw a f).Ex g -
        (paperThetaObservationLaw (paperThetaTiltReflection a) f).Ex g := by
  rw [thetaTiltStatisticReflectionGap,
    thetaTiltStatisticMean_eq_integral a.property,
    thetaTiltStatisticMean_eq_integral (a := -(a : ℝ)) (by simpa only [abs_neg] using a.property),
    paperThetaObservationLaw_Ex, paperThetaObservationLaw_Ex]
  rfl

theorem paperThetaObservation_reflectionGap_tv (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → ℝ) :
    |thetaTiltStatisticReflectionGap (fun x => g (f x)) a| ≤
      2 * ‖g‖ * (paperThetaObservationLaw a f).tv
        (paperThetaObservationLaw (paperThetaTiltReflection a) f) := by
  rw [paperThetaObservation_reflectionGap_eq]
  exact finite_expectation_contrast _ _ _

/-- The literal native reflection gap inherits the exact theta source information budget. -/
theorem paperThetaObservation_reflectionGap_source_budget (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → ℝ) :
    |thetaTiltStatisticReflectionGap (fun x => g (f x)) a| ≤
      2 * ‖g‖ * Real.sqrt (2 * (a : ℝ) * thetaTiltMean a) :=
  (paperThetaObservation_reflectionGap_tv a f g).trans
    (mul_le_mul_of_nonneg_left (paperThetaObservation_tv_budget a f) (by positivity))

/-- Subtracting any common constant leaves the gap unchanged and sharpens its size factor. -/
theorem paperThetaObservation_reflectionGap_centered_budget (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → ℝ) (c : ℝ) :
    |thetaTiltStatisticReflectionGap (fun x => g (f x)) a| ≤
      2 * ‖fun i => g i - c‖ * Real.sqrt (2 * (a : ℝ) * thetaTiltMean a) := by
  have h := paperThetaObservation_reflectionGap_source_budget a f (fun i => g i - c)
  rw [paperThetaObservation_reflectionGap_eq a f (fun i => g i - c)] at h
  rw [paperThetaObservation_reflectionGap_eq a f g]
  simp only [Law.Ex_sub, Law.Ex_const] at h
  convert h using 1
  congr 1
  ring

end
end RHTower
