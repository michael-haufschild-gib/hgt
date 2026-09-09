import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarCutoffBoundaryValue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeCutoffPowerMoments

/-! The full cutoff bulk moment equals the unchanged transition plus its exact terminal power integral. -/
open Complex Set MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem weighted_cutoff_integrable (v : ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(v-1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le ha (by simpa only [min_eq_left hab] using hy.1)
  exact (nativeCutoff_height_continuous.continuousAt.mul
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))).continuousWithinAt

/-- All cutoff pieces are retained, including the constant tail between the original transition and boundary. -/
theorem cutoffBulkMoment_eq_transition (delta k : ℂ) (hv : delta+k-1 ≠ 0) :
    cutoffBulkMoment delta k = nativeCutoffTransitionMoment (delta+k-1)+
      ((4:ℂ)^(delta+k-1)-(3:ℂ)^(delta+k-1))/(delta+k-1) := by
  let v := delta+k-1
  let f := fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(v-1)
  have he : cutoffBulkMoment delta k = ∫ y in (1:ℝ)..4, f y := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy0 : 0 < y := by
      norm_num only [uIcc_of_le (by norm_num : (1:ℝ)≤4),mem_Icc] at hy
      linarith [hy.1]
    dsimp [f,powerCutoffHeight,cutoffPower]
    rw [mul_left_comm,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy0.ne')]
    congr 2
    dsimp [v]
    ring
  have hi12 := weighted_cutoff_integrable v 1 2 (by norm_num) (by norm_num)
  have hi23 := weighted_cutoff_integrable v 2 3 (by norm_num) (by norm_num)
  have hi34 := weighted_cutoff_integrable v 3 4 (by norm_num) (by norm_num)
  have hl : (∫ y in (1:ℝ)..2, f y) = 0 := by
    calc
      _ = ∫ _y in (1:ℝ)..2, (0:ℂ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy2 : y ≤ 2 := (show y ∈ Icc (1:ℝ) 2 by simpa using hy).2
        dsimp [f,cutoff]
        rw [Real.smoothTransition.zero_of_nonpos (by change y-2≤0; linarith)]
        simp
      _ = 0 := by simp
  have hm : (∫ y in (2:ℝ)..3, f y) = nativeCutoffTransitionMoment v :=
    intervalIntegral.integral_of_le (by norm_num)
  have hh : (∫ y in (3:ℝ)..4, f y) = ((4:ℂ)^v-(3:ℂ)^v)/v := by
    calc
      _ = ∫ y in (3:ℝ)..4, (y:ℂ)^(v-1) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy3 : 3 ≤ y := (show y ∈ Icc (3:ℝ) 4 by
          simpa only [uIcc_of_le (by norm_num : (3:ℝ)≤4)] using hy).1
        dsimp [f,cutoff]
        rw [Real.smoothTransition.one_of_one_le (by change 1≤y-2; linarith)]
        simp
      _ = _ := by
        rw [integral_cpow (Or.inr ⟨by intro h; apply hv; dsimp [v] at h; linear_combination h,
          by norm_num⟩)]
        simp only [sub_add_cancel,Complex.ofReal_ofNat]
  rw [he,← intervalIntegral.integral_add_adjacent_intervals (hi12.trans hi23) hi34,
    ← intervalIntegral.integral_add_adjacent_intervals hi12 hi23,hl,hm,hh,zero_add]

/-- The original cutoff mismatch quotient uses exactly the native Mellin continuation. -/
theorem cutoffBulkMoment_eq_nativeMellin (delta k : ℂ) (hv : delta+k-1 ≠ 0) :
    cutoffBulkMoment delta k = (4:ℂ)^(delta+k-1)/(delta+k-1)-nativeCutoffMellinContinuation (delta+k-1) := by
  rw [cutoffBulkMoment_eq_transition delta k hv]
  unfold nativeCutoffMellinContinuation
  ring

end
end RHTower.D4BMJointSource
