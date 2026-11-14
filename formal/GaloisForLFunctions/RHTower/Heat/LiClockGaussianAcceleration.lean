import GaloisForLFunctions.RHTower.LiClockThetaInverseClass
import GaloisForLFunctions.RHTower.LiClockThetaTailCounterInput
import GaloisForLFunctions.HTGeometry.BorelResurgence.GaussianAccelerationExponential

/-!
# Gaussian acceleration of the theta clock and its causal inverse

Every derivative of the theta kernel, its clock and forcing inputs, its resolvent, and its two
responses has a proved exponential envelope. Gaussian acceleration is consequently convergent
at every positive time for all these functions. Linearity transports the exact causal clock
equation to the accelerated observables.
-/

open MeasureTheory Set GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace RHTower

noncomputable section

private theorem integrable_acceleration_of_exp_bound (g : ℝ → ℝ) (hg : Continuous g)
    (C R : ℝ) (hbound : ∀ x, |g x| ≤ C * Real.exp (R * |x|)) (s : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x * g x) := by
  have hC : 0 ≤ C := by
    have h := (abs_nonneg (g 0)).trans (hbound 0)
    simpa only [abs_zero, mul_zero, Real.exp_zero, mul_one] using h
  have hmajor := ((integrable_gaussianAcceleration_exponential s R).add
    (integrable_gaussianAcceleration_exponential s (-R))).const_mul C
  have hk : Continuous (gaussianAccelerationKernel (Real.exp s)) := by
    unfold gaussianAccelerationKernel
    fun_prop
  apply hmajor.mono' (hk.mul hg).aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  have he : Real.exp (R * |x|) ≤ Real.exp (R * x) + Real.exp (-R * x) := by
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_neg hx, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianAccelerationKernel_nonneg _ _)]
  calc
    gaussianAccelerationKernel (Real.exp s) x * |g x| ≤
        gaussianAccelerationKernel (Real.exp s) x * (C * Real.exp (R * |x|)) :=
      mul_le_mul_of_nonneg_left (hbound x) (gaussianAccelerationKernel_nonneg _ _)
    _ ≤ gaussianAccelerationKernel (Real.exp s) x *
        (C * (Real.exp (R * x) + Real.exp (-R * x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hC)
        (gaussianAccelerationKernel_nonneg _ _)
    _ = _ := by ring

/-- Every derivative of the literal theta kernel is accelerable at every positive time. -/
theorem integrable_gaussianAcceleration_liClockThetaKernel (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m liClockThetaKernel x) := by
  obtain ⟨C, hC⟩ := liClockEveryExpType_liClockThetaKernel 1 zero_lt_one m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liClockThetaKernel.continuous_iteratedDeriv m (natCast_lt_infty m).le) C 1 hC s

/-- Acceleration accommodates every derivative of the clock input `K + tK'`. -/
theorem integrable_gaussianAcceleration_liClockThetaClockInput (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m liClockThetaClockInput x) := by
  obtain ⟨C, hC⟩ := liClockEveryExpType_liClockThetaClockInput 1 zero_lt_one m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liClockThetaClockInput.continuous_iteratedDeriv m (natCast_lt_infty m).le) C 1 hC s

/-- The derivative forcing family has the same unrestricted positive-time acceleration. -/
theorem integrable_gaussianAcceleration_liClockThetaForcingInput (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m liClockThetaForcingInput x) := by
  obtain ⟨C, hC⟩ := liClockEveryExpType_liClockThetaForcingInput 1 zero_lt_one m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liClockThetaForcingInput.continuous_iteratedDeriv m (natCast_lt_infty m).le) C 1 hC s

/-- Every derivative of the causal theta resolvent is accelerable. -/
theorem integrable_gaussianAcceleration_liClockThetaResolvent (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m liClockThetaResolvent x) := by
  obtain ⟨δ, _, _, hgrowth⟩ := exists_liClockThetaResolvent_iteratedDeriv_growth
  obtain ⟨C, hC⟩ := hgrowth m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liClockThetaResolvent.continuous_iteratedDeriv m (natCast_lt_infty m).le) C δ hC s

/-- The actual full-copy clock response and all its derivatives are accelerable. -/
theorem integrable_gaussianAcceleration_liEvenCrossActualClockResponse (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m liEvenCrossActualClockResponse x) := by
  obtain ⟨δ, _, _, hgrowth⟩ := liClockSubGammaClass_liEvenCrossActualClockResponse
  obtain ⟨C, hC⟩ := hgrowth m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liEvenCrossActualClockResponse.continuous_iteratedDeriv m
      (natCast_lt_infty m).le) C δ hC s

/-- The signed massive response and every derivative have convergent acceleration. -/
theorem integrable_gaussianAcceleration_neg_liEvenCrossActualClockMassiveSource
    (s : ℝ) (m : ℕ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      iteratedDeriv m (fun t => -liEvenCrossActualClockMassiveSource t) x) := by
  obtain ⟨δ, _, _, hgrowth⟩ := liClockSubGammaClass_neg_liEvenCrossActualClockMassiveSource
  obtain ⟨C, hC⟩ := hgrowth m
  exact integrable_acceleration_of_exp_bound _
    (contDiff_liEvenCrossActualClockMassiveSource.neg.continuous_iteratedDeriv m
      (natCast_lt_infty m).le) C δ hC s

/-- The causal convolution is integrable because its exact value is the difference of two
accelerable clock functions. -/
theorem integrable_gaussianAcceleration_liClockThetaCausalConvolution (s : ℝ) :
    Integrable (fun x => gaussianAccelerationKernel (Real.exp s) x *
      volterraConv liEvenCrossActualClockResponse liClockThetaKernel x) := by
  have hh := integrable_gaussianAcceleration_liClockThetaClockInput s 0
  have hF := integrable_gaussianAcceleration_liEvenCrossActualClockResponse s 0
  simp only [iteratedDeriv_zero] at hh hF
  apply (hh.sub hF).congr
  refine ae_of_all _ fun x => ?_
  have he : volterraConv liEvenCrossActualClockResponse liClockThetaKernel x =
      liClockThetaClockInput x - liEvenCrossActualClockResponse x := by
    linarith only [liEvenCrossActualClockResponse_volterra_kernel x]
  dsimp only [Pi.sub_apply]
  rw [he]
  ring

/-- The exact causal clock equation survives Gaussian acceleration. -/
theorem gaussianAcceleration_liClockThetaCausalEquation (s : ℝ) :
    gaussianAcceleration liEvenCrossActualClockResponse (Real.exp s) +
      gaussianAcceleration (volterraConv liEvenCrossActualClockResponse liClockThetaKernel)
        (Real.exp s) = gaussianAcceleration liClockThetaClockInput (Real.exp s) := by
  have hF := integrable_gaussianAcceleration_liEvenCrossActualClockResponse s 0
  simp only [iteratedDeriv_zero] at hF
  unfold gaussianAcceleration
  rw [← integral_add hF.integrableOn
    (integrable_gaussianAcceleration_liClockThetaCausalConvolution s).integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [← mul_add, liEvenCrossActualClockResponse_volterra_kernel]

end

end RHTower

#print axioms RHTower.integrable_gaussianAcceleration_liClockThetaKernel
#print axioms RHTower.integrable_gaussianAcceleration_liClockThetaClockInput
#print axioms RHTower.integrable_gaussianAcceleration_liClockThetaForcingInput
#print axioms RHTower.integrable_gaussianAcceleration_liClockThetaResolvent
#print axioms RHTower.integrable_gaussianAcceleration_liEvenCrossActualClockResponse
#print axioms RHTower.integrable_gaussianAcceleration_neg_liEvenCrossActualClockMassiveSource
#print axioms RHTower.integrable_gaussianAcceleration_liClockThetaCausalConvolution
#print axioms RHTower.gaussianAcceleration_liClockThetaCausalEquation
