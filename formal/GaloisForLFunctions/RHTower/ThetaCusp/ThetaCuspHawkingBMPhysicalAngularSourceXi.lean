import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalAngularSourceValue
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalSelfLaurent

/-! The evaluated physical source couples exactly to three native affine Xi values. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- At a nonreal argument the original completion and entire Xi have exactly the same zero condition. -/
theorem nativeCompletedLambda_zero_iff_xi {s : ℂ} (hs : s.im ≠ 0) :
    reflectedCompletedLambda s = 0 ↔ xi s = 0 := by
  have h0 : s ≠ 0 := by intro he; exact hs (by rw [he]; rfl)
  have h1 : s ≠ 1 := by intro he; exact hs (by rw [he]; rfl)
  have he : reflectedCompletedLambda s = completedRiemannZeta s := by
    rw [reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
    field_simp [gammaR_ne_zero_of_im_ne hs]
  have hp : s*(s-1)/2 ≠ 0 := div_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (by norm_num)
  rw [he,xi_eq_half_mul h0 h1,mul_eq_zero]
  simp only [hp,false_or]

/-- No cutoff or Gamma ambiguity remains: angular cancellation is exactly incidence at these three original Xi arguments. -/
theorem physicalSelfSourceCoefficient_zero_iff_xi (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔
      xi (5*(q.1:ℂ)/2-1) = 0 ∨ xi ((q.1:ℂ)/2) = 0 ∨ xi (3*(q.1:ℂ)/2) = 0 := by
  have hi := xi_divisor_support_im_ne_zero q.1
  have ha : (5*(q.1:ℂ)/2-1).im ≠ 0 := by
    simpa [Complex.mul_im] using div_ne_zero (mul_ne_zero (by norm_num : (5:ℝ) ≠ 0) hi)
      (by norm_num : (2:ℝ) ≠ 0)
  have hb : ((q.1:ℂ)/2).im ≠ 0 := by simpa using div_ne_zero hi (by norm_num : (2:ℝ) ≠ 0)
  have hc : (1-3*(q.1:ℂ)/2).im ≠ 0 := by
    simpa [Complex.mul_im] using neg_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num : (3:ℝ) ≠ 0) hi) (by norm_num : (2:ℝ) ≠ 0))
  rw [physicalSelfSourceCoefficient_zero_iff_Lambda q hq,nativeCompletedLambda_zero_iff_xi ha,
    nativeCompletedLambda_zero_iff_xi hb,nativeCompletedLambda_zero_iff_xi hc,xi_one_sub]

/-- The original scalar pole survives exactly when the three native Xi incidences and radial source cancellation are absent. -/
theorem continuedPhysicalSelfResponse_nonremovable_iff_xi (q : XiZeroCopy)
    (hq : 1/2 < (q.1:ℂ).re) (branch side : Bool) (a : ℂ) (t : ℝ) (ht : t < 0) :
    (¬ ∃ c : ℂ, Tendsto (fun w => continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 c)) ↔
      xi (5*(q.1:ℂ)/2-1) ≠ 0 ∧ xi ((q.1:ℂ)/2) ≠ 0 ∧ xi (3*(q.1:ℂ)/2) ≠ 0 ∧
      clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
        (physicalRate q branch) a t ≠ 0 := by
  rw [continuedPhysicalSelfResponse_nonremovable_iff q branch side a t ht]
  simp only [ne_eq,physicalSelfSourceCoefficient_zero_iff_xi q hq,not_or,and_assoc]

end
end RHTower.D4BMJointSource
