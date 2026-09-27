import GaloisForLFunctions.RHTower.CCMPrimeDeficitNoetherAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The conservative-force action and its Noether boundary term

The ordinary kinetic-minus-potential action differs from the translation
invariant deficit action by the endpoint term q(T)D(T). Absolute continuity
justifies integration by parts across all prime entries. Consequently a
position translation changes the ordinary action by cD(T), and its Noether
charge is velocity minus D(T).
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

def ccmPrimeDeficitForceAction (q : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, (deriv q t) ^ 2 / 2 - ccmPrimeDeficitPotential t (q t)

/-- Exact boundary correction relating the two actions on every C1 path. -/
theorem ccmPrimeDeficitAction_eq_forceAction_sub_boundary (q : ℝ → ℝ)
    (hq : ContDiff ℝ 1 q) (T : ℝ) :
    ccmPrimeDeficitAction q 0 T = ccmPrimeDeficitForceAction q T -
      q T * ccmLogChebyshevDeficitPrimitive T := by
  have hf : IntervalIntegrable (fun t => Real.exp t - Chebyshev.psi (Real.exp t)) volume 0 T :=
    (Real.continuous_exp.intervalIntegrable 0 T).sub
      ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)
  have hD : AbsolutelyContinuousOnInterval ccmLogChebyshevDeficitPrimitive 0 T :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hparts := hD.integral_mul_deriv_eq_deriv_mul hq.contDiffOn.absolutelyContinuousOnInterval
  have hvel : deriv (ccmPrimeDeficitTrajectory 0 0) = ccmLogChebyshevDeficitPrimitive := by
    funext t
    simpa only [zero_add] using (hasDerivAt_ccmPrimeDeficitTrajectory 0 0 t).deriv
  have hderiv : ∀ᵐ t : ℝ ∂volume,
      deriv ccmLogChebyshevDeficitPrimitive t = Real.exp t - Chebyshev.psi (Real.exp t) := by
    filter_upwards [ccmPrimeDeficitTrajectory_newton_ae 0 0] with t ht
    simpa only [hvel, ccmPrimeDeficitPotential_force] using ht
  have hint : (∫ t in (0 : ℝ)..T, deriv ccmLogChebyshevDeficitPrimitive t * q t) =
      ∫ t in (0 : ℝ)..T, q t * (Real.exp t - Chebyshev.psi (Real.exp t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with t ht _
    rw [ht, mul_comm]
  rw [hint, show ccmLogChebyshevDeficitPrimitive 0 = 0 by
    simp [ccmLogChebyshevDeficitPrimitive], zero_mul, sub_zero] at hparts
  have hk : IntervalIntegrable (fun t => (deriv q t) ^ 2 / 2) volume 0 T :=
    ((hq.continuous_deriv_one.pow 2).div_const 2).intervalIntegrable 0 T
  have hDv : IntervalIntegrable (fun t => ccmLogChebyshevDeficitPrimitive t * deriv q t) volume 0 T :=
    (continuous_ccmLogChebyshevDeficitPrimitive.mul hq.continuous_deriv_one).intervalIntegrable 0 T
  have hqF : IntervalIntegrable (fun t => q t * (Real.exp t - Chebyshev.psi (Real.exp t))) volume 0 T :=
    hf.continuousOn_mul hq.continuous.continuousOn
  unfold ccmPrimeDeficitAction ccmPrimeDeficitLagrangian ccmPrimeDeficitForceAction ccmPrimeDeficitPotential
  simp only [neg_mul, sub_neg_eq_add]
  rw [intervalIntegral.integral_sub hk hDv, intervalIntegral.integral_add hk hqF]
  nlinarith only [hparts]

/-- Position translation is a symmetry of the force action up to its exact arithmetic boundary term. -/
theorem ccmPrimeDeficitForceAction_position_translation (q : ℝ → ℝ)
    (hq : ContDiff ℝ 1 q) (T c : ℝ) :
    ccmPrimeDeficitForceAction (fun t => q t + c) T =
      ccmPrimeDeficitForceAction q T + c * ccmLogChebyshevDeficitPrimitive T := by
  have h := ccmPrimeDeficitAction_position_translation q 0 T c
  rw [ccmPrimeDeficitAction_eq_forceAction_sub_boundary _ (hq.add contDiff_const),
    ccmPrimeDeficitAction_eq_forceAction_sub_boundary q hq] at h
  nlinarith only [h]

theorem contDiff_ccmPrimeDeficitTrajectory (q₀ p : ℝ) :
    ContDiff ℝ 1 (ccmPrimeDeficitTrajectory q₀ p) := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun t => (hasDerivAt_ccmPrimeDeficitTrajectory q₀ p t).differentiableAt
  · have hvel : deriv (ccmPrimeDeficitTrajectory q₀ p) =
        fun t => p + ccmLogChebyshevDeficitPrimitive t :=
      funext fun t => (hasDerivAt_ccmPrimeDeficitTrajectory q₀ p t).deriv
    rw [hvel]
    exact continuous_const.add continuous_ccmLogChebyshevDeficitPrimitive

/-- The constructed physical trajectories realize the boundary symmetry and conserved charge. -/
theorem ccmPrimeDeficitTrajectory_force_noether (q₀ p : ℝ) :
    (∀ T c : ℝ,
      ccmPrimeDeficitForceAction (fun t => ccmPrimeDeficitTrajectory q₀ p t + c) T =
        ccmPrimeDeficitForceAction (ccmPrimeDeficitTrajectory q₀ p) T +
          c * ccmLogChebyshevDeficitPrimitive T) ∧
    (∀ t : ℝ, deriv (ccmPrimeDeficitTrajectory q₀ p) t - ccmLogChebyshevDeficitPrimitive t = p) ∧
    (∀ᵐ t : ℝ ∂volume, deriv (deriv (ccmPrimeDeficitTrajectory q₀ p)) t =
      Real.exp t - Chebyshev.psi (Real.exp t)) := by
  refine ⟨ccmPrimeDeficitForceAction_position_translation _ (contDiff_ccmPrimeDeficitTrajectory q₀ p),
    ?_, ?_⟩
  · intro t
    rw [(hasDerivAt_ccmPrimeDeficitTrajectory q₀ p t).deriv]
    ring
  · filter_upwards [ccmPrimeDeficitTrajectory_newton_ae q₀ p] with t ht
    simpa only [ccmPrimeDeficitPotential_force] using ht

end RHTower
