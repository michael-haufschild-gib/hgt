import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitWeilFlux
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier

/-!
# The arithmetic boundary condition for the deficit flux

Mertens' theorem and the prime number theorem determine the weighted total
deficit exactly. They select the flux state with zero scaled boundary value
at infinity. The state consequently equals a convergent future convolution
of the actual incoming amplitude. Convergence is proved unconditionally;
no uniform critical-scale bound is inferred from this identity alone.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

/-- The total weighted deficit is gamma + 1, as a limit of actual finite
integrals. This is the boundary cancellation needed by the flux state. -/
theorem tendsto_integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t) atTop
        (nhds (Real.eulerMascheroniConstant + 1)) := by
  have hM : Tendsto (fun T : ℝ => T - mertensSum ⌊Real.exp T⌋₊) atTop
      (nhds Real.eulerMascheroniConstant) := by
    have h := (tendsto_real_sum_vonMangoldt_div_sub_log.comp Real.tendsto_exp_atTop).neg
    simpa only [Function.comp_def, Real.log_exp, ← mertensSum_eq_Icc_zero,
      neg_sub, neg_neg] using h
  have hP : Tendsto (fun T : ℝ => Real.exp (-T) * Chebyshev.psi (Real.exp T)) atTop
      (nhds 1) := by
    have h := (tendsto_chebyshevError_div.comp Real.tendsto_exp_atTop).add_const 1
    rw [zero_add] at h
    refine h.congr fun T => ?_
    simp only [Function.comp_def, chebyshevError, Real.exp_neg]
    field_simp
    ring
  have h := hM.add (hP.sub tendsto_ccmLogChebyshevDeficitPrimitive_scaled_zero)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive hT]
  ring

theorem tendsto_ccmPrimeDeficitFluxState_scaled_zero :
    Tendsto (fun T : ℝ => Real.exp (-T / 2) * ccmPrimeDeficitFluxState T)
      atTop (nhds 0) := by
  have h := tendsto_integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive.const_sub
    (Real.eulerMascheroniConstant + 1)
  rw [sub_self] at h
  refine h.congr fun T => ?_
  unfold ccmPrimeDeficitFluxState
  rw [← mul_assoc, ← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero, one_mul]

/-- The future convolution has a genuine limit fixed by the arithmetic
boundary condition. The exponential homogeneous solution is absent. -/
theorem tendsto_future_integral_ccmPrimeDeficitIncoming (T : ℝ) :
    Tendsto (fun U : ℝ => ∫ t in T..U,
      Real.exp (-(t - T) / 2) * ccmPrimeDeficitIncoming t) atTop
        (nhds (ccmPrimeDeficitFluxState T)) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t) * ccmLogChebyshevDeficitPrimitive t
  have hf : Continuous f :=
    (Real.continuous_exp.comp continuous_neg).mul continuous_ccmLogChebyshevDeficitPrimitive
  have h := (tendsto_integral_exp_neg_mul_ccmLogChebyshevDeficitPrimitive.sub_const
    (∫ t in (0 : ℝ)..T, f t)).const_mul (Real.exp (T / 2))
  change Tendsto _ atTop (nhds (ccmPrimeDeficitFluxState T)) at h
  refine h.congr fun U => ?_
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 T) (hf.intervalIntegrable T U)
  have hs : (∫ t in (0 : ℝ)..U, f t) - (∫ t in (0 : ℝ)..T, f t) =
      ∫ t in T..U, f t := by linarith only [ha]
  change Real.exp (T / 2) * ((∫ t in (0 : ℝ)..U, f t) - (∫ t in (0 : ℝ)..T, f t)) = _
  rw [hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [f, ccmPrimeDeficitIncoming]
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

end RHTower
