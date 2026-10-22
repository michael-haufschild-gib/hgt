import GaloisForLFunctions.RHTower.CCM.CCMPrimePowerSquareRootControl

/-!
# Exact descent of the prime-power deficit to half logarithmic radius

Costa--Pereira separates the proper-power contribution into a complete copy
of psi at half radius and a positive remainder of cubic-root size. Integration
therefore gives a signed recurrence for the actual deficit, retaining its
smaller-scale value instead of replacing it by an absolute estimate.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

def ccmPrimePowerDescentRemainder (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) -
    Chebyshev.psi (Real.exp (t / 2))

private theorem descent_integrable (a b : ℝ) :
    IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) -
      Chebyshev.psi (Real.exp (t / 2))) volume a b := by
  have hm : Monotone (fun t : ℝ => Chebyshev.psi (Real.exp (t / 2))) := by
    intro s t hst
    exact Chebyshev.psi_mono (Real.exp_le_exp.mpr (by linarith))
  exact ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable.sub
    (Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable).sub hm.intervalIntegrable

/-- The discarded part has a sign and a global bound strictly below the
critical exponent. No unknown prime-error term occurs in this bound. -/
theorem ccmPrimePowerDescentRemainder_bounds {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ccmPrimePowerDescentRemainder T ∧
    ccmPrimePowerDescentRemainder T ≤ (Real.log 4 + 4) *
      (3 * (Real.exp (T / 3) - 1) + 5 * (Real.exp (T / 5) - 1)) := by
  constructor
  · exact intervalIntegral.integral_nonneg hT
      (fun t _ => (ccmProperPrimePowerSource_sub_half_bounds t).1)
  · have hi (n : ℝ) : IntervalIntegrable (fun t : ℝ => Real.exp (t / n)) volume 0 T := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h := intervalIntegral.integral_mono_on hT (descent_integrable 0 T)
      (((hi 3).add (hi 5)).const_mul (Real.log 4 + 4))
      (fun t _ => (ccmProperPrimePowerSource_sub_half_bounds t).2)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hi 3) (hi 5),
      intervalIntegral.integral_comp_div Real.exp (by norm_num : (3 : ℝ) ≠ 0),
      intervalIntegral.integral_comp_div Real.exp (by norm_num : (5 : ℝ) ≠ 0)] at h
    simp only [zero_div, smul_eq_mul, integral_exp, Real.exp_zero] at h
    exact h

/-- Higher prime powers are a full half-radius Chebyshev primitive plus a
positive cubic-root remainder. -/
theorem ccmProperPrimePowerPrimitive_eq_half_deficit (T : ℝ) :
    ccmProperPrimePowerPrimitive T =
      2 * (Real.exp (T / 2) - 1 - ccmLogChebyshevDeficitPrimitive (T / 2)) +
        ccmPrimePowerDescentRemainder T := by
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp t)) volume 0 (T / 2) :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable
  have hhalf : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp (t / 2))) volume 0 T := by
    have hm : Monotone (fun t : ℝ => Chebyshev.psi (Real.exp (t / 2))) := by
      intro s t hst
      exact Chebyshev.psi_mono (Real.exp_le_exp.mpr (by linarith))
    exact hm.intervalIntegrable
  have hproper : IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t) -
      Chebyshev.theta (Real.exp t)) volume 0 T :=
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable.sub
      (Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable
  rw [ccmPrimePowerDescentRemainder, intervalIntegral.integral_sub hproper hhalf,
    ccmLogChebyshevDeficitPrimitive,
    intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 (T / 2)) hi,
    integral_exp, Real.exp_zero,
    intervalIntegral.integral_comp_div (fun t => Chebyshev.psi (Real.exp t))
      (by norm_num : (2 : ℝ) ≠ 0), zero_div, smul_eq_mul]
  unfold ccmProperPrimePowerPrimitive
  ring

/-- Exact signed recurrence for the full remainder. The only uncontrolled
same-scale term is the prime-only deficit; the smaller-scale copy is explicit. -/
theorem ccmLogChebyshevDeficitPrimitive_scale_descent (T : ℝ) :
    ccmLogChebyshevDeficitPrimitive T = ccmLogThetaDeficitPrimitive T -
      2 * (Real.exp (T / 2) - 1) + 2 * ccmLogChebyshevDeficitPrimitive (T / 2) -
        ccmPrimePowerDescentRemainder T := by
  rw [ccmLogChebyshevDeficitPrimitive_eq_theta_sub_proper T,
    ccmProperPrimePowerPrimitive_eq_half_deficit]
  ring

/-- After critical normalization, the explicit remainder decays at least at
the sixth-exponential rate, with a still smaller fifth-power allowance. -/
theorem ccmPrimePowerDescentRemainder_critical_bound {T : ℝ} (hT : 0 ≤ T) :
    |Real.exp (-T / 2) * ccmPrimePowerDescentRemainder T| ≤
      (Real.log 4 + 4) * (3 * Real.exp (-T / 6) + 5 * Real.exp (-3 * T / 10)) := by
  obtain ⟨hR0, hR⟩ := ccmPrimePowerDescentRemainder_bounds hT
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hR0)]
  have hc : 0 ≤ Real.log 4 + 4 := by positivity
  have hR' : ccmPrimePowerDescentRemainder T ≤
      (Real.log 4 + 4) * (3 * Real.exp (T / 3) + 5 * Real.exp (T / 5)) := by
    nlinarith only [hR, hc]
  apply (mul_le_mul_of_nonneg_left hR' (Real.exp_pos (-T / 2)).le).trans_eq
  calc
    _ = (Real.log 4 + 4) *
        (3 * Real.exp (-T / 2 + T / 3) + 5 * Real.exp (-T / 2 + T / 5)) := by
      simp only [Real.exp_add]
      ring
    _ = _ := by
      rw [show -T / 2 + T / 3 = -T / 6 by ring,
        show -T / 2 + T / 5 = -3 * T / 10 by ring]

end RHTower
