import GaloisForLFunctions.RHTower.CCM.CCMPoleLeadingCancellation

/-!
# Removing the higher-prime-power part of the signed deficit

The logarithmic integral of psi minus theta has an unconditional square-root
bound. Its square-root-normalized limit is exactly two. Thus higher prime
powers supply a controlled, nonzero bias at the critical scale. The remaining
signed integral involving theta is retained exactly; it is not bounded here.
-/

noncomputable section
open MeasureTheory Filter Set

namespace RHTower

/-- The contribution of all proper prime powers to the logarithmic primitive. -/
def ccmProperPrimePowerPrimitive (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t)

/-- The signed deficit containing prime entries only. -/
def ccmLogThetaDeficitPrimitive (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, Real.exp t - Chebyshev.theta (Real.exp t)

private theorem proper_integrable (a b : ℝ) :
    IntervalIntegrable (fun t => Chebyshev.psi (Real.exp t) -
      Chebyshev.theta (Real.exp t)) volume a b :=
  (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable.sub
    (Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable

/-- Exact signed separation: no absolute value is taken on the prime remainder. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_theta_sub_proper (T : ℝ) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmLogThetaDeficitPrimitive T - ccmProperPrimePowerPrimitive T := by
  have hi : IntervalIntegrable (fun t => Real.exp t - Chebyshev.theta (Real.exp t))
      volume 0 T := (Real.continuous_exp.intervalIntegrable 0 T).sub
        (Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable
  rw [ccmLogThetaDeficitPrimitive, ccmProperPrimePowerPrimitive,
    ← intervalIntegral.integral_sub hi (proper_integrable 0 T)]
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem ccmProperPrimePowerPrimitive_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ccmProperPrimePowerPrimitive T := by
  apply intervalIntegral.integral_nonneg hT
  intro t _
  exact sub_nonneg.mpr (Chebyshev.theta_le_psi _)

/-- All higher prime powers together have a global critical-scale envelope. -/
theorem exists_ccmProperPrimePowerPrimitive_squareRoot_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      ccmProperPrimePowerPrimitive T ≤ B * (Real.exp (T / 2) - 1) := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  refine ⟨2 * K, by positivity, fun T hT => ?_⟩
  have hb : ∀ t : ℝ, Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) ≤
      K * Real.exp (t / 2) := by
    intro t
    have hs : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring
    apply (hC _).trans
    rw [hs]
    exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
  have hi : IntervalIntegrable (fun t : ℝ => K * Real.exp (t / 2)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on hT (proper_integrable 0 T) hi
    (fun t _ => hb t)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    zero_div, smul_eq_mul, integral_exp, Real.exp_zero] at h
  exact h.trans_eq (by ring)

private theorem psi_half_scaled_tendsto :
    Tendsto (fun t : ℝ => Real.exp (-t / 2) * Chebyshev.psi (Real.exp (t / 2)))
      atTop (nhds 1) := by
  have hident (x : ℝ) : chebyshevPsiReal x = Chebyshev.psi x := by
    rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
    congr 1
    ext n
    simp
  have ht : Tendsto (fun t : ℝ => t / 2) atTop atTop := tendsto_id.atTop_div_const two_pos
  have h := tendsto_chebyshevPsiReal_div.comp (Real.tendsto_exp_atTop.comp ht)
  refine h.congr fun t => ?_
  simp only [Function.comp_def, hident, div_eq_mul_inv, ← Real.exp_neg]
  rw [neg_mul]
  ring

/-- Costa--Pereira inequalities isolate the square contribution with a
strictly smaller exponential remainder, retaining its sign. -/
theorem ccmProperPrimePowerSource_sub_half_bounds (t : ℝ) :
    0 ≤ Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) -
      Chebyshev.psi (Real.exp (t / 2)) ∧
    Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) -
      Chebyshev.psi (Real.exp (t / 2)) ≤
      (Real.log 4 + 4) * (Real.exp (t / 3) + Real.exp (t / 5)) := by
  have he (n : ℝ) : (Real.exp t) ^ n⁻¹ = Real.exp (t / n) := by
    rw [← Real.exp_mul, div_eq_mul_inv]
  have hlo := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi (Real.exp_pos t).le
  have hhi := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (Real.exp t)
  simp only [he] at hlo hhi
  constructor
  · linarith [Chebyshev.psi_nonneg (Real.exp (t / 3)),
      Chebyshev.psi_nonneg (Real.exp (t / 7))]
  · linarith [Chebyshev.psi_le_const_mul_self (Real.exp_pos (t / 3)).le,
      Chebyshev.psi_le_const_mul_self (Real.exp_pos (t / 5)).le]

theorem tendsto_ccmProperPrimePowerSource_scaled_one :
    Tendsto (fun t : ℝ => Real.exp (-t / 2) *
      (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t))) atTop (nhds 1) := by
  have hthird : Tendsto (fun t : ℝ => Real.exp (-(t / 6))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const (by norm_num))
  have hfifth : Tendsto (fun t : ℝ => Real.exp (-(3 * t / 10))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_div_const (by norm_num))
  have hbound : Tendsto (fun t : ℝ => (Real.log 4 + 4) *
      (Real.exp (-(t / 6)) + Real.exp (-(3 * t / 10)))) atTop (nhds 0) := by
    simpa only [add_zero, mul_zero] using (hthird.add hfifth).const_mul (Real.log 4 + 4)
  have hz : Tendsto (fun t : ℝ => Real.exp (-t / 2) *
      (Chebyshev.psi (Real.exp t) - Chebyshev.theta (Real.exp t) -
        Chebyshev.psi (Real.exp (t / 2)))) atTop (nhds 0) := by
    apply squeeze_zero (fun t => mul_nonneg (Real.exp_pos _).le
      (ccmProperPrimePowerSource_sub_half_bounds t).1) _ hbound
    intro t
    have h := mul_le_mul_of_nonneg_left (ccmProperPrimePowerSource_sub_half_bounds t).2
      (Real.exp_pos (-t / 2)).le
    apply h.trans_eq
    calc
      _ = (Real.log 4 + 4) *
          (Real.exp (-t / 2 + t / 3) + Real.exp (-t / 2 + t / 5)) := by
        simp only [Real.exp_add]
        ring
      _ = _ := by
        rw [show -t / 2 + t / 3 = -(t / 6) by ring,
          show -t / 2 + t / 5 = -(3 * t / 10) by ring]
  convert! hz.add psi_half_scaled_tendsto using 1
  · ext t
    ring
  · norm_num

/-- Integration preserves the critical-scale asymptotic, with coefficient two. -/
theorem tendsto_ccmProperPrimePowerPrimitive_scaled_two :
    Tendsto (fun T : ℝ => Real.exp (-T / 2) * ccmProperPrimePowerPrimitive T)
      atTop (nhds 2) := by
  let f : ℝ → ℝ := fun t => Chebyshev.psi (Real.exp t) -
    Chebyshev.theta (Real.exp t) - Real.exp (t / 2)
  have hf (a b : ℝ) : IntervalIntegrable f volume a b := by
    apply (proper_integrable a b).sub
    apply Continuous.intervalIntegrable
    fun_prop
  have hg (a b : ℝ) : IntervalIntegrable (fun t => f (2 * t)) volume a b := by
    convert! (hf (2 * a) (2 * b)).comp_mul_left (c := 2) using 1 <;> ring
  have hs : Tendsto (fun t => Real.exp (-t) * f (2 * t)) atTop (nhds 0) := by
    have h := (tendsto_ccmProperPrimePowerSource_scaled_one.comp
      (tendsto_id.const_mul_atTop two_pos)).sub_const 1
    simp only [sub_self] at h
    refine h.congr fun t => ?_
    dsimp only [Function.comp_def, f, id_eq]
    rw [show 2 * t / 2 = t by ring, show -(2 * t) / 2 = -t by ring]
    have hc : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith only [hc]
  have hint := (tendsto_exp_neg_mul_primitive_zero (fun t => f (2 * t)) hg hs).comp
    (tendsto_id.atTop_div_const two_pos)
  have hz : Tendsto (fun T => Real.exp (-T / 2) * ∫ t in (0 : ℝ)..T, f t)
      atTop (nhds 0) := by
    have h := hint.const_mul 2
    simp only [mul_zero] at h
    convert! h using 1
    ext T
    simp only [Function.comp_def, id_eq, intervalIntegral.integral_comp_mul_left _ (by norm_num : (2 : ℝ) ≠ 0),
      mul_zero, smul_eq_mul, show 2 * (T / 2) = T by ring]
    ring
  have he : Tendsto (fun T : ℝ => Real.exp (-T / 2)) atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const two_pos)
  have h := hz.add ((tendsto_const_nhds.sub he (a := (1 : ℝ))).const_mul 2)
  norm_num only [sub_zero, mul_one, zero_add] at h
  refine h.congr fun T => ?_
  dsimp only [f]
  rw [intervalIntegral.integral_sub (proper_integrable 0 T)
    (show IntervalIntegrable (fun t : ℝ => Real.exp (t / 2)) volume 0 T from by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_comp_div Real.exp (by norm_num : (2 : ℝ) ≠ 0),
    zero_div, smul_eq_mul, integral_exp, Real.exp_zero]
  change Real.exp (-T / 2) * (ccmProperPrimePowerPrimitive T -
    2 * (Real.exp (T / 2) - 1)) + 2 * (1 - Real.exp (-T / 2)) = _
  have hc : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  nlinarith only [hc]

end RHTower
