import GaloisForLFunctions.BiScaleUncertainty.ClampedExponentialRamp

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

theorem clampedRamp_exp_ratio_tail {ε a x : ℝ} (hε : 0 < ε) (ha : 1 ≤ a)
    (hx : Real.log (a*(1+ε)) ≤ x) : clampedRamp ε (Real.exp x/a) = 0 := by
  have ha0 : 0 < a := by linarith
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < a*(1+ε))] at he
  exact clampedRamp_eq_zero hε ((le_div_iff₀ ha0).2 (by nlinarith))

theorem integrableOn_ramp_exp {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    IntegrableOn (fun x => Real.exp x*clampedRamp ε (Real.exp x/a)) (Ici 0) := by
  have hc : Continuous (fun x => Real.exp x*clampedRamp ε (Real.exp x/a)) :=
    Real.continuous_exp.mul ((continuous_clampedRamp ε).comp (Real.continuous_exp.div_const a))
  apply (hc.integrableOn_Icc (a := 0) (b := Real.log (a*(1+ε)))).of_forall_sdiff_eq_zero measurableSet_Ici
  intro x hx
  have ht : Real.log (a*(1+ε)) ≤ x := by
    by_contra! hn
    exact hx.2 ⟨hx.1, hn.le⟩
  rw [clampedRamp_exp_ratio_tail hε ha ht, mul_zero]

theorem integrableOn_ramp_plain {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    IntegrableOn (fun x => clampedRamp ε (Real.exp x/a)) (Ici 0) := by
  have hc : Continuous (fun x => clampedRamp ε (Real.exp x/a)) :=
    (continuous_clampedRamp ε).comp (Real.continuous_exp.div_const a)
  apply (hc.integrableOn_Icc (a := 0) (b := Real.log (a*(1+ε)))).of_forall_sdiff_eq_zero measurableSet_Ici
  intro x hx
  apply clampedRamp_exp_ratio_tail hε ha
  by_contra! hn
  exact hx.2 ⟨hx.1, hn.le⟩

private theorem integral_ramp_exp_collar {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    (∫ x in Real.log a..Real.log (a*(1+ε)), Real.exp x*((1+ε-Real.exp x/a)/ε)) = ε*a/2 := by
  have ha0 : 0 < a := by linarith
  let P : ℝ → ℝ := fun x => ((1+ε)*Real.exp x-(Real.exp x)^2/(2*a))/ε
  have hd (x : ℝ) : HasDerivAt P (Real.exp x*((1+ε-Real.exp x/a)/ε)) x := by
    convert (((Real.hasDerivAt_exp x).const_mul (1+ε)).sub
      (((Real.hasDerivAt_exp x).pow 2).div_const (2*a))).div_const ε using 1 <;> first | rfl | ring
  have hc : Continuous (fun x => Real.exp x*((1+ε-Real.exp x/a)/ε)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  dsimp [P]
  rw [Real.exp_log ha0, Real.exp_log (by positivity : 0 < a*(1+ε))]
  field_simp
  ring

/-- The positive exponential branch of the ramp has an affine dilation moment. -/
theorem integral_ramp_exp {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    (∫ x in Ici (0 : ℝ), Real.exp x*clampedRamp ε (Real.exp x/a)) = a-1+ε*a/2 := by
  have ha0 : 0 < a := by linarith
  have hA : 0 < 1+ε := by linarith
  have hL0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have hL1 : Real.log a ≤ Real.log (a*(1+ε)) := by
    apply Real.log_le_log ha0
    nlinarith
  have hc : Continuous (fun x => Real.exp x*clampedRamp ε (Real.exp x/a)) :=
    Real.continuous_exp.mul ((continuous_clampedRamp ε).comp (Real.continuous_exp.div_const a))
  have hl : (∫ x in (0 : ℝ)..Real.log a, Real.exp x*clampedRamp ε (Real.exp x/a)) = a-1 := by
    have he : (∫ x in (0 : ℝ)..Real.log a, Real.exp x*clampedRamp ε (Real.exp x/a)) =
        ∫ x in (0 : ℝ)..Real.log a, Real.exp x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL0] at hx
      have ht := Real.exp_le_exp.mpr hx.2
      rw [Real.exp_log ha0] at ht
      dsimp only
      rw [clampedRamp_eq_one hε ((div_le_iff₀ ha0).2 (by simpa using ht)), mul_one]
    rw [he, integral_exp, Real.exp_log ha0, Real.exp_zero]
  have hr : (∫ x in Real.log a..Real.log (a*(1+ε)), Real.exp x*clampedRamp ε (Real.exp x/a)) = ε*a/2 := by
    rw [← integral_ramp_exp_collar hε ha]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hL1] at hx
    have hlo := Real.exp_le_exp.mpr hx.1
    have hhi := Real.exp_le_exp.mpr hx.2
    rw [Real.exp_log ha0] at hlo
    rw [Real.exp_log (mul_pos ha0 hA)] at hhi
    dsimp only
    rw [clampedRamp_eq_linear hε ((le_div_iff₀ ha0).2 (by simpa using hlo))
      ((div_le_iff₀ ha0).2 (by nlinarith))]
  have heq : (∫ x in Ici (0 : ℝ), Real.exp x*clampedRamp ε (Real.exp x/a)) =
      ∫ x in Icc 0 (Real.log (a*(1+ε))), Real.exp x*clampedRamp ε (Real.exp x/a) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici (fun _ hx => hx.1)
    intro x hx
    have ht : Real.log (a*(1+ε)) ≤ x := by
      by_contra! hn
      exact hx.2 ⟨hx.1, hn.le⟩
    rw [clampedRamp_exp_ratio_tail hε ha ht, mul_zero]
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hL0.trans hL1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (Real.log a))
      (hc.intervalIntegrable (Real.log a) (Real.log (a*(1+ε)))), hl, hr]

theorem integral_ramp_plain {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    (∫ x in Ici (0 : ℝ), clampedRamp ε (Real.exp x/a)) = Real.log a+rampLogCorrection ε := by
  have h := integral_ramp_polar hε ha
  have hf : (fun x => (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) =
      fun x => Real.exp x*clampedRamp ε (Real.exp x/a)+clampedRamp ε (Real.exp x/a) := by
    funext x
    ring
  rw [hf, integral_add (integrableOn_ramp_exp hε ha) (integrableOn_ramp_plain hε ha),
    integral_ramp_exp hε ha] at h
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
