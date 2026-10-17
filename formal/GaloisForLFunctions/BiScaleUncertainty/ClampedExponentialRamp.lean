import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact polar integration of a continuous one-sided exponential ramp. -/

open MeasureTheory Set
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

/-- A continuous replacement for the cutoff at one, with a right collar of width `ε`. -/
def clampedRamp (ε t : ℝ) : ℝ := min 1 (max 0 ((1+ε-t)/ε))

theorem clampedRamp_nonneg (ε t : ℝ) : 0 ≤ clampedRamp ε t := by
  unfold clampedRamp
  positivity

theorem clampedRamp_le_one (ε t : ℝ) : clampedRamp ε t ≤ 1 := by
  exact min_le_left _ _

theorem continuous_clampedRamp (ε : ℝ) : Continuous (clampedRamp ε) := by
  unfold clampedRamp
  fun_prop

theorem clampedRamp_eq_one {ε t : ℝ} (hε : 0 < ε) (ht : t ≤ 1) :
    clampedRamp ε t = 1 := by
  have h : 1 ≤ (1+ε-t)/ε := (le_div_iff₀ hε).2 (by linarith)
  simp [clampedRamp, max_eq_right (by linarith : 0 ≤ (1+ε-t)/ε),
    min_eq_left h]

theorem clampedRamp_eq_zero {ε t : ℝ} (hε : 0 < ε) (ht : 1+ε ≤ t) :
    clampedRamp ε t = 0 := by
  have h : (1+ε-t)/ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp [clampedRamp, max_eq_left h]

theorem clampedRamp_eq_linear {ε t : ℝ} (hε : 0 < ε)
    (hlo : 1 ≤ t) (hhi : t ≤ 1+ε) :
    clampedRamp ε t = (1+ε-t)/ε := by
  have h0 : 0 ≤ (1+ε-t)/ε := div_nonneg (by linarith) hε.le
  have h1 : (1+ε-t)/ε ≤ 1 := (div_le_iff₀ hε).2 (by linarith)
  simp [clampedRamp, max_eq_right h0, min_eq_right h1]

theorem antitone_clampedRamp {ε : ℝ} (hε : 0 < ε) : Antitone (clampedRamp ε) := by
  intro a b hab
  unfold clampedRamp
  gcongr

/-- The logarithmic polar contribution of the collar. -/
def rampLogCorrection (ε : ℝ) : ℝ := ((1+ε)*Real.log (1+ε)-ε)/ε



private theorem ramp_polar_tail {ε a x : ℝ} (hε : 0 < ε) (ha : 1 ≤ a)
    (hx : Real.log (a*(1+ε)) ≤ x) :
    (Real.exp x+1)*clampedRamp ε (Real.exp x/a) = 0 := by
  have ha0 : 0 < a := by linarith
  have he := Real.exp_le_exp.mpr hx
  rw [Real.exp_log (by positivity : 0 < a*(1+ε))] at he
  rw [clampedRamp_eq_zero hε ((le_div_iff₀ ha0).2 (by nlinarith)), mul_zero]

theorem integrableOn_ramp_polar {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    IntegrableOn (fun x => (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) (Ici 0) := by
  have hc : Continuous (fun x => (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) :=
    (Real.continuous_exp.add continuous_const).mul
      ((continuous_clampedRamp ε).comp (Real.continuous_exp.div_const a))
  apply (hc.integrableOn_Icc (a := 0) (b := Real.log (a*(1+ε)))).of_forall_sdiff_eq_zero
    measurableSet_Ici
  intro x hx
  apply ramp_polar_tail hε ha
  by_contra! hn
  exact hx.2 ⟨hx.1, hn.le⟩

private theorem integral_ramp_polar_collar {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    (∫ x in Real.log a..Real.log (a*(1+ε)),
      (Real.exp x+1)*((1+ε-Real.exp x/a)/ε)) = ε*a/2+rampLogCorrection ε := by
  have ha0 : 0 < a := by linarith
  let P : ℝ → ℝ := fun x =>
    (((1+ε)-1/a)*Real.exp x+(1+ε)*x-(Real.exp x)^2/(2*a))/ε
  have hd (x : ℝ) : HasDerivAt P
      ((Real.exp x+1)*((1+ε-Real.exp x/a)/ε)) x := by
    convert (((Real.hasDerivAt_exp x).const_mul ((1+ε)-1/a)).add
      ((hasDerivAt_id x).const_mul (1+ε))).sub
      (((Real.hasDerivAt_exp x).pow 2).div_const (2*a)) |>.div_const ε using 1 <;> first | rfl | ring
  have hc : Continuous (fun x => (Real.exp x+1)*((1+ε-Real.exp x/a)/ε)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable _ _)]
  dsimp [P]
  rw [Real.exp_log ha0, Real.exp_log (by positivity : 0 < a*(1+ε)),
    Real.log_mul ha0.ne' (by positivity : 1+ε ≠ 0)]
  unfold rampLogCorrection
  field_simp
  ring

/-- Exact integration retains both the exponential and logarithmic polar terms. -/
theorem integral_ramp_polar {ε a : ℝ} (hε : 0 < ε) (ha : 1 ≤ a) :
    (∫ x in Ici (0 : ℝ), (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) =
      a-1+Real.log a+ε*a/2+rampLogCorrection ε := by
  have ha0 : 0 < a := by linarith
  have hA : 0 < 1+ε := by linarith
  have hL0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have hL1 : Real.log a ≤ Real.log (a*(1+ε)) := by
    apply Real.log_le_log ha0
    nlinarith
  have hc : Continuous (fun x => (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) :=
    (Real.continuous_exp.add continuous_const).mul
      ((continuous_clampedRamp ε).comp (Real.continuous_exp.div_const a))
  have hleft : (∫ x in (0 : ℝ)..Real.log a,
      (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) = a-1+Real.log a := by
    have he : (∫ x in (0 : ℝ)..Real.log a,
        (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) =
        ∫ x in (0 : ℝ)..Real.log a, Real.exp x+1 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL0] at hx
      have ht := Real.exp_le_exp.mpr hx.2
      rw [Real.exp_log ha0] at ht
      dsimp only
      rw [clampedRamp_eq_one hε ((div_le_iff₀ ha0).2 (by simpa using ht)), mul_one]
    rw [he, intervalIntegral.integral_add (Real.continuous_exp.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), integral_exp, intervalIntegral.integral_const,
      Real.exp_log ha0]
    simp
  have hright : (∫ x in Real.log a..Real.log (a*(1+ε)),
      (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) = ε*a/2+rampLogCorrection ε := by
    rw [← integral_ramp_polar_collar hε ha]
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
  have heq : (∫ x in Ici (0 : ℝ), (Real.exp x+1)*clampedRamp ε (Real.exp x/a)) =
      ∫ x in Icc 0 (Real.log (a*(1+ε))),
        (Real.exp x+1)*clampedRamp ε (Real.exp x/a) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (fun _ hx => hx.1)
    intro x hx
    apply ramp_polar_tail hε ha
    by_contra! hn
    exact hx.2 ⟨hx.1, hn.le⟩
  rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hL0.trans hL1),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (0 : ℝ) (Real.log a))
      (hc.intervalIntegrable (Real.log a) (Real.log (a*(1+ε)))),
    hleft, hright]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
