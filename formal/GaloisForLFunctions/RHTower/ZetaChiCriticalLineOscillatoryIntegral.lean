import GaloisForLFunctions.RHTower.ZetaChiHardyPhase
import GaloisForLFunctions.RHTower.TrigammaVerticalLowerBound
import GaloisForLFunctions.RHTower.HardyPhaseCellCancellation
import GaloisForLFunctions.RHTower.VanDerCorputSecond

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exact real phase of a critical-line chi factor twisted by one Dirichlet frequency. -/
def zetaChiCriticalTwistPhase (ω t : ℝ) : ℝ :=
  ω * t - 2 * gammaHardyTheta t

theorem hasDerivAt_zetaChiCriticalTwistPhase (ω t : ℝ) :
    HasDerivAt (zetaChiCriticalTwistPhase ω)
      (ω - 2 * gammaHardyPhaseRate t) t := by
  unfold zetaChiCriticalTwistPhase
  have h := ((hasDerivAt_id t).const_mul ω).sub
    ((hasDerivAt_gammaHardyTheta t).const_mul 2)
  change HasDerivAt (fun u : ℝ => ω * u - 2 * gammaHardyTheta u)
    (ω * 1 - 2 * gammaHardyPhaseRate t) t at h
  simpa using h

theorem hasDerivAt_zetaChiCriticalTwistRate (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => ω - 2 * gammaHardyPhaseRate u)
      (-2 * deriv gammaHardyPhaseRate t) t := by
  have hr : HasDerivAt gammaHardyPhaseRate
      (deriv gammaHardyPhaseRate t) t :=
    (hasDerivAt_gammaHardyPhaseRate t).congr_deriv
      (deriv_gammaHardyPhaseRate t).symm
  have h := (hasDerivAt_const t ω).sub (hr.const_mul 2)
  change HasDerivAt (fun u : ℝ => ω - 2 * gammaHardyPhaseRate u)
    (0 - 2 * deriv gammaHardyPhaseRate t) t at h
  simpa using h

theorem zetaChi_line_mul_exp_eq_exp_twistPhase (ω t : ℝ) :
    zetaChi (linePt t) * Complex.exp ((((ω * t : ℝ) : ℂ)) * I) =
      Complex.exp (((zetaChiCriticalTwistPhase ω t : ℝ) : ℂ) * I) := by
  rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_add]
  congr 1
  unfold zetaChiCriticalTwistPhase
  push_cast
  ring

/-- Uniform stationary-phase bound from a dyadic block's left endpoint to any point in the block. -/
theorem norm_integral_zetaChi_line_mul_exp_to_le
    {T B : ℝ} (hT : 4 ≤ T) (hTB : T ≤ B) (hB : B ≤ 2 * T) (ω : ℝ) :
    ‖∫ t in T..B,
        zetaChi (linePt t) * Complex.exp ((((ω * t : ℝ) : ℂ)) * I)‖ ≤
      6 / Real.sqrt (1 / (100 * T)) := by
  have hTpos : 0 < T := by linarith
  have hlam : 0 < 1 / (100 * T) := by positivity
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChi_line_mul_exp_eq_exp_twistPhase ω t)]
  apply norm_integral_cexp_secondDeriv_neg hTB hlam
      (g' := fun t => ω - 2 * gammaHardyPhaseRate t)
      (g'' := fun t => -2 * deriv gammaHardyPhaseRate t)
  · intro t ht
    exact hasDerivAt_zetaChiCriticalTwistPhase ω t
  · intro t ht
    exact hasDerivAt_zetaChiCriticalTwistRate ω t
  · have hc : Continuous (fun t : ℝ =>
        -(2 * deriv gammaHardyPhaseRate t)) :=
      (continuous_const.mul continuous_deriv_gammaHardyPhaseRate).neg
    simpa only [neg_mul] using hc.continuousOn
  · intro t ht
    have htIcc : t ∈ Set.Icc T B := by
      rwa [Set.uIcc_of_le hTB] at ht
    have htpos : 0 < t := hTpos.trans_le htIcc.1
    have hcurv := deriv_gammaHardyPhaseRate_lower_bound (hT.trans htIcc.1)
    have htTop : t ≤ 2 * T := htIcc.2.trans hB
    have haux : 1 ≤ 2 * T / t := by
      exact (le_div_iff₀ htpos).2 (by simpa using htTop)
    have heq : 2 * (1 / (100 * t)) * (100 * T) = 2 * T / t := by
      field_simp [htpos.ne', hTpos.ne']
    have hfrac : 1 / (100 * T) ≤ 2 * (1 / (100 * t)) := by
      rw [div_le_iff₀ (by positivity : 0 < 100 * T)]
      rw [heq]
      exact haux
    have : 1 / (100 * T) ≤ 2 * deriv gammaHardyPhaseRate t :=
      hfrac.trans (mul_le_mul_of_nonneg_left hcurv (by norm_num))
    linarith

/-- Uniform stationary-phase bound for every critical-line chi-twisted Dirichlet frequency. -/
theorem norm_integral_zetaChi_line_mul_exp_le
    {T : ℝ} (hT : 4 ≤ T) (ω : ℝ) :
    ‖∫ t in T..(2 * T),
        zetaChi (linePt t) * Complex.exp ((((ω * t : ℝ) : ℂ)) * I)‖ ≤
      6 / Real.sqrt (1 / (100 * T)) := by
  exact norm_integral_zetaChi_line_mul_exp_to_le hT (by linarith) le_rfl ω

/-- Primitive of one critical-line chi-twisted frequency, anchored at a dyadic left endpoint. -/
def zetaChiCriticalTwistPrimitive (T ω t : ℝ) : ℂ :=
  ∫ u in T..t,
    zetaChi (linePt u) * Complex.exp (((ω * u : ℝ) : ℂ) * I)

theorem continuous_zetaChiCriticalTwistIntegrand (ω : ℝ) :
    Continuous (fun t : ℝ =>
      zetaChi (linePt t) * Complex.exp (((ω * t : ℝ) : ℂ) * I)) := by
  have heq : (fun t : ℝ =>
      zetaChi (linePt t) * Complex.exp (((ω * t : ℝ) : ℂ) * I)) =
      fun t : ℝ => Complex.exp (((zetaChiCriticalTwistPhase ω t : ℝ) : ℂ) * I) := by
    funext t
    exact zetaChi_line_mul_exp_eq_exp_twistPhase ω t
  rw [heq]
  have hphase : Continuous (zetaChiCriticalTwistPhase ω) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_zetaChiCriticalTwistPhase ω t).continuousAt
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp hphase).mul continuous_const)

theorem hasDerivAt_zetaChiCriticalTwistPrimitive (T ω t : ℝ) :
    HasDerivAt (zetaChiCriticalTwistPrimitive T ω)
      (zetaChi (linePt t) * Complex.exp (((ω * t : ℝ) : ℂ) * I)) t := by
  let f : ℝ → ℂ := fun u =>
    zetaChi (linePt u) * Complex.exp (((ω * u : ℝ) : ℂ) * I)
  have hf : Continuous f := continuous_zetaChiCriticalTwistIntegrand ω
  exact intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable T t)
    (hf.stronglyMeasurableAtFilter volume (nhds t)) hf.continuousAt

theorem zetaChiCriticalTwistPrimitive_left (T ω : ℝ) :
    zetaChiCriticalTwistPrimitive T ω T = 0 := by
  exact intervalIntegral.integral_same

/-- Every anchored primitive inside the dyadic block obeys the same stationary-phase bound. -/
theorem norm_zetaChiCriticalTwistPrimitive_le
    {T t : ℝ} (hT : 4 ≤ T) (ht : t ∈ Set.Icc T (2 * T)) (ω : ℝ) :
    ‖zetaChiCriticalTwistPrimitive T ω t‖ ≤
      6 / Real.sqrt (1 / (100 * T)) := by
  exact norm_integral_zetaChi_line_mul_exp_to_le hT ht.1 ht.2 ω

end

end RHTower
