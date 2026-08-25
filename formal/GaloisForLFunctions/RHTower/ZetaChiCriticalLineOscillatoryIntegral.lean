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

/-- Uniform stationary-phase bound for every critical-line chi-twisted Dirichlet frequency. -/
theorem norm_integral_zetaChi_line_mul_exp_le
    {T : ℝ} (hT : 4 ≤ T) (ω : ℝ) :
    ‖∫ t in T..(2 * T),
        zetaChi (linePt t) * Complex.exp ((((ω * t : ℝ) : ℂ)) * I)‖ ≤
      6 / Real.sqrt (1 / (100 * T)) := by
  have hTpos : 0 < T := by linarith
  have hab : T ≤ 2 * T := by linarith
  have hlam : 0 < 1 / (100 * T) := by positivity
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChi_line_mul_exp_eq_exp_twistPhase ω t)]
  apply norm_integral_cexp_secondDeriv_neg hab hlam
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
    have htIcc : t ∈ Set.Icc T (2 * T) := by
      rwa [Set.uIcc_of_le hab] at ht
    have htpos : 0 < t := hTpos.trans_le htIcc.1
    have hcurv := deriv_gammaHardyPhaseRate_lower_bound (hT.trans htIcc.1)
    have haux : 1 ≤ 2 * T / t := by
      exact (le_div_iff₀ htpos).2 (by linarith [htIcc.2])
    have heq : 2 * (1 / (100 * t)) * (100 * T) = 2 * T / t := by
      field_simp [htpos.ne', hTpos.ne']
    have hfrac : 1 / (100 * T) ≤ 2 * (1 / (100 * t)) := by
      rw [div_le_iff₀ (by positivity : 0 < 100 * T)]
      rw [heq]
      exact haux
    have : 1 / (100 * T) ≤ 2 * deriv gammaHardyPhaseRate t :=
      hfrac.trans (mul_le_mul_of_nonneg_left hcurv (by norm_num))
    linarith

end

end RHTower
