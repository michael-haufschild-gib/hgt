import GaloisForLFunctions.RHTower.ZetaChiCriticalLineOscillatoryIntegral

open Complex MeasureTheory
noncomputable section
namespace RHTower

/-- Exact real phase of an integer chi grade and a Dirichlet frequency. -/
def zetaChiCriticalGradePhase (k : ℤ) (ω t : ℝ) : ℝ :=
  ω * t - 2 * (k : ℝ) * gammaHardyTheta t

theorem hasDerivAt_zetaChiCriticalGradePhase (k : ℤ) (ω t : ℝ) :
    HasDerivAt (zetaChiCriticalGradePhase k ω)
      (ω - 2 * (k : ℝ) * gammaHardyPhaseRate t) t := by
  unfold zetaChiCriticalGradePhase
  have h := ((hasDerivAt_id t).const_mul ω).sub
    ((hasDerivAt_gammaHardyTheta t).const_mul (2 * (k : ℝ)))
  change HasDerivAt (fun u : ℝ => ω * u - 2 * (k : ℝ) * gammaHardyTheta u)
    (ω * 1 - 2 * (k : ℝ) * gammaHardyPhaseRate t) t at h
  simpa only [mul_one] using h

theorem hasDerivAt_zetaChiCriticalGradeRate (k : ℤ) (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => ω - 2 * (k : ℝ) * gammaHardyPhaseRate u)
      (-2 * (k : ℝ) * deriv gammaHardyPhaseRate t) t := by
  have hr : HasDerivAt gammaHardyPhaseRate (deriv gammaHardyPhaseRate t) t :=
    (hasDerivAt_gammaHardyPhaseRate t).congr_deriv (deriv_gammaHardyPhaseRate t).symm
  have h := (hasDerivAt_const t ω).sub (hr.const_mul (2 * (k : ℝ)))
  change HasDerivAt (fun u : ℝ => ω - 2 * (k : ℝ) * gammaHardyPhaseRate u)
    (0 - 2 * (k : ℝ) * deriv gammaHardyPhaseRate t) t at h
  simpa only [zero_sub, neg_mul] using h

/-- The actual integer power, including inverse grades, is exactly its real
Hardy phase. -/
theorem zetaChi_line_zpow_mul_exp_eq_exp_gradePhase (k : ℤ) (ω t : ℝ) :
    zetaChi (linePt t) ^ k * Complex.exp (((ω * t : ℝ) : ℂ) * I) =
      Complex.exp (((zetaChiCriticalGradePhase k ω t : ℝ) : ℂ) * I) := by
  rw [zetaChi_line_eq_exp_neg_two_theta, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  unfold zetaChiCriticalGradePhase
  push_cast
  ring

/-- Every nonzero actual chi grade has uniform square-root cancellation on
all dyadic subintervals, independently of its Dirichlet frequency. -/
theorem norm_integral_zetaChi_line_zpow_mul_exp_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    {k : ℤ} (hk : k ≠ 0) (ω : ℝ) :
    ‖∫ t in a..b, zetaChi (linePt t) ^ k * Complex.exp (((ω * t : ℝ) : ℂ) * I)‖ ≤
      6 / Real.sqrt (|(k : ℝ)| / (100 * T)) := by
  have hTpos : 0 < T := by linarith
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkabs : 0 < |(k : ℝ)| := abs_pos.mpr hkR
  have hlam : 0 < |(k : ℝ)| / (100 * T) := by positivity
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChi_line_zpow_mul_exp_eq_exp_gradePhase k ω t)]
  have hg : ∀ t ∈ Set.uIcc a b, HasDerivAt (zetaChiCriticalGradePhase k ω)
      (ω - 2 * (k : ℝ) * gammaHardyPhaseRate t) t :=
    fun t _ => hasDerivAt_zetaChiCriticalGradePhase k ω t
  have hg' : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ => ω - 2 * (k : ℝ) * gammaHardyPhaseRate u)
        (-2 * (k : ℝ) * deriv gammaHardyPhaseRate t) t :=
    fun t _ => hasDerivAt_zetaChiCriticalGradeRate k ω t
  have hc : ContinuousOn (fun t : ℝ => -2 * (k : ℝ) * deriv gammaHardyPhaseRate t)
      (Set.uIcc a b) := (continuous_const.mul continuous_deriv_gammaHardyPhaseRate).continuousOn
  have hcurv : ∀ t ∈ Set.uIcc a b,
      |(k : ℝ)| / (100 * T) ≤ 2 * |(k : ℝ)| * deriv gammaHardyPhaseRate t := by
    intro t ht
    have htIcc : t ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at ht
    have htlo : T ≤ t := ha.trans htIcc.1
    have htpos : 0 < t := hTpos.trans_le htlo
    have htTop : t ≤ 2 * T := htIcc.2.trans hb
    have hrate := deriv_gammaHardyPhaseRate_lower_bound (hT.trans htlo)
    have haux : 1 ≤ 2 * T / t := (le_div_iff₀ htpos).mpr (by simpa using htTop)
    have heq : 2 * (1 / (100 * t)) * (100 * T) = 2 * T / t := by
      field_simp [htpos.ne', hTpos.ne']
    have hfrac : 1 / (100 * T) ≤ 2 * (1 / (100 * t)) := by
      rw [div_le_iff₀ (by positivity : 0 < 100 * T), heq]
      exact haux
    have hbase := hfrac.trans (mul_le_mul_of_nonneg_left hrate (by norm_num : (0 : ℝ) ≤ 2))
    have hmul := mul_le_mul_of_nonneg_left hbase hkabs.le
    calc
      _ = |(k : ℝ)| * (1 / (100 * T)) := by ring
      _ ≤ |(k : ℝ)| * (2 * deriv gammaHardyPhaseRate t) := hmul
      _ = _ := by ring
  rcases lt_or_gt_of_ne hkR with hkneg | hkpos
  · apply norm_integral_cexp_secondDeriv hab hlam hg hg' hc
    intro t ht
    have h := hcurv t ht
    rw [abs_of_neg hkneg] at h ⊢
    nlinarith
  · apply norm_integral_cexp_secondDeriv_neg hab hlam hg hg' hc
    intro t ht
    have h := hcurv t ht
    rw [abs_of_pos hkpos] at h ⊢
    nlinarith

end RHTower
