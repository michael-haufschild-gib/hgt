import GaloisForLFunctions.RHTower.HardyPhaseIntegrableError
import GaloisForLFunctions.RHTower.ZetaChiCompactHeightVariation
import GaloisForLFunctions.RHTower.ZetaChiDisplacedCriticalRatioOscillatoryIntegral

open Complex
noncomputable section
namespace RHTower

/-- Full complex critical chi logarithmic slope, with its real conductor
term removed, has the integrable Hardy-phase error. -/
theorem norm_logDeriv_zetaChi_line_add_log_conductor_le {t : ℝ} (ht : 4 ≤ t) :
    ‖logDeriv zetaChi (linePt t) + (Real.log (t / (2 * Real.pi)) : ℂ)‖ ≤ 26 / t ^ 2 := by
  have he := logDeriv_zetaChi_displacedLinePt_zero_eq t
  have hpt : displacedLinePt 0 t = linePt t := by simp [displacedLinePt, linePt]
  rw [hpt] at he
  rw [he, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have hb := gammaHardyPhaseRate_sub_log_conductor_integrable_bound ht
  calc
    _ = 2 * |gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2| := by
      rw [show -2 * gammaHardyPhaseRate t + Real.log (t / (2 * Real.pi)) =
        -2 * (gammaHardyPhaseRate t - Real.log (t / (2 * Real.pi)) / 2) by ring,
        abs_mul]
      norm_num
    _ ≤ 2 * (13 / t ^ 2) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- The conductor term controls the full complex chi slope throughout
the compact shifted strip, without any zeta nonvanishing premise. -/
theorem norm_logDeriv_zetaChi_add_log_conductor_le {s : ℂ} {t : ℝ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : 4 ≤ t) (him : 2 * |s.im| ≤ t) :
    ‖logDeriv zetaChi (s + (t : ℂ) * I) + (Real.log (t / (2 * Real.pi)) : ℂ)‖ ≤
      (10 / t) * ‖s - (1 / 2 : ℂ)‖ + 26 / t ^ 2 := by
  calc
    _ = ‖(logDeriv zetaChi (s + (t : ℂ) * I) - logDeriv zetaChi (linePt t)) +
        (logDeriv zetaChi (linePt t) + (Real.log (t / (2 * Real.pi)) : ℂ))‖ := by
      congr 1
      ring
    _ ≤ ‖logDeriv zetaChi (s + (t : ℂ) * I) - logDeriv zetaChi (linePt t)‖ +
        ‖logDeriv zetaChi (linePt t) + (Real.log (t / (2 * Real.pi)) : ℂ)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_logDeriv_zetaChi_compact_shift_le hs0 hs1 ht him)
      (norm_logDeriv_zetaChi_line_add_log_conductor_le ht)

end RHTower
