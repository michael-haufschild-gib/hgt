import GaloisForLFunctions.RHTower.ZetaChiCompactHeightVariation
import GaloisForLFunctions.RHTower.CompactGaussianReflectedRowBounds
import GaloisForLFunctions.RHTower.HardyCarrier

open Complex
noncomputable section
namespace RHTower

/-- Actual reflected common row with its critical-line chi phase removed. -/
def compactGaussianSlowRow (s : ℂ) (N tau : ℝ) : ℂ :=
  reflectedCompactGaussianRow s N tau / zetaChi (linePt tau)

theorem compactGaussianSlowRow_eq_ratio (s : ℂ) (N tau : ℝ) :
    compactGaussianSlowRow s N tau =
      ((Real.sqrt N : ℂ) * (N : ℂ) ^ (s - 1)) *
        smoothAFEZetaChiShiftRatio (linePt tau) (s - (1 / 2 : ℂ)) := by
  have hshift : linePt tau + (s - (1 / 2 : ℂ)) = s + (tau : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  unfold compactGaussianSlowRow reflectedCompactGaussianRow smoothAFEZetaChiShiftRatio
  rw [hshift]
  ring

/-- Removing the critical chi phase preserves the actual row norm. -/
theorem norm_compactGaussianSlowRow (s : ℂ) (N tau : ℝ) :
    ‖compactGaussianSlowRow s N tau‖ = ‖reflectedCompactGaussianRow s N tau‖ := by
  rw [compactGaussianSlowRow, norm_div, norm_zetaChi_line, div_one]

/-- Exact height derivative after the critical chi phase is removed. -/
theorem hasDerivAt_compactGaussianSlowRow {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N tau : ℝ) :
    HasDerivAt (compactGaussianSlowRow s N)
      (I * compactGaussianSlowRow s N tau *
        (logDeriv zetaChi (s + (tau : ℂ) * I) - logDeriv zetaChi (linePt tau))) tau := by
  have hshift : linePt tau + (s - (1 / 2 : ℂ)) = s + (tau : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  have hG : Gammaℝ (1 - (linePt tau + (s - (1 / 2 : ℂ)))) ≠ 0 := by
    rw [hshift]
    apply Gammaℝ_ne_zero_of_re_pos
    simpa using sub_pos.mpr hs1
  have hchi : zetaChi (linePt tau + (s - (1 / 2 : ℂ))) ≠ 0 := by
    rw [hshift]
    exact zetaChi_ne_zero_of_mem_openStrip (by simpa using hs0) (by simpa using hs1)
  have hq := hasDerivAt_smoothAFEZetaChiShiftRatio_line_logDeriv hG hchi
  have hf : compactGaussianSlowRow s N = fun u =>
      ((Real.sqrt N : ℂ) * (N : ℂ) ^ (s - 1)) *
        smoothAFEZetaChiShiftRatio (linePt u) (s - (1 / 2 : ℂ)) := by
    funext u
    exact compactGaussianSlowRow_eq_ratio s N u
  have hh := hq.const_mul ((Real.sqrt N : ℂ) * (N : ℂ) ^ (s - 1))
  have he : ((Real.sqrt N : ℂ) * (N : ℂ) ^ (s - 1)) *
      (I * smoothAFEZetaChiShiftRatio (linePt tau) (s - (1 / 2 : ℂ)) *
        (logDeriv zetaChi (linePt tau + (s - (1 / 2 : ℂ))) - logDeriv zetaChi (linePt tau))) =
      I * compactGaussianSlowRow s N tau *
        (logDeriv zetaChi (s + (tau : ℂ) * I) - logDeriv zetaChi (linePt tau)) := by
    rw [compactGaussianSlowRow_eq_ratio, hshift]
    ring
  exact (hh.congr_deriv he).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => congrFun hf u))

/-- The actual row amplitude varies at conductor scale on every fixed right
strip compact, rather than at the critical chi phase's logarithmic speed. -/
theorem norm_deriv_compactGaussianSlowRow_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (N : ℝ) {tau : ℝ} (htau : 4 ≤ tau) (him : 2 * |s.im| ≤ tau) :
    ‖deriv (compactGaussianSlowRow s N) tau‖ ≤
      ‖reflectedCompactGaussianRow s N tau‖ * ((10 / tau) * ‖s - (1 / 2 : ℂ)‖) := by
  rw [(hasDerivAt_compactGaussianSlowRow hs0 hs1 N tau).deriv,
    norm_mul, norm_mul, norm_I, one_mul, norm_compactGaussianSlowRow]
  exact mul_le_mul_of_nonneg_left
    (norm_logDeriv_zetaChi_compact_shift_le hs0.le hs1.le htau him) (norm_nonneg _)

end RHTower
