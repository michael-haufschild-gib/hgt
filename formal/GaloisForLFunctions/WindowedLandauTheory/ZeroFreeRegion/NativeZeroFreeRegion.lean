import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.WindowedLandauTheory.ZeroFreeRegion.Statement

/-! The corpus's logarithmic region, expressed using the height shift by two. -/

namespace WindowedLandauTheory.ZF

theorem zeroFreeRegion : ZeroFreeRegion := by
  refine ⟨1 / 232, by norm_num, fun s _ hs => ?_⟩
  let a := |s.im|
  have ha : 0 ≤ a := abs_nonneg _
  have h2 : Real.log 2 ≤ Real.log (a + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hlog : 0 < Real.log (a + 2) := (Real.log_pos (by norm_num)).trans_le h2
  have hlog4 : 0 < Real.log (a + 4) := Real.log_pos (by linarith)
  have hsmall : (1 / 232 : ℝ) / Real.log (a + 2) < 1 := by
    rw [div_lt_one hlog]
    linarith only [Real.log_two_gt_d9, h2]
  have hpow : a + 4 ≤ (a + 2) ^ 2 := by nlinarith only [ha, sq_nonneg a]
  have hlogs := Real.log_le_log (show 0 < a + 4 by linarith) hpow
  rw [Real.log_pow] at hlogs
  have hcmp : (1 / 232 : ℝ) / Real.log (a + 2) < 1 / 58 / Real.log (a + 4) := by
    rw [div_lt_div_iff₀ hlog hlog4]
    norm_num at hlogs ⊢
    linarith only [hlogs, hlog]
  apply RHTower.riemannZeta_ne_zero_of_lt_re
  · linarith only [hsmall, hs]
  · linarith only [hcmp, hs]

end WindowedLandauTheory.ZF
