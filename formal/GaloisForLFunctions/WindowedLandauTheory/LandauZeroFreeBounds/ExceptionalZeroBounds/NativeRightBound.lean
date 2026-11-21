import GaloisForLFunctions.RHTower.DirichletLEulerLogarithmRightOfTheOneLine
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.XiResolventArchPrimeSplit
import GaloisForLFunctions.RHTower.ZetaPoleBoundExplicit
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! On the right half-plane the real zeta series majorizes the twisted logarithmic derivatives. -/

open Complex

namespace WindowedLandauTheory.ZeroFreeDirichlet

private theorem norm_zeta_logDeriv_real {x : ℝ} (hx : 1 < x) :
    ‖deriv riemannZeta x / riemannZeta x‖ = (-deriv riemannZeta x / riemannZeta x).re := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (x : ℂ)) (by simpa using hx)
  rw [neg_div, RHTower.lseries_vonMangoldt_ofReal hx] at h
  calc ‖deriv riemannZeta x / riemannZeta x‖ = ‖-(deriv riemannZeta x / riemannZeta x)‖ :=
      (norm_neg _).symm
    _ = RHTower.vonMangoldtWeightLogMoment 0 x := by
      rw [← h, Complex.norm_real, Real.norm_of_nonneg (RHTower.vonMangoldtWeightLogMoment_zero_nonneg x)]
    _ = (-deriv riemannZeta x / riemannZeta x).re := by
      rw [neg_div, ← h, Complex.ofReal_re]

theorem l_log_deriv_right : LLogDerivRight := by
  let C := max 1 RHTower.vonMangoldtSquareMass
  refine ⟨C, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro q _ χ s hs
  have h := RHTower.norm_logDeriv_LFunction_le χ hs s.im
  rw [Complex.re_add_im] at h
  unfold negLD
  rw [norm_neg]
  apply h.trans
  rcases le_or_gt s.re 2 with h₂ | h₂
  · rw [norm_zeta_logDeriv_real hs]
    exact (RHTower.neg_re_logDeriv_riemannZeta_real_le hs h₂).trans
      (add_le_add le_rfl (le_max_left _ _))
  · rw [← logDeriv_apply]
    exact (RHTower.norm_logDeriv_zeta_le_of_two_le_re (by simpa using h₂.le)).trans
      ((le_max_right _ _).trans (le_add_of_nonneg_left (by positivity)))

end WindowedLandauTheory.ZeroFreeDirichlet
