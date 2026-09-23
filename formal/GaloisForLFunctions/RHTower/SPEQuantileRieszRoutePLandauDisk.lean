import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceSpectralPole
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap

open Complex Filter Topology

noncomputable section

namespace RHTower

private theorem zetaResidueUnit_ne_zero_low_height {s : ℂ}
    (hre : 0 < s.re) (him : |s.im| ≤ 4) : zetaResidueUnit s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst s
    simp [zetaResidueUnit]
  · intro hunit
    have hzeta : riemannZeta s = 0 := by
      simpa [zetaResidueUnit, hs1, sub_ne_zero.mpr hs1] using hunit
    have hxi : xi s = 0 := (xi_eq_zero_iff hre hs1).2 hzeta
    exact xi_ne_zero_of_abs_im_le_four him hxi

theorem analyticAt_routePSourceLaplaceContinuation_of_low_height
    {z : ℂ} (hre : -(1 / 2 : ℝ) < z.re) (him : |z.im| ≤ 4) :
    AnalyticAt ℂ routePSourceLaplaceContinuation z := by
  have hsre : 0 < (z + 1 / 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hsim : |(z + 1 / 2).im| ≤ 4 := by simpa using him
  have hU : zetaResidueUnit (z + 1 / 2) ≠ 0 :=
    zetaResidueUnit_ne_zero_low_height hsre hsim
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z := by fun_prop
  have hlog : AnalyticAt ℂ
      (fun w : ℂ => logDeriv zetaResidueUnit (w + 1 / 2)) z :=
    AnalyticAt.comp (f := fun w : ℂ => w + 1 / 2)
      (analyticAt_logDeriv_zetaResidueUnit hU) hshift
  have hhalf : z + 1 / 2 ≠ 0 := ne_zero_of_re_pos hsre
  have hone : z + 1 ≠ 0 := by
    apply ne_zero_of_re_pos
    norm_num [Complex.add_re]
    linarith
  have hE : AnalyticAt ℂ criticalNormalizedChebyshevErrorContinuation z := by
    change AnalyticAt ℂ
      (fun w : ℂ => -(logDeriv zetaResidueUnit (w + 1 / 2) + 1) / (w + 1 / 2)) z
    exact (hlog.add analyticAt_const).neg.div hshift hhalf
  change AnalyticAt ℂ
    (fun w : ℂ => (criticalNormalizedChebyshevErrorContinuation w - 2 / 3) / (w + 1)) z
  exact (hE.sub analyticAt_const).div (analyticAt_id.add analyticAt_const) hone

theorem analyticOnNhd_routePSourceLaplaceContinuation_closedBall_one :
    AnalyticOnNhd ℂ routePSourceLaplaceContinuation
      (Metric.closedBall (1 : ℂ) (5 / 4 : ℝ)) := by
  intro z hz
  have hnorm : ‖z - 1‖ ≤ (5 / 4 : ℝ) := by
    simpa [Complex.dist_eq] using (Metric.mem_closedBall.mp hz)
  have hreBound : |z.re - 1| ≤ ‖z - 1‖ := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (Complex.abs_re_le_norm (z - 1))
  have himBound : |z.im| ≤ ‖z - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using
      (Complex.abs_im_le_norm (z - 1))
  have hre : -(1 / 2 : ℝ) < z.re := by
    have hlo := (abs_le.mp (hreBound.trans hnorm)).1
    linarith
  have him : |z.im| ≤ 4 := by
    linarith [himBound, hnorm]
  exact analyticAt_routePSourceLaplaceContinuation_of_low_height hre him

end RHTower
