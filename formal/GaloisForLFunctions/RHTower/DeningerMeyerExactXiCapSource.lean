import GaloisForLFunctions.RHTower.DeningerMeyerNativeClockBoundaryDefect
import GaloisForLFunctions.RHTower.PrimeRotationXiSourceTransport

/-!
# An actual global cap source for the entire Xi function

The fixed polynomial-Gaussian Meyer cap test, scaled by `4*pi^2`, has
literal Poisson boundary Mellin transform exactly Xi on the whole plane.
Its negative Euler orbit produces every polynomial multiple of Xi. The
meromorphic Xi clock gauge is therefore the ratio of actual boundary
transforms, not an independently prescribed divisor model.
-/

open Complex Filter Topology
open scoped SchwartzMap
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

private theorem fixedBoundaryMellin_scaled_eq_xi_of_re_gt_one {s : ℂ} (hs : 1 < s.re) :
    (4 * (Real.pi : ℂ)^2) * deningerMeyerFixedBoundaryMellin s = xi s := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; simp [h] at hs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfun : (((meyerPoissonTestSource : DeningerMeyerCap) : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      fun x : ℝ => ((meyerPoissonTest x : ℝ) : ℂ) := funext meyerPoissonTestSchwartz_apply
  change (4 * (Real.pi : ℂ)^2) *
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM meyerPoissonTestSource) s = _
  rw [deningerMeyerStrongLogMellin_boundary_eq_zeta_mul_mellin meyerPoissonTestSource hs,
    hfun, mellin_meyerPoissonTest (by linarith : -2 < s.re)]
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hz : completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero h0]
    field_simp
  have hGamma : Complex.Gamma ((s+2)/2) = (s/2) * Complex.Gamma (s/2) := by
    rw [show (s+2)/2 = s/2+1 by ring, Complex.Gamma_add_one _ (div_ne_zero h0 two_ne_zero)]
  have hpow : (Real.pi : ℂ)^(-s/2) = (Real.pi : ℂ)^(-(s+4)/2) * (Real.pi : ℂ)^2 := by
    rw [show (-s/2 : ℂ) = (-(s+4)/2)+1+1 by ring,
      Complex.cpow_add _ _ hpi, Complex.cpow_add _ _ hpi, Complex.cpow_one]
    ring
  rw [xi_eq_half_mul h0 h1, hz, Complex.Gammaℝ_def, hGamma, hpow]
  ring

/-- The exact global Xi factor is already a literal Poisson boundary transform. -/
theorem deningerMeyerFixedBoundaryMellin_scaled_eq_xi (s : ℂ) :
    (4 * (Real.pi : ℂ)^2) * deningerMeyerFixedBoundaryMellin s = xi s := by
  have ha : AnalyticOnNhd ℂ
      (fun z => (4 * (Real.pi : ℂ)^2) * deningerMeyerFixedBoundaryMellin z) Set.univ :=
    analyticOnNhd_const.mul deningerMeyerFixedBoundaryMellin_analytic
  have he : (fun z => (4 * (Real.pi : ℂ)^2) * deningerMeyerFixedBoundaryMellin z) =ᶠ[𝓝 (2 : ℂ)] xi := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact fixedBoundaryMellin_scaled_eq_xi_of_re_gt_one hz
  exact congrFun (ha.eq_of_eventuallyEq xi_analyticOnNhd_univ he) s

/-- One fixed actual Meyer cap element with exact Xi boundary transform. -/
def deningerMeyerXiCapSource : DeningerMeyerCap :=
  (4 * (Real.pi : ℂ)^2) • meyerPoissonTestSource

theorem deningerMeyerXiCapSource_mellin (s : ℂ) :
    deningerMeyerBoundaryMellin deningerMeyerXiCapSource s = xi s := by
  change deningerMeyerBoundaryMellinLM s ((4 * (Real.pi : ℂ)^2) • meyerPoissonTestSource) = _
  rw [map_smul]
  exact deningerMeyerFixedBoundaryMellin_scaled_eq_xi s

/-- Every polynomial multiple of the entire Xi factor has an actual cap producer. -/
theorem deningerMeyerXiCapSource_polynomial_mellin (n : ℕ) (c : Fin n → ℂ) (s : ℂ) :
    deningerMeyerBoundaryMellin
      (deningerMeyerBoundaryPolynomialSource deningerMeyerXiCapSource n c) s =
      (windowLin 0 n c).eval s * xi s := by
  rw [deningerMeyerBoundaryPolynomialSource_mellin, deningerMeyerXiCapSource_mellin]

/-- Exact source provenance of the earlier meromorphic Xi clock correction. -/
theorem deningerMeyerXiCapSource_clock_gauge (a s : ℂ) :
    deningerMeyerBoundaryMellin deningerMeyerXiCapSource s /
      deningerMeyerStrongLogMellin
        (deningerMeyerLogClockModulation a (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource)) s =
      xiTranslationGauge a s := by
  rw [deningerMeyerLogClockModulation_mellin]
  change deningerMeyerBoundaryMellin deningerMeyerXiCapSource s /
    deningerMeyerBoundaryMellin deningerMeyerXiCapSource (s+a) = _
  rw [deningerMeyerXiCapSource_mellin, deningerMeyerXiCapSource_mellin]
  rfl

end
end RHTower
