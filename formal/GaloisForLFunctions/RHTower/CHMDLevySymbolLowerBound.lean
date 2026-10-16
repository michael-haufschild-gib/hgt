import GaloisForLFunctions.RHTower.CHMDArchimedeanLevyTranslateForm
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# Logarithmic growth of the archimedean Lévy symbol

The archimedean symbol `γ(r) = Re ψ(1/4 + ir/2) − log π` has the Lévy–Khintchine form
`γ(r) − γ(0) = 2∫_0^∞ ω(x)(1 − cos rx)dx ≥ 0`. The half-plane asymptotics of the digamma function
give `γ(r) ≥ log(|r|/2) − 3/2 − log π` for `|r| ≥ 4`, so the Lévy symbol `γ(r) − γ(0)` grows at
least logarithmically: the archimedean jump form controls a logarithmic Sobolev norm.
-/

open MeasureTheory Set Filter Topology Zeta23
noncomputable section
namespace RHTower.CHMDPolar

/-- The Lévy symbol of the archimedean place: `γ(r) − γ(0)`. -/
def levySymbol (r : ℝ) : ℝ := EF.gammaBracket r - EF.gammaBracket 0

theorem levySymbol_eq_integral (r : ℝ) :
    levySymbol r = 2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (r * x)) :=
  CHMDLightCone.gammaBracket_sub_zero_eq_integral r

theorem levySymbol_nonneg (r : ℝ) : 0 ≤ levySymbol r := by
  rw [levySymbol_eq_integral]
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioi fun x hx => ?_)
  exact mul_nonneg (archLevyDensity_pos hx).le (by linarith [Real.cos_le_one (r * x)])

/-- Digamma lower bound on the line `Re z = 1/4` at height `|r|/2 ≥ 2`. -/
theorem gammaBracket_ge_log {r : ℝ} (hr : 4 ≤ |r|) :
    Real.log (|r| / 2) - 3 / 2 - Real.log Real.pi ≤ EF.gammaBracket r := by
  rw [WeilHerglotz.gammaBracket_eq]
  set z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I with hz
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hzim : z.im = r / 2 := by simp [hz]
  have hre : 0 < z.re := by rw [hzre]; norm_num
  have hnorm : |r| / 2 ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_div, abs_two] at h
    exact h
  have hz2 : 2 ≤ ‖z‖ := le_trans (by linarith) hnorm
  have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hre hz2
  have hre' : (Complex.log z).re - ‖Complex.digamma z - Complex.log z‖ ≤ (Complex.digamma z).re := by
    have h1 := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
    rw [Complex.sub_re] at h1
    linarith [(abs_le.mp h1).1]
  rw [Complex.log_re] at hre'
  have h3 : 3 / ‖z‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz2
  have hlog : Real.log (|r| / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by linarith) hnorm
  linarith

/-- The additive constant of the logarithmic lower bound. -/
def levyConst : ℝ := 3 / 2 + Real.log Real.pi + EF.gammaBracket 0

/-- **Logarithmic growth of the Lévy symbol**: `γ(r) − γ(0) ≥ log(|r|/2) − levyConst` for `|r| ≥ 4`. -/
theorem levySymbol_ge_log {r : ℝ} (hr : 4 ≤ |r|) :
    Real.log (|r| / 2) - levyConst ≤ levySymbol r := by
  unfold levySymbol levyConst
  linarith [gammaBracket_ge_log hr]

/-- The lower bound on the tail `|r| ≥ T` is uniform. -/
theorem levySymbol_ge_log_of_le {T r : ℝ} (hT : 4 ≤ T) (hr : T ≤ |r|) :
    Real.log (T / 2) - levyConst ≤ levySymbol r := by
  have h := levySymbol_ge_log (le_trans hT hr)
  have hlog : Real.log (T / 2) ≤ Real.log (|r| / 2) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

theorem tendsto_log_half_sub_atTop : Tendsto (fun T : ℝ => Real.log (T / 2) - levyConst) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => T / 2) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  exact tendsto_atTop_add_const_right _ _ (Real.tendsto_log_atTop.comp h1)

end RHTower.CHMDPolar
