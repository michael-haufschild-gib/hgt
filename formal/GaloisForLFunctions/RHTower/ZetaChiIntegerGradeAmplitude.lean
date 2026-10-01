import GaloisForLFunctions.RHTower.ZetaChiIntegerGradeOscillation
import GaloisForLFunctions.RHTower.OscillatoryIntegralComplexAmplitude

open Complex MeasureTheory Topology
noncomputable section
namespace RHTower

/-- Integer chi grades, including inverse powers, have continuous exact
critical-line oscillatory carriers. -/
theorem continuous_zetaChiCriticalGradeIntegrand (k : ℤ) (ω : ℝ) :
    Continuous (fun t : ℝ =>
      zetaChi (linePt t) ^ k * Complex.exp (((ω * t : ℝ) : ℂ) * I)) := by
  have hg : Continuous (zetaChiCriticalGradePhase k ω) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (hasDerivAt_zetaChiCriticalGradePhase k ω t).continuousAt)
  have hc : Continuous (fun t : ℝ =>
      Complex.exp (((zetaChiCriticalGradePhase k ω t : ℝ) : ℂ) * I)) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hg).mul continuous_const)
  exact hc.congr (fun t => (zetaChi_line_zpow_mul_exp_eq_exp_gradePhase k ω t).symm)

/-- Every nonzero integer grade retains stationary cancellation under a
height-dependent complex amplitude, with its full derivative variation paid. -/
theorem norm_integral_complexAmplitude_mul_zetaChi_line_zpow_mul_exp_le
    {T a b : ℝ} (hT : 4 ≤ T) (ha : T ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * T)
    {k : ℤ} (hk : k ≠ 0) (ω : ℝ) {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hu' : IntervalIntegrable u' volume a b) :
    ‖∫ x in a..b, u x *
      (zetaChi (linePt x) ^ k * Complex.exp (((ω * x : ℝ) : ℂ) * I))‖ ≤
      (6 / Real.sqrt (|(k : ℝ)| / (100 * T))) *
        (‖u b‖ + ∫ x in a..b, ‖u' x‖) := by
  let f : ℝ → ℂ := fun x =>
    zetaChi (linePt x) ^ k * Complex.exp (((ω * x : ℝ) : ℂ) * I)
  let F : ℝ → ℂ := fun x => ∫ t in a..x, f t
  have hf : Continuous f := continuous_zetaChiCriticalGradeIntegrand k ω
  apply norm_integral_complexAmplitude_mul_deriv_le hab hu
    (u' := u') (v := F) (v' := f)
  · intro x _
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable a x)
      (hf.stronglyMeasurableAtFilter volume (nhds x)) hf.continuousAt
  · exact hu'
  · exact hf.intervalIntegrable a b
  · exact intervalIntegral.integral_same
  · intro x hx
    exact norm_integral_zetaChi_line_zpow_mul_exp_le hT ha hx.1 (hx.2.trans hb) hk ω

end RHTower
