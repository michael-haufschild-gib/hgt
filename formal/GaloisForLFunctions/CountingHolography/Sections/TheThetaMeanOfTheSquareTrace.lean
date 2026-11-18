import GaloisForLFunctions.CountingHolography.Sections.UnitMultiplicityOnThePoleHyperplane
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.KernelLogarithmicTrace

/-!
# The theta mean of the two long square lags

The same positive theta density cancels both unbounded translates in the
square degree. The integrals converge absolutely at every real center.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticScatteringHolography RenormalizedIntersectionTheory ArithmeticOrientationGeometry
open SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality SquareRootThreshold Zeta23 _root_.RHTower
open MeasureTheory Filter Topology

private abbrev coeff := evenCoeff zetaZeroConfig (boxSpline 1 3)

private theorem trace_series (t : ℝ) :
    2*realSplineTrace t = ∑' z : ℂ, (coeff z*Complex.exp (z*t)).re := by
  have h := configuration_shifted_trace_series temperedConfig_zetaZeroConfig 0 t
  rw [← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq] at h
  simpa only [Complex.ofReal_zero,sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using h

/-- The spline trace has an absolute exponential envelope on the full real line. -/
theorem realSplineTrace_strip_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ,
    |realSplineTrace t| ≤ A*Real.exp (1/2*|t|) := by
  refine ⟨(∑' z : ℂ, ‖coeff z‖)/2,div_nonneg (tsum_nonneg fun _ => norm_nonneg _) two_pos.le,fun t => ?_⟩
  have h := abs_cexp_series_le coeff id (summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig)
    (fun _ hz => abs_re_le_of_evenCoeff_ne_zero hz) t
  change |∑' z : ℂ, (coeff z*Complex.exp (z*t)).re| ≤ _ at h
  rw [← trace_series,abs_mul,abs_two] at h
  linarith only [h]

/-- The actual theta source kills the real spline trace at every translation.
Each spectral coefficient is multiplied by Xi at its own zero. -/
theorem thetaMean_realSplineTrace (t : ℝ) :
    Integrable (fun x => thetaCuspFullSource x*realSplineTrace (t+x)) ∧
      (∫ x, thetaCuspFullSource x*realSplineTrace (t+x)) = 0 := by
  have hm (s : ℝ) : Integrable fun x => Real.exp (s*|x|)*|thetaCuspFullSource x| := by
    simpa only [abs_of_pos (thetaCuspFullSource_pos _)] using
      HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource s
  obtain ⟨A,hA,hF⟩ := realSplineTrace_strip_bound
  refine ⟨integrable_kernel_of_strip_bound hA (by norm_num : (0:ℝ) ≤ 1/2)
    (Complex.continuous_re.comp continuous_splineSeries) contDiff_thetaCuspFullSource.continuous (hm _) hF t,?_⟩
  have hc := integral_kernel_cexp_tsum coeff id (by norm_num : (0:ℝ) ≤ 1/2)
    (summable_norm_evenCoeff_spline temperedConfig_zetaZeroConfig)
    (fun _ hz => abs_re_le_of_evenCoeff_ne_zero hz) contDiff_thetaCuspFullSource.continuous hm t
  have hzero (z : ℂ) : coeff z*(∫ x : ℝ, (thetaCuspFullSource x:ℂ)*Complex.exp (z*x)) = 0 := by
    by_cases hz : coeff z = 0
    · rw [hz,zero_mul]
    rw [← sourceTransform_I_mul_eq_laplace]
    change coeff z*sourceTransform thetaSourceC (Complex.I*z)=0
    rw [sourceTransform_thetaSourceC,XiC_I_mul_of_evenCoeff_ne_zero hz,mul_zero]
  simp only [id_eq,hzero,zero_mul,Complex.zero_re,tsum_zero,← trace_series] at hc
  simp_rw [mul_left_comm (thetaCuspFullSource _) 2,integral_const_mul] at hc
  linarith only [hc]

/-- The two long-range terms of the three-square Weil degree. -/
def squareLongTrace (u : ℝ) := 4*realSplineTrace u-2*realSplineTrace (u+Real.log 4)

theorem continuous_squareLongTrace : Continuous squareLongTrace := by
  have hc : Continuous realSplineTrace := Complex.continuous_re.comp continuous_splineSeries
  exact (continuous_const.mul hc).sub (continuous_const.mul (hc.comp (continuous_id.add continuous_const)))

/-- Both long lags obey the same strip exponent after a fixed translation. -/
theorem squareLongTrace_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, |squareLongTrace u| ≤ A*Real.exp (1/2*|u|) := by
  obtain ⟨B,hB,h⟩ := realSplineTrace_strip_bound
  let k := Real.exp (1/2*|Real.log 4|)
  refine ⟨4*B+2*B*k,by dsimp only [k]; positivity,fun u => ?_⟩
  have h₁ := h u
  have h₂ := (h (u+Real.log 4)).trans (mul_le_mul_of_nonneg_left
    (SurfaceOfSpecZ.ScaleLocality.exp_abs_add_le (by norm_num : (0:ℝ) ≤ 1/2) u (Real.log 4)) hB)
  have hh := abs_sub_le (4*realSplineTrace u) 0 (2*realSplineTrace (u+Real.log 4))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul] at hh
  norm_num at hh
  dsimp only [squareLongTrace,k]
  linarith only [hh,h₁,h₂]

/-- The complete long-range term has zero theta mean at every center. -/
theorem thetaMean_squareLongTrace (T : ℝ) :
    Integrable (fun x => thetaCuspFullSource x*squareLongTrace (T+x)) ∧ (∫ x, thetaCuspFullSource x*squareLongTrace (T+x))=0 := by
  obtain ⟨h₁,e₁⟩ := thetaMean_realSplineTrace T
  obtain ⟨h₂,e₂⟩ := thetaMean_realSplineTrace (T+Real.log 4)
  have he (x : ℝ) : thetaCuspFullSource x*squareLongTrace (T+x)=
      4*(thetaCuspFullSource x*realSplineTrace (T+x))-2*(thetaCuspFullSource x*realSplineTrace ((T+Real.log 4)+x)) := by
    unfold squareLongTrace
    rw [show T+x+Real.log 4=T+Real.log 4+x by ring]
    ring
  simp_rw [he]
  refine ⟨(h₁.const_mul 4).sub (h₂.const_mul 2),?_⟩
  rw [integral_sub (h₁.const_mul 4) (h₂.const_mul 2),integral_const_mul,integral_const_mul,e₁,e₂]
  ring

#print axioms thetaMean_realSplineTrace
#print axioms thetaMean_squareLongTrace

end GaloisForLFunctions.CountingHolography.Sections
