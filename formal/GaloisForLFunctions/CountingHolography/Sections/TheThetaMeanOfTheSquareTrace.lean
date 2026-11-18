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

#print axioms thetaMean_realSplineTrace

end GaloisForLFunctions.CountingHolography.Sections
