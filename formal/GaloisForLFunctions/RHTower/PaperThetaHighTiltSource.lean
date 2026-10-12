import GaloisForLFunctions.RHTower.PaperThetaHighTiltFourier

/-! # Literal source Fourier reconstruction beyond the Hilbert-space domain

The coefficients retain the flat mode, its amplitude, and the original theta
CDF. Reconstruction returns to Lebesgue almost every point of the real source
coordinate, even though the admitted circle inputs are not square integrable.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource HedenmalmQuantile GaloisForLFunctions.HTGeometry FourierLLogL

theorem sourceLogCost_ne_top_iff_all (z : ℂ) :
    sourceLogCost z ≠ ∞ ↔ z = 0 ∨ XiC z = 0 ∨ 2 < z.im := by
  have hd : density z = logPowerDensity z 1 := by
    funext x
    simp only [density, logPowerDensity, NNReal.coe_one, Real.rpow_one]
  have hc : Continuous (density z) := by
    rw [hd]
    exact continuous_logPowerDensity z 1
  rw [sourceLogCost, lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable
    (Eventually.of_forall (density_nonneg z)), hd, integrable_logPowerDensity_iff]
  simp only [NNReal.coe_one, mul_one]

theorem sourceLogCost_eq_top_iff_all (z : ℂ) :
    sourceLogCost z = ∞ ↔ z ≠ 0 ∧ XiC z ≠ 0 ∧ z.im ≤ 2 := by
  simpa only [not_not, not_or, not_lt] using not_congr (sourceLogCost_ne_top_iff_all z)

theorem integrable_flatMode_highTilt (z : HighTiltPoint) : Integrable (flatMode z.val) := by
  have hh := (memLLogL_highTilt z).integrable
  rw [← measurePreserving_circle.map_eq,
    integrable_map_measure (measurable_circleMode_all z.val).aestronglyMeasurable
      Period.measurable_circle.aemeasurable] at hh
  have hp := hh.congr (circleMode_circle_ae z.val)
  refine ((integrable_unitInterval_iff_cdf hp.aestronglyMeasurable).mp hp).congr
    (Eventually.of_forall fun x => ?_)
  simp only [flatModePullback]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, Complex.real_smul]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  field_simp

theorem integrable_sourceCoeff_highTilt (z : HighTiltPoint) (k : ℤ) :
    Integrable (fun x => flatMode z.val x * Period.phase (-k) (thetaSource.cdfFun x)) := by
  have hu := integrable_flatMode_highTilt z
  refine hu.norm.mono' (hu.aestronglyMeasurable.mul
    ((Period.phase_cont (-k)).comp thetaSource.continuous_cdfFun).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Period.phase_unimod, mul_one]

/-- Entire-parameter coefficient transport uses the unchanged literal source coefficients. -/
theorem fourierCoeff_eq_sourceCoeff_all (z : ℂ) (k : ℤ) :
    fourierCoeff (circleMode z) k = sourceCoeff z k := by
  have hm : Measurable (fun x => circleMode z x * fourier (-k) x) :=
    (measurable_circleMode_all z).mul (fourier (-k)).continuous.measurable
  rw [fourierCoeff_eq_integral, ← measurePreserving_circle.map_eq,
    integral_map Period.measurable_circle.aemeasurable hm.aestronglyMeasurable]
  calc
    _ = ∫ t, flatModePullback z t * Period.phase (-k) t ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [circleMode_circle_ae z] with t ht
      rw [ht, Period.fourier_circle]
      simp only [Int.cast_neg]
    _ = ∫ x, thetaSource.normalized x •
        (flatModePullback z (thetaSource.cdfFun x) * Period.phase (-k) (thetaSource.cdfFun x)) := by
      apply integral_unitInterval_eq_cdf
      exact ((measurable_pullback_all z).mul (Period.phase_cont (-k)).measurable).aestronglyMeasurable
    _ = sourceCoeff z k := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [flatModePullback]
      rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, Complex.real_smul]
      have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
        exact_mod_cast (thetaSource.normalized_pos x).ne'
      field_simp

theorem sourcePartialSum_eq_all (z : ℂ) (N : ℕ) (t : ℝ) :
    sourcePartialSum z N t = symmetricPartialSum (circleMode z) N (Period.circle t) := by
  simp only [sourcePartialSum, symmetricPartialSum, fourierCoeff_eq_sourceCoeff_all,
    Period.fourier_circle]

theorem source_quantile_recovery_highTilt (z : HighTiltPoint) :
    ∀ᵐ t ∂unitIntervalMeasure, Tendsto (fun N : ℕ => sourcePartialSum z.val N t)
      atTop (𝓝 (flatModePullback z.val t)) := by
  filter_upwards [quantile_recovery_highTilt z] with t ht
  simpa only [sourcePartialSum_eq_all] using ht

/-- The original flat mode is recovered at Lebesgue almost every real coordinate. -/
theorem source_flat_recovery_highTilt (z : HighTiltPoint) :
    ∀ᵐ x : ℝ, Tendsto (fun N : ℕ =>
      (thetaSource.normalized x : ℂ) * sourcePartialSum z.val N (thetaSource.cdfFun x))
        atTop (𝓝 (flatMode z.val x)) := by
  have h := (measurePreserving_cdf_unitInterval thetaSource).quasiMeasurePreserving.ae
    (source_quantile_recovery_highTilt z)
  have h' : (fun x => Tendsto (fun N : ℕ => sourcePartialSum z.val N (thetaSource.cdfFun x))
      atTop (𝓝 (flatModePullback z.val (thetaSource.cdfFun x)))) =ᵐ[thetaSource.law]
        (fun _ => True) := h.mono fun _ hx => propext (iff_true_intro hx)
  filter_upwards [thetaSource.law_ae_eq.mp h'] with x hx
  have ht := (of_eq_true hx).const_mul (thetaSource.normalized x : ℂ)
  convert ht using 1
  simp only [flatModePullback]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  field_simp

end RHTower.PaperThetaEndpoint
