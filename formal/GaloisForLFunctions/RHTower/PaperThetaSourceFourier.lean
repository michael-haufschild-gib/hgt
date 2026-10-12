import GaloisForLFunctions.RHTower.PaperThetaFourierEndpoint

/-! # Literal source coefficients and almost-everywhere mode reconstruction

The coefficient integrals use the flat mode and the actual theta CDF. The CDF
Jacobian cancels the original quantile denominator exactly. At every Xi zero,
the full symmetric sums reconstruct the flat mode in Lebesgue almost every point.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry FourierLLogL HedenmalmThetaSource HedenmalmQuantile

namespace PaperThetaEndpoint

abbrev StripPoint := {z : ℂ // |z.im| < 1}

/-- Extended logarithmic cost distinguishes nonintegrability from a zero Bochner integral. -/
def sourceLogCost (z : ℂ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (density z x)

theorem sourceLogCost_ne_top_iff (z : Point) : sourceLogCost z.val ≠ ∞ ↔ XiC z.val = 0 := by
  rw [sourceLogCost, lintegral_ofReal_ne_top_iff_integrable
    (continuous_density z).aestronglyMeasurable
      (Eventually.of_forall (density_nonneg z.val)), integrable_density_iff]

theorem sourceLogCost_eq_top_iff (z : Point) : sourceLogCost z.val = ∞ ↔ XiC z.val ≠ 0 := by
  simpa only [not_not] using (not_congr (sourceLogCost_ne_top_iff z))

/-- The Fourier coefficient written entirely in the original flat source coordinate. -/
def sourceCoeff (z : ℂ) (k : ℤ) : ℂ :=
  ∫ x, flatMode z x * Period.phase (-k) (thetaSource.cdfFun x)

private theorem integrable_coefficient {z : ℂ} (hu : Integrable (flatMode z)) (k : ℤ) :
    Integrable (fun x => flatMode z x * Period.phase (-k) (thetaSource.cdfFun x)) := by
  refine hu.norm.mono' (hu.aestronglyMeasurable.mul
    ((Period.phase_cont (-k)).comp thetaSource.continuous_cdfFun).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Period.phase_unimod, mul_one]

theorem integrable_sourceCoeff_integrand (z : Point) (k : ℤ) :
    Integrable (fun x => flatMode z.val x * Period.phase (-k) (thetaSource.cdfFun x)) :=
  integrable_coefficient (integrable_flatMode z.property.1 z.property.2) k

theorem integrable_divisor_flatMode (z : DivisorPoint) : Integrable (flatMode z.val) := by
  have hp : Integrable (flatModePullback z.val) unitIntervalMeasure :=
    ((Lp.memLp (portEigenmode z.val)).integrable (by norm_num)).congr
      (portEigenmode_ae_flatModePullback z.property)
  refine ((integrable_unitInterval_iff_cdf hp.aestronglyMeasurable).1 hp).congr
    (Eventually.of_forall fun x => ?_)
  simp only [flatModePullback]
  rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, Complex.real_smul]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  field_simp

theorem integrable_divisor_sourceCoeff_integrand (z : DivisorPoint) (k : ℤ) :
    Integrable (fun x => flatMode z.val x * Period.phase (-k) (thetaSource.cdfFun x)) :=
  integrable_coefficient (integrable_divisor_flatMode z) k

theorem fourierCoeff_eq_sourceCoeff (z : StripPoint) (k : ℤ) :
    fourierCoeff (circleMode z.val) k = sourceCoeff z.val k := by
  have hm : Measurable (fun x => circleMode z.val x * fourier (-k) x) :=
    (measurable_circleMode_of_strip z.property).mul (fourier (-k)).continuous.measurable
  rw [fourierCoeff_eq_integral, ← measurePreserving_circle.map_eq,
    integral_map Period.measurable_circle.aemeasurable hm.aestronglyMeasurable]
  calc
    _ = ∫ t, flatModePullback z.val t * Period.phase (-k) t ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [circleMode_circle_ae z.val] with t ht
      rw [ht, Period.fourier_circle]
      simp only [Int.cast_neg]
    _ = ∫ x, thetaSource.normalized x •
        (flatModePullback z.val (thetaSource.cdfFun x) *
          Period.phase (-k) (thetaSource.cdfFun x)) := by
      apply integral_unitInterval_eq_cdf
      exact ((((continuous_flatMode z.property).measurable.comp
        thetaSource.measurable_quantileFun).div (measurable_metricSymbol thetaSource)).mul
          (Period.phase_cont (-k)).measurable).aestronglyMeasurable
    _ = sourceCoeff z.val k := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [flatModePullback]
      rw [thetaSource.quantile_cdfFun, metricSymbol_cdfFun_eq, Complex.real_smul]
      have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
        exact_mod_cast (thetaSource.normalized_pos x).ne'
      field_simp

/-- The zero Fourier mode vanishes throughout the upper strip. -/
theorem sourceCoeff_zero (z : Point) : sourceCoeff z.val 0 = 0 := by
  simpa only [sourceCoeff, Int.cast_zero, neg_zero, Period.phase, zero_mul,
    mul_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one]
    using integral_flatMode z.property.1 z.property.2

/-- Symmetric source sums use every integer frequency in the stated window. -/
def sourcePartialSum (z : ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), sourceCoeff z k * Period.phase k t

theorem sourcePartialSum_eq (z : StripPoint) (N : ℕ) (t : ℝ) :
    sourcePartialSum z.val N t = symmetricPartialSum (circleMode z.val) N (Period.circle t) := by
  simp only [sourcePartialSum, symmetricPartialSum, fourierCoeff_eq_sourceCoeff z,
    Period.fourier_circle]

theorem source_quantile_recovery (z : DivisorPoint) :
    ∀ᵐ t ∂unitIntervalMeasure, Tendsto (fun N : ℕ => sourcePartialSum z.val N t)
      atTop (𝓝 (flatModePullback z.val t)) := by
  have h := quantile_recovery z
  let w : StripPoint := ⟨z.val, abs_im_lt_one_of_XiC_eq_zero z.property⟩
  filter_upwards [h] with t ht
  have he : (fun N : ℕ => sourcePartialSum z.val N t) =
      (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle t)) :=
    funext fun N => sourcePartialSum_eq w N t
  rw [he]
  exact ht

/-- Source coefficients recover the original flat mode, with Lebesgue a.e. semantics. -/
theorem source_flat_recovery (z : DivisorPoint) :
    ∀ᵐ x : ℝ, Tendsto (fun N : ℕ =>
      (thetaSource.normalized x : ℂ) * sourcePartialSum z.val N (thetaSource.cdfFun x))
        atTop (𝓝 (flatMode z.val x)) := by
  have h := (measurePreserving_cdf_unitInterval thetaSource).quasiMeasurePreserving.ae
    (source_quantile_recovery z)
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

end PaperThetaEndpoint
end RHTower
