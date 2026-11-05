import GaloisForLFunctions.RHTower.WeilLevyHarmonicDoublingPairCoupling
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelLogFourierKernel
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanGeometricCommutatorKernel

/-!
# The logarithmic part of the literal Weil symbol

Subtracting exp(-t)/(2t) from the positive-lag archimedean Lévy density
leaves a positive kernel bounded by 3/4, with integrable even extension.
The Abel logarithmic identity gives the exact spectral decomposition.
Its remaining Fourier multiplier is a bounded self-adjoint physical
convolution and preserves essential boundedness.
-/

open MeasureTheory Set Filter
open scoped FourierTransform
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower

/-- The positive-lag Lévy density of `(1/2) log(1-D²)`. -/
def logReferenceLevyDensity (t : ℝ) : ℝ := Real.exp (-t) / (2 * t)

/-- The integrable difference between the Weil and logarithmic Lévy densities. -/
def archLogRemainder (t : ℝ) : ℝ := archLevyDensity t - logReferenceLevyDensity t

theorem measurable_archLogRemainder : Measurable archLogRemainder := by
  unfold archLogRemainder logReferenceLevyDensity
  exact measurable_archLevyDensity.sub (by fun_prop)

theorem archLogRemainder_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ archLogRemainder t := by
  have hd : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith only [ht]))
  have hdt : 1 - Real.exp (-2 * t) ≤ 2 * t := by
    linarith only [Real.add_one_le_exp (-2 * t)]
  unfold archLogRemainder logReferenceLevyDensity archLevyDensity
  apply sub_nonneg.mpr
  calc
    _ ≤ Real.exp (-t / 2) / (2 * t) :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [ht]))
        (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hd hdt

theorem archLogRemainder_le_three_quarters {t : ℝ} (ht : 0 < t) :
    archLogRemainder t ≤ 3 / 4 := by
  have hj := WeilLevyHarmonicDoubling.two_mul_archLevyDensity_le_inv_add_half ht
  have hrec : 1 / t = 2 * (1 / (2 * t)) := by ring
  rw [hrec] at hj
  have hexp : (1 - Real.exp (-t)) / (2 * t) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [Real.add_one_le_exp (-t)]
  have hdiff : 1 / (2 * t) - logReferenceLevyDensity t =
      (1 - Real.exp (-t)) / (2 * t) := by
    unfold logReferenceLevyDensity
    ring
  unfold archLogRemainder
  linarith only [hj, hexp, hdiff]

theorem archLogRemainder_le_density {t : ℝ} (ht : 0 < t) :
    archLogRemainder t ≤ archLevyDensity t := by
  unfold archLogRemainder logReferenceLevyDensity
  exact sub_le_self _ (div_nonneg (Real.exp_pos _).le (by positivity))

/-- Removing the logarithmic singularity leaves a positive integrable kernel. -/
theorem integrableOn_archLogRemainder : IntegrableOn archLogRemainder (Ioi 0) := by
  have hnear : IntegrableOn archLogRemainder (Ioc (0 : ℝ) 1) := by
    have hc : IntegrableOn (fun _ : ℝ => (3 / 4 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (hs := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
    apply hc.mono' measurable_archLogRemainder.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (archLogRemainder_nonneg ht.1)]
    exact archLogRemainder_le_three_quarters ht.1
  have hfar : IntegrableOn archLogRemainder (Ioi (1 : ℝ)) := by
    apply (WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi (by norm_num : (0 : ℝ) < 1)).mono'
      measurable_archLogRemainder.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, abs_of_nonneg (archLogRemainder_nonneg ht0)]
    exact archLogRemainder_le_density ht0
  have hs : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ht.1
      · exact lt_trans (zero_lt_one : (0 : ℝ) < 1) (show (1 : ℝ) < t from ht)
    · intro ht
      by_cases h : t ≤ 1
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hs]
  exact hnear.union hfar

/-- The even remainder is a finite convolution kernel on the physical line. -/
theorem integrable_archLogRemainder_abs : Integrable (fun t : ℝ => archLogRemainder |t|) := by
  let f : ℝ → ℝ := fun t => archLogRemainder |t|
  have hi : IntegrableOn f (Ioi 0) :=
    integrableOn_archLogRemainder.congr_fun (fun t ht => by
      dsimp only [f]
      rw [abs_of_pos ht]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp only [Function.comp_def, f, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hi

#print axioms integrable_archLogRemainder_abs

theorem integrableOn_archLogRemainder_mul_cos (ξ : ℝ) :
    IntegrableOn (fun t => archLogRemainder t * Real.cos (ξ * t)) (Ioi 0) := by
  refine integrableOn_archLogRemainder.mono'
    (measurable_archLogRemainder.mul (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (archLogRemainder_nonneg ht)]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (ξ * t)) (archLogRemainder_nonneg ht)

/-- The reference Lévy symbol has the exact logarithmic normalization. -/
theorem logReferenceLevyDensity_symbol (ξ : ℝ) :
    (∫ t in Ioi (0 : ℝ), logReferenceLevyDensity t * (1 - Real.cos (ξ * t))) =
      (1 / 4 : ℝ) * Real.log (1 + ξ ^ 2) := by
  calc
    _ = (1 / 2 : ℝ) * abelLogKernelIntegral 1 ξ := by
      unfold abelLogKernelIntegral
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [logReferenceLevyDensity, abelLogKernelIntegrand, one_mul]
      ring
    _ = _ := by
      rw [integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos (by norm_num)]
      simp only [div_one]
      ring

/-- The finite scalar part left after extracting the logarithmic multiplier. -/
def archLogScalar : ℝ :=
  2 * gammaHardyPhaseRate 0 + 2 * ∫ t in Ioi (0 : ℝ), archLogRemainder t

/-- Exact symbol decomposition: logarithmic reference plus a finite cosine kernel. -/
theorem gammaHardyPhaseRate_eq_log_reference (ξ : ℝ) :
    2 * gammaHardyPhaseRate ξ =
      (1 / 2 : ℝ) * Real.log (1 + ξ ^ 2) + archLogScalar -
        2 * ∫ t in Ioi (0 : ℝ), archLogRemainder t * Real.cos (ξ * t) := by
  have hr := integrableOn_archLogRemainder
  have hc := integrableOn_archLogRemainder_mul_cos ξ
  have hj := integrableOn_archLevyDensity_mul_one_sub_cos ξ
  have hn : IntegrableOn
      (fun t => logReferenceLevyDensity t * (1 - Real.cos (ξ * t))) (Ioi 0) := by
    refine (hj.sub (hr.sub hc)).congr ?_
    filter_upwards [] with t
    change archLevyDensity t * (1 - Real.cos (ξ * t)) -
      (archLogRemainder t - archLogRemainder t * Real.cos (ξ * t)) = _
    unfold archLogRemainder
    ring
  have hs : gammaHardyPhaseRate ξ - gammaHardyPhaseRate 0 =
      (1 / 4 : ℝ) * Real.log (1 + ξ ^ 2) +
        ((∫ t in Ioi (0 : ℝ), archLogRemainder t) -
          ∫ t in Ioi (0 : ℝ), archLogRemainder t * Real.cos (ξ * t)) := by
    rw [gammaHardyPhaseRate_sub_zero_eq_integral]
    calc
      _ = ∫ t in Ioi (0 : ℝ),
          logReferenceLevyDensity t * (1 - Real.cos (ξ * t)) +
            (archLogRemainder t - archLogRemainder t * Real.cos (ξ * t)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        unfold archLogRemainder
        ring
      _ = _ := by
        have hrc : IntegrableOn
            (fun t => archLogRemainder t - archLogRemainder t * Real.cos (ξ * t))
            (Ioi (0 : ℝ)) := hr.sub hc
        have hsub : (∫ t in Ioi (0 : ℝ),
            archLogRemainder t - archLogRemainder t * Real.cos (ξ * t)) =
            (∫ t in Ioi (0 : ℝ), archLogRemainder t) -
              ∫ t in Ioi (0 : ℝ), archLogRemainder t * Real.cos (ξ * t) :=
          integral_sub hr hc
        rw [integral_add hn hrc, hsub, logReferenceLevyDensity_symbol]
  unfold archLogScalar
  linarith only [hs]

#print axioms gammaHardyPhaseRate_eq_log_reference

@[simp] theorem archLogRemainder_zero : archLogRemainder 0 = 0 := by
  simp only [archLogRemainder, archLevyDensity, logReferenceLevyDensity,
    neg_zero, zero_div, Real.exp_zero, mul_zero, sub_self, div_zero]

theorem archLogRemainder_abs_nonneg (t : ℝ) : 0 ≤ archLogRemainder |t| := by
  by_cases ht : t = 0
  · simp only [ht, abs_zero, archLogRemainder_zero, le_refl]
  · exact archLogRemainder_nonneg (abs_pos.mpr ht)

theorem archLogRemainder_abs_le (t : ℝ) : archLogRemainder |t| ≤ 3 / 4 := by
  by_cases ht : t = 0
  · simp only [ht, abs_zero, archLogRemainder_zero]
    norm_num
  · exact archLogRemainder_le_three_quarters (abs_pos.mpr ht)

/-- The literal even convolution profile lies in both L¹ and L². -/
def archLogEvenSource : CCMEvenL1L2Source where
  toFun t := (archLogRemainder |t| : ℂ)
  integrable := integrable_archLogRemainder_abs.ofReal
  memLp_two := RHTower.memLp_two_of_integrable_of_norm_le
    integrable_archLogRemainder_abs.ofReal (C := 3 / 4) (fun t => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (archLogRemainder_abs_nonneg t)]
      exact archLogRemainder_abs_le t)
  even t := by simp only [abs_neg]

theorem measurable_archLogEvenSource : Measurable (archLogEvenSource : ℝ → ℂ) :=
  Complex.continuous_ofReal.measurable.comp (measurable_archLogRemainder.comp measurable_abs)

theorem archLogEvenSource_fourier (ξ : ℝ) :
    𝓕 (archLogEvenSource : ℝ → ℂ) ξ =
      ((2 * ∫ t in Ioi (0 : ℝ), archLogRemainder t *
        Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) := by
  rw [CCMEvenL1L2Source.fourier_eq_two_mul_integral_Ioi_cos]
  push_cast
  congr 1
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (archLogRemainder |t| : ℂ) *
    Complex.cos (2 * (Real.pi : ℂ) * (ξ : ℂ) * (t : ℂ)) = _
  have hangle : 2 * (Real.pi : ℂ) * (ξ : ℂ) * (t : ℂ) =
      ((2 * Real.pi * ξ * t : ℝ) : ℂ) := by push_cast; rfl
  rw [hangle, ← Complex.ofReal_cos, abs_of_pos ht]
  exact (Complex.ofReal_mul _ _).symm

/-- The archimedean Weil symbol is the logarithmic reference minus a bounded Fourier multiplier. -/
theorem gammaHardyPhaseRate_eq_log_reference_fourier (ξ : ℝ) :
    2 * gammaHardyPhaseRate (2 * Real.pi * ξ) =
      (1 / 2 : ℝ) * Real.log (1 + (2 * Real.pi * ξ) ^ 2) + archLogScalar -
        (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re := by
  rw [archLogEvenSource_fourier, Complex.ofReal_re]
  exact gammaHardyPhaseRate_eq_log_reference (2 * Real.pi * ξ)

open GaloisForLFunctions.HTGeometry

/-- The finite even remainder acts by literal convolution on physical L². -/
def archLogConvolution : SoninL2 →L[ℂ] SoninL2 :=
  (convolutionKernel archLogEvenSource measurable_archLogEvenSource
    archLogEvenSource.integrable).op

theorem archLogConvolution_coeFn (f : SoninL2) :
    (archLogConvolution f : ℝ → ℂ) =ᵐ[volume]
      fun x => ∫ y : ℝ, (archLogRemainder |x - y| : ℂ) * f y :=
  (convolutionKernel archLogEvenSource measurable_archLogEvenSource
    archLogEvenSource.integrable).op_coeFn f

/-- The even real remainder gives a bounded self-adjoint convolution operator. -/
theorem archLogConvolution_isSelfAdjoint : IsSelfAdjoint archLogConvolution := by
  rw [archLogConvolution, convolutionKernel_op_eq_fourierMulCLM]
  apply isSelfAdjoint_fourierMulCLM
  intro ξ
  rw [archLogEvenSource_fourier]
  exact Complex.conj_ofReal _

/-- This physical convolution sends essentially bounded sources to essentially bounded sources. -/
theorem archLogConvolution_bound (f : SoninL2) (C : ℝ)
    (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖archLogConvolution f x‖ ≤
      (∫ t : ℝ, ‖archLogEvenSource t‖) * C := by
  filter_upwards [archLogConvolution_coeFn f] with x hx
  rw [hx]
  calc
    _ ≤ ∫ y : ℝ, ‖archLogEvenSource (x - y)‖ * C := by
      apply norm_integral_le_of_norm_le
        ((archLogEvenSource.integrable.comp_sub_left x).norm.mul_const C)
      filter_upwards [hb] with y hy
      change ‖archLogEvenSource (x - y) * f y‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      exact integral_sub_left_eq_self (fun t : ℝ => ‖archLogEvenSource t‖) volume x

#print axioms gammaHardyPhaseRate_eq_log_reference_fourier
#print axioms archLogConvolution_isSelfAdjoint
#print axioms archLogConvolution_bound

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
