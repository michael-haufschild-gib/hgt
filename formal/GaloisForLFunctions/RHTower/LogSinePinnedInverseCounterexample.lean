import GaloisForLFunctions.RHTower.LogSineQuantileEigenmode
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmHilbertSchmidtNorm
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# A compact pinned inverse with positive Hankel conductances and nonreal spectrum

The actual singular kernel energy is finite. In the fixed sech coordinate its
integrand is bounded by a multiple of (1+abs u)^(-2), using the literal profile
and the sine endpoint inequality. Its square-integrable field of functionals
therefore defines a bounded Hilbert–Schmidt, hence compact, operator on L2(0,1).
The operator is exactly i*M_q*C almost everywhere, retaining the full pinned history.

The previously constructed normalized L2 modes are eigenvectors of this operator.
For every sufficiently small positive regularization, a nonreal eigenvalue coexists
with strict profile concavity, positive conductances and every shifted conductance
Hankel inequality. This closes the operator-domain counterexample to that bare
criterion. The exact positive conductance moment representation remains valid;
it does not control the full directed spectral coupling. No theta arithmetic
identity, theta spectral conclusion or RH proof is asserted.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

private theorem quantile_sine_product_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    2 * t * (1 - t) ≤ Real.sin (Real.pi * t) := by
  by_cases h : t ≤ 1 / 2
  · have hs := two_mul_le_logSineProfile_sine ht.1 h
    nlinarith [sq_nonneg t]
  · have hs := two_mul_le_logSineProfile_sine (sub_nonneg.mpr ht.2)
      (show 1 - t ≤ 1 / 2 by linarith)
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub] at hs
    nlinarith [sq_nonneg (1 - t)]

private theorem logSineBaseCoordinate_energy_bound (u : ℝ) :
    Real.cosh u * logSineBaseCoordinate u * (1 - logSineBaseCoordinate u) ≤ 1 / 2 := by
  have hs := quantile_sine_product_bound (Ioo_subset_Icc_self (logSineBaseCoordinate_mem u))
  rw [sin_logSineBaseCoordinate] at hs
  have h := (le_div_iff₀ (Real.cosh_pos u)).mp hs
  nlinarith

private theorem clock_log_cosh_lower (u : ℝ) :
    |u| / 2 ≤ Real.log (1 + Real.cosh u) := by
  apply (Real.le_log_iff_exp_le (add_pos zero_lt_one (Real.cosh_pos u))).mpr
  have hc : Real.cosh u = Real.cosh |u| := by
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
    · rw [abs_of_neg (lt_of_not_ge hu), Real.cosh_neg]
  rw [hc, Real.cosh_eq]
  have he : Real.exp (|u| / 2) ^ 2 = Real.exp |u| := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [sq_nonneg (Real.exp (|u| / 2) - 1), Real.exp_pos (-|u|)]

private theorem logSineClockDenom_coercive {δ : ℝ} (hδ : 0 < δ) (u : ℝ) :
    min 1 (δ / 2) * (1 + |u|) ≤ logSineClockDenom δ u := by
  have h1 := min_le_left (1 : ℝ) (δ / 2)
  have h2 := mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) (δ / 2)) (abs_nonneg u)
  have h3 := mul_le_mul_of_nonneg_left (clock_log_cosh_lower u) hδ.le
  unfold logSineClockDenom
  nlinarith

private theorem integrable_abs_tail_square :
    Integrable (fun u : ℝ => 1 / (1 + |u|) ^ 2) := by
  have hi := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
  convert hi using 1
  funext u
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two, one_div]

private theorem integrable_logSineBase_energy {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ =>
      Real.cosh u * logSineBaseCoordinate u * (1 - logSineBaseCoordinate u) /
        (Real.pi * logSineClockDenom δ u ^ 2)) := by
  let c : ℝ := min 1 (δ / 2)
  have hc : 0 < c := lt_min zero_lt_one (half_pos hδ)
  have ht : Continuous logSineBaseCoordinate := continuous_iff_continuousAt.mpr
    fun u => (hasDerivAt_logSineBaseCoordinate u).continuousAt
  have hd (u : ℝ) : 0 < logSineClockDenom δ u :=
    zero_lt_one.trans_le (logSineClockDenom_ge_one hδ.le u)
  apply (integrable_abs_tail_square.const_mul (1 / (2 * Real.pi * c ^ 2))).mono'
  · exact ((Real.continuous_cosh.mul ht |>.mul (continuous_const.sub ht)).div
      (continuous_const.mul ((continuous_logSineClockDenom δ).pow 2))
      (fun u => mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (hd u).ne'))).aestronglyMeasurable
  · filter_upwards with u
    have htI := logSineBaseCoordinate_mem u
    have hn : 0 ≤ Real.cosh u * logSineBaseCoordinate u * (1 - logSineBaseCoordinate u) /
        (Real.pi * logSineClockDenom δ u ^ 2) := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (mul_nonneg (Real.cosh_pos u).le htI.1.le) (sub_nonneg.mpr htI.2.le)
    rw [Real.norm_of_nonneg hn]
    have hD := logSineClockDenom_coercive hδ u
    have hs : (c * (1 + |u|)) ^ 2 ≤ logSineClockDenom δ u ^ 2 :=
      pow_le_pow_left₀ (by positivity) hD 2
    calc
      _ ≤ (1 / 2) / (Real.pi * logSineClockDenom δ u ^ 2) :=
        div_le_div_of_nonneg_right (logSineBaseCoordinate_energy_bound u) (by positivity)
      _ ≤ (1 / 2) / (Real.pi * (c * (1 + |u|)) ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left hs Real.pi_pos.le)
      _ = _ := by field_simp

/-- The exact singular kernel energy is finite for every positive regularization. -/
theorem integrable_logSineQuantileKernelEnergy {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun t => logSineQuantileSpeed δ t ^ 2 * (t * (1 - t))) unitIntervalMeasure := by
  have hs := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := logSineBaseCoordinate)
    (f' := fun u => 1 / (Real.pi * Real.cosh u)) MeasurableSet.univ
    (fun u _ => (hasDerivAt_logSineBaseCoordinate u).hasDerivWithinAt)
    logSineBaseCoordinate_injective.injOn
    (fun t => logSineQuantileSpeed δ t ^ 2 * (t * (1 - t)))
  rw [logSineBaseCoordinate_image_univ, integrableOn_univ] at hs
  have hi : IntegrableOn (fun t => logSineQuantileSpeed δ t ^ 2 * (t * (1 - t)))
      (Ioo (0 : ℝ) 1) := by
    apply hs.mpr
    apply (integrable_logSineBase_energy hδ).congr
    filter_upwards with u
    rw [abs_of_pos (by positivity), smul_eq_mul]
    unfold logSineQuantileSpeed
    rw [logSineProfile_baseCoordinate]
    have hd : logSineClockDenom δ u ≠ 0 :=
      (zero_lt_one.trans_le (logSineClockDenom_ge_one hδ.le u)).ne'
    field_simp [hd, (Real.cosh_pos u).ne']
  change IntegrableOn (fun t => logSineQuantileSpeed δ t ^ 2 * (t * (1 - t))) (Icc (0 : ℝ) 1)
  exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hi

open HedenmalmHilbertSchmidt
open scoped ENNReal

local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The actual singular kernel row, represented as a continuous functional. -/
def logSinePinnedKernelField (δ t : ℝ) : H →L[ℂ] ℂ :=
  innerSL ℂ ((-(Complex.I * (logSineQuantileSpeed δ t : ℂ))) • pinnedSliceVec t)

private theorem norm_logSinePinnedKernelField {δ t : ℝ} (hδ : 0 ≤ δ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ‖logSinePinnedKernelField δ t‖ = logSineQuantileSpeed δ t * ‖pinnedSliceVec t‖ := by
  rw [logSinePinnedKernelField, innerSL_apply_norm, norm_smul, norm_neg, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (logSineQuantileSpeed_pos hδ ht)]

private theorem aestronglyMeasurable_logSinePinnedKernelField {δ : ℝ} (hδ : 0 ≤ δ) :
    AEStronglyMeasurable (logSinePinnedKernelField δ) unitIntervalMeasure := by
  have hq : ContinuousOn (logSineQuantileSpeed δ) (Ioo (0 : ℝ) 1) :=
    fun t ht => (continuousAt_logSineQuantileSpeed hδ ht).continuousWithinAt
  have hc : ContinuousOn (logSinePinnedKernelField δ) (Ioo (0 : ℝ) 1) := by
    have hscal : ContinuousOn (fun t => -(Complex.I * (logSineQuantileSpeed δ t : ℂ)))
        (Ioo (0 : ℝ) 1) :=
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hq)).neg
    exact (innerSL (𝕜 := ℂ) (E := H)).continuous.comp_continuousOn
      (hscal.smul continuous_pinnedSliceVec.continuousOn)
  have hr : unitIntervalMeasure.restrict (Ioo (0 : ℝ) 1) = unitIntervalMeasure := by
    rw [unitIntervalMeasure, Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr Ioo_subset_Icc_self, restrict_Ioo_eq_restrict_Icc]
  have hm := hc.aestronglyMeasurable (μ := unitIntervalMeasure) measurableSet_Ioo
  rwa [hr] at hm

theorem memLp_logSinePinnedKernelField {δ : ℝ} (hδ : 0 < δ) :
    MemLp (logSinePinnedKernelField δ) 2 unitIntervalMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_logSinePinnedKernelField hδ.le)).mpr
  apply (integrable_logSineQuantileKernelEnergy hδ).congr
  filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
  rw [norm_logSinePinnedKernelField hδ.le ht, mul_pow, norm_sq_pinnedSliceVec ht]

/-- The kernel is a genuine square-integrable field of functionals. -/
def logSinePinnedKernelL2 {δ : ℝ} (hδ : 0 < δ) : Lp (H →L[ℂ] ℂ) 2 unitIntervalMeasure :=
  (memLp_logSinePinnedKernelField hδ).toLp (logSinePinnedKernelField δ)

/-- The bounded singular pinned inverse, with all kernel-energy obligations discharged. -/
def logSinePinnedInverse {δ : ℝ} (hδ : 0 < δ) : H →L[ℂ] H :=
  kernelOperator unitIntervalMeasure (logSinePinnedKernelL2 hδ)

theorem isHilbertSchmidt_logSinePinnedInverse {δ : ℝ} (hδ : 0 < δ) :
    ContinuousLinearMap.IsHilbertSchmidt (logSinePinnedInverse hδ) :=
  isHilbertSchmidt_kernelOperator _ _

theorem isCompactOperator_logSinePinnedInverse {δ : ℝ} (hδ : 0 < δ) :
    IsCompactOperator (logSinePinnedInverse hδ) :=
  (isHilbertSchmidt_logSinePinnedInverse hδ).isCompactOperator

private theorem inner_pinnedSliceVec_eq (t : ℝ) (f : H) :
    (inner ℂ (pinnedSliceVec t) f : ℂ) = pinnedVolterraFun f t := by
  rw [MeasureTheory.L2.inner_def, pinnedVolterraFun, pinnedPrefix, pinnedMean]
  have he : (fun u => (inner ℂ ((pinnedSliceVec t : ℝ → ℂ) u) (f u) : ℂ))
      =ᵐ[unitIntervalMeasure]
      fun u => (Iic t).indicator (fun u => f u) u - (t : ℂ) * f u := by
    filter_upwards [pinnedSliceVec_coeFn t] with u hu
    rw [hu, RCLike.inner_apply', pinnedKernelSlice]
    by_cases hut : u ≤ t <;> simp [hut]
    ring
  rw [integral_congr_ae he,
    integral_sub ((integrable_coe f).indicator measurableSet_Iic) ((integrable_coe f).const_mul (t : ℂ)),
    integral_const_mul]

private theorem logSinePinnedKernelField_apply (δ t : ℝ) (f : H) :
    logSinePinnedKernelField δ t f =
      Complex.I * (logSineQuantileSpeed δ t : ℂ) * pinnedVolterraFun f t := by
  change (inner ℂ ((-(Complex.I * (logSineQuantileSpeed δ t : ℂ))) • pinnedSliceVec t) f : ℂ) = _
  rw [inner_smul_left, inner_pinnedSliceVec_eq]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The bounded operator retains the original singular coefficient and full pinned history. -/
theorem logSinePinnedInverse_ae {δ : ℝ} (hδ : 0 < δ) (f : H) :
    (logSinePinnedInverse hδ f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => Complex.I * (logSineQuantileSpeed δ t : ℂ) * (pinnedVolterra f) t := by
  have hh := (evalBilinear (𝕜 := ℂ) (E := H)).coeFn_holder
    (r := (2 : ENNReal)) (logSinePinnedKernelL2 hδ) (Lp.const ∞ unitIntervalMeasure f)
  have hf := (memLp_logSinePinnedKernelField hδ).coeFn_toLp
  have hc := Lp.coeFn_const (p := ∞) unitIntervalMeasure f
  filter_upwards [hh, hf, hc, pinnedVolterra_coeFn f] with t hh hf hc hv
  rw [logSinePinnedInverse, kernelOperator, kernelOperatorMap_apply, hh,
    logSinePinnedKernelL2, hf, hc]
  change logSinePinnedKernelField δ t f =
    Complex.I * (logSineQuantileSpeed δ t : ℂ) * (pinnedVolterra f) t
  rw [logSinePinnedKernelField_apply, hv]

/-- Actual compact-operator eigenvectors arise from the already normalized literal modes. -/
theorem logSinePinnedInverse_mode_eigen {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    logSinePinnedInverse hδ (logSineModeVector hδ z hz) = (-z⁻¹) • logSineModeVector hδ z hz := by
  apply Lp.ext
  filter_upwards [logSinePinnedInverse_ae hδ (logSineModeVector hδ z hz),
    logSineModeVector_root hδ z hz, Lp.coeFn_smul (-z⁻¹) (logSineModeVector hδ z hz)]
    with t hb hr hs
  rw [hb, hs]
  exact hr

/-- The literal Hilbert–Schmidt pinned inverse has nonreal eigenvalues despite every
shifted positive conductance Hankel form and strict profile concavity. -/
theorem logSine_positive_hankel_nonreal_compact_spectrum :
    ∃ η : ℝ, 0 < η ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ < η →
      StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (logSineProfile δ) ∧
      (∀ n : ℕ, 0 < logSineConductance δ (n + 1)) ∧
      (∀ (shift : ℕ) (F : Finset ℕ) (c : ℕ → ℝ),
        0 ≤ ∑ m ∈ F, ∑ n ∈ F, c m * c n * logSineConductance δ (m + n + shift + 1)) ∧
      ∃ (lam : ℂ) (f : H), lam.im ≠ 0 ∧ f ≠ 0 ∧ pinnedMean f = 1 ∧
        logSinePinnedInverse hδ f = lam • f := by
  obtain ⟨η, hη, hm⟩ := logSine_positive_hankel_nonreal_pinned_mode
  refine ⟨η, hη, fun δ hδ hsmall => ?_⟩
  obtain ⟨hconc, hpos, hhankel, lam, f, hlam, hf, hmean, heq⟩ := hm δ hδ hsmall
  refine ⟨hconc, hpos, hhankel, lam, f, hlam, hf, hmean, ?_⟩
  apply Lp.ext
  filter_upwards [logSinePinnedInverse_ae hδ f, heq, Lp.coeFn_smul lam f] with t hb he hs
  rw [hb, hs]
  exact he

end
end RHTower
