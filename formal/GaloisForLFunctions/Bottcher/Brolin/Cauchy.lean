/-
# Böttcher tower — Brolin: Cauchy-transform limits

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.TargetLimit

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-! ## Cauchy-transform limit for the constructed hDisc measure -/

noncomputable def truncatedCauchyKernel (z : ℂ) (δ : ℝ) (w : ℂ) : ℂ :=
  (starRingEnd ℂ) (z - w) /
    (((max (δ ^ 2) (‖z - w‖ ^ 2) : ℝ) : ℂ))

theorem continuous_truncatedCauchyKernel {z : ℂ} {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun w : ℂ => truncatedCauchyKernel z δ w) := by
  unfold truncatedCauchyKernel
  have hnum : Continuous fun w : ℂ => (starRingEnd ℂ) (z - w) := by
    fun_prop
  have hreal :
      Continuous fun w : ℂ => max (δ ^ 2) (‖z - w‖ ^ 2) :=
    continuous_const.max (((continuous_const.sub continuous_id).norm).pow 2)
  have hden :
      Continuous fun w : ℂ =>
        (((max (δ ^ 2) (‖z - w‖ ^ 2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp hreal
  refine hnum.div hden ?_
  intro w
  have hpos : 0 < max (δ ^ 2) (‖z - w‖ ^ 2) :=
    lt_of_lt_of_le (sq_pos_of_pos hδ) (le_max_left _ _)
  exact_mod_cast (ne_of_gt hpos)

theorem truncatedCauchyKernel_eq_cauchyKernel_of_le_norm
    {z w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδw : δ ≤ ‖z - w‖) :
    truncatedCauchyKernel z δ w = (z - w)⁻¹ := by
  unfold truncatedCauchyKernel
  have hsq : δ ^ 2 ≤ ‖z - w‖ ^ 2 := by
    nlinarith [hδw, hδ, norm_nonneg (z - w)]
  rw [max_eq_right hsq]
  set x : ℂ := z - w
  have hx : x ≠ 0 := by
    intro hx0
    have hnorm : ‖z - w‖ = 0 := by
      simpa [x] using congrArg norm hx0
    rw [hnorm] at hδw
    linarith
  change (starRingEnd ℂ) x / (((‖x‖ ^ 2 : ℝ) : ℂ)) = x⁻¹
  have hden : x * (starRingEnd ℂ) x = (((‖x‖ ^ 2 : ℝ) : ℂ)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← hden]
  field_simp [hx]

theorem cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂μ =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂μ := by
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact congrArg Complex.re
    (truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)).symm

theorem cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂μ =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂μ := by
  refine integral_congr_ae ?_
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  filter_upwards [hmem] with w hw
  exact congrArg Complex.im
    (truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)).symm

/-- If a finite measure is carried by a Green sublevel uniformly separated from
`z`, then the true Cauchy kernel at `z` is integrable against that measure. -/
theorem cauchyKernel_integrable_of_greenSublevel_support
    {c z : ℂ} {μ : Measure ℂ} [IsFiniteMeasure μ] {ε δ : ℝ}
    (hμ : μ (greenSublevel c ε)ᶜ = 0) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    Integrable (fun w : ℂ => (z - w)⁻¹) μ := by
  have hmem : ∀ᵐ w ∂μ, w ∈ greenSublevel c ε := by
    exact (mem_ae_iff).2 hμ
  have htrunc :
      Integrable (fun w : ℂ => truncatedCauchyKernel z δ w) μ := by
    refine Integrable.of_bound
      (Measurable.aestronglyMeasurable
        (continuous_truncatedCauchyKernel (z := z) hδ).measurable)
      δ⁻¹ ?_
    filter_upwards [hmem] with w hw
    rw [truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)]
    rw [norm_inv]
    gcongr
    exact hsep w hw
  refine htrunc.congr ?_
  filter_upwards [hmem] with w hw
  exact truncatedCauchyKernel_eq_cauchyKernel_of_le_norm hδ (hsep w hw)

noncomputable def truncatedCauchyKernelReOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => (truncatedCauchyKernel z δ (w : ℂ)).re,
      Complex.continuous_re.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

noncomputable def truncatedCauchyKernelImOnEscapeDisk
    (c z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (escapeDisk c) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : escapeDisk c => (truncatedCauchyKernel z δ (w : ℂ)).im,
      Complex.continuous_im.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

theorem integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂preBrolinMeasure c n =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂preBrolinMeasureOnEscapeDisk c n := by
  rw [preBrolinMeasure_eq_map_preBrolinMeasureOnEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_limitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [limitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) := by
  rw [shiftedLimitingBrolinMeasure, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelReOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelReOnEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(brolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelImOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelImOnEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_re_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasure_subseq_integral_tendsto_limiting
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_subseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_im_limitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelReOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelReOnEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityOnEscapeDisk c (shiftedBrolinIndex c k) :
            Measure (escapeDisk c)))
      atTop
      (𝓝 (∫ w : escapeDisk c, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (shiftedBrolinProbabilityOnEscapeDisk_subseq_tendsto c))
      (truncatedCauchyKernelImOnEscapeDisk c z δ hδ)
  simpa [truncatedCauchyKernelImOnEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re
        ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_re_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
    (c z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im
        ∂shiftedLimitingBrolinMeasure c)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityOnEscapeDisk_shiftedSubseq_integral_tendsto
      c z hδ
  rw [integral_truncatedCauchyKernel_im_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  rfl

theorem eventually_cauchyIntegral_re_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (brolinLimitSubsequence c k) := by
  filter_upwards [eventually_preBrolinMeasure_subseq_greenSublevel_compl_of_pos
    c hε] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_re_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasure c (shiftedBrolinIndex c k) := by
  have hfull :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_preBrolinMeasure_greenSublevel_compl_of_pos c hε)
  filter_upwards [hfull] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem cauchyIntegral_re_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂limitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasure c :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_im_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂limitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasure c :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_re_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).re
        ∂shiftedLimitingBrolinMeasure c :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

theorem cauchyIntegral_im_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
    (c z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (truncatedCauchyKernel z δ w).im
        ∂shiftedLimitingBrolinMeasure c :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hε) hδ hsep

def HasSubseqCauchyTransformLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).re
        ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).im
        ∂preBrolinMeasure c (brolinLimitSubsequence c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

def HasShiftedSubseqCauchyTransformLimit (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).re
        ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto
      (fun k => ∫ w, ((z - w)⁻¹).im
        ∂preBrolinMeasure c (shiftedBrolinIndex c k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem limitingBrolinMeasure_hasSubseqCauchyTransformLimit (c : ℂ) :
    HasSubseqCauchyTransformLimit c (limitingBrolinMeasure c) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htruncRe :=
    truncatedCauchyKernel_re_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδpos
  have hlimRe :=
    cauchyIntegral_re_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_limitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasure_subseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit
    (c : ℂ) :
    HasShiftedSubseqCauchyTransformLimit c (shiftedLimitingBrolinMeasure c) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htruncRe :=
    truncatedCauchyKernel_re_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
      c z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasure_shiftedSubseq_integral_tendsto_shifted
      c z hδpos
  have hlimRe :=
    cauchyIntegral_re_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_shiftedLimitingBrolinMeasure_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasure_shiftedSubseq_eq_integral_truncatedCauchyKernel
      c z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem gapAMu_hasSubseqCauchyTransformLimit (c : ℂ) :
    HasSubseqCauchyTransformLimit c (gapAMu c) := by
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact limitingBrolinMeasure_hasSubseqCauchyTransformLimit c

/-- Along the shifted compactness extraction, the finite normalized logarithmic
derivatives have the same exterior limit as the unshifted GAP-A measure. -/
theorem finiteBrolinNormalizedLogDerivative_zero_shiftedSubseq_tendsto_gapAMu
    (c : ℂ) {z : ℂ} (hz : z ∉ filledJulia c) :
    Tendsto
      (fun k =>
        (finiteBrolinNormalizedLogDerivativeAt c 0 z
          (shiftedBrolinIndex c k)).re)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) ∧
    Tendsto
      (fun k =>
        (finiteBrolinNormalizedLogDerivativeAt c 0 z
          (shiftedBrolinIndex c k)).im)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
  let η : ℕ → ℕ := shiftedBrolinLimitSubsequence c
  let nseq : ℕ → ℕ := fun k => brolinLimitSubsequence c (η k)
  let factor : ℕ → ℂ := fun k =>
    ((quadratic c)^[nseq k] z) ^ 2 / (quadratic c)^[nseq k + 1] z
  have hη : Tendsto η atTop atTop :=
    shiftedBrolinLimitSubsequence_tendsto_atTop c
  have hnseq : Tendsto nseq atTop atTop :=
    (brolinLimitSubsequence_tendsto_atTop c).comp hη
  have hbaseInt := gapAMu_hasSubseqCauchyTransformLimit c hz
  have hbaseIntRe :
      Tendsto
        (fun k =>
          ∫ w, ((z - w)⁻¹).re
            ∂preBrolinMeasure c (nseq k))
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    simpa [nseq, η] using hbaseInt.1.comp hη
  have hbaseIntIm :
      Tendsto
        (fun k =>
          ∫ w, ((z - w)⁻¹).im
            ∂preBrolinMeasure c (nseq k))
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    simpa [nseq, η] using hbaseInt.2.comp hη
  have hvalidBase :
      ∀ᶠ k in atTop, (quadratic c)^[nseq k] z ≠ 0 :=
    hnseq.eventually (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  have hbaseDerivRe :
      Tendsto
        (fun k => (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k)).re)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    refine hbaseIntRe.congr' ?_
    filter_upwards [hvalidBase] with k hk
    have h :=
      integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := nseq k) (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (nseq k)] at h
    exact h
  have hbaseDerivIm :
      Tendsto
        (fun k => (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k)).im)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    refine hbaseIntIm.congr' ?_
    filter_upwards [hvalidBase] with k hk
    have h :=
      integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := nseq k) (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (nseq k)] at h
    exact h
  have hfactor : Tendsto factor atTop (𝓝 (1 : ℂ)) := by
    simpa [factor, nseq] using
      finiteBrolinCauchyShiftFactor_tendsto_one
        (c := c) (z := z) hz (φ := nseq) hnseq
  have hfactorRe : Tendsto (fun k => (factor k).re) atTop (𝓝 1) := by
    simpa [factor] using (Complex.continuous_re.tendsto (1 : ℂ)).comp hfactor
  have hfactorIm : Tendsto (fun k => (factor k).im) atTop (𝓝 0) := by
    simpa [factor] using (Complex.continuous_im.tendsto (1 : ℂ)).comp hfactor
  have hprodRe :
      Tendsto
        (fun k =>
          (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) *
            factor k).re)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂gapAMu c)) := by
    have h :=
      (hbaseDerivRe.mul hfactorRe).sub
        (hbaseDerivIm.mul hfactorIm)
    simpa [Complex.mul_re] using h
  have hprodIm :
      Tendsto
        (fun k =>
          (finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) *
            factor k).im)
        atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂gapAMu c)) := by
    have h :=
      (hbaseDerivRe.mul hfactorIm).add
        (hbaseDerivIm.mul hfactorRe)
    simpa [Complex.mul_im] using h
  have hvalidShift :
      ∀ᶠ k in atTop, (quadratic c)^[nseq k + 1] z ≠ 0 :=
    ((tendsto_add_atTop_nat 1).comp hnseq).eventually
      (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  have hrec :
      ∀ᶠ k in atTop,
        finiteBrolinNormalizedLogDerivativeAt c 0 z (shiftedBrolinIndex c k) =
          finiteBrolinNormalizedLogDerivativeAt c 0 z (nseq k) * factor k := by
    filter_upwards [hvalidBase, hvalidShift] with k hk0 hk1
    simpa [shiftedBrolinIndex, nseq, η, factor] using
      finiteBrolinNormalizedLogDerivativeAt_zero_succ_eq_mul
        (c := c) (z := z) (n := nseq k) hk0 hk1
  constructor
  · refine hprodRe.congr' ?_
    filter_upwards [hrec] with k hk
    exact congrArg Complex.re hk.symm
  · refine hprodIm.congr' ?_
    filter_upwards [hrec] with k hk
    exact congrArg Complex.im hk.symm

/-- The shifted finite Cauchy transforms also converge to the GAP-A Cauchy
transform. -/
theorem gapAMu_hasShiftedSubseqCauchyTransformLimit (c : ℂ) :
    HasShiftedSubseqCauchyTransformLimit c (gapAMu c) := by
  intro z hz
  have hderiv :=
    finiteBrolinNormalizedLogDerivative_zero_shiftedSubseq_tendsto_gapAMu
      c hz
  have hvalid :
      ∀ᶠ k in atTop, (quadratic c)^[shiftedBrolinIndex c k] z ≠ 0 :=
    (shiftedBrolinIndex_tendsto_atTop c).eventually
      (eventually_iterate_ne_zero_of_not_mem_filledJulia hz)
  constructor
  · refine hderiv.1.congr' ?_
    filter_upwards [hvalid] with k hk
    have h :=
      integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := shiftedBrolinIndex c k)
        (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (shiftedBrolinIndex c k)] at h
    exact h.symm
  · refine hderiv.2.congr' ?_
    filter_upwards [hvalid] with k hk
    have h :=
      integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div
        (c := c) (a := 0) (z := z) (n := shiftedBrolinIndex c k)
        (by simpa using hk)
    rw [preBrolinMeasureAt_zero c (shiftedBrolinIndex c k)] at h
    exact h.symm

/-- The shifted cluster and the GAP-A limiting/Riesz measure have identical
exterior Cauchy transforms. -/
theorem shiftedLimitingBrolinMeasure_cauchyIntegral_eq_gapAMu_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    (∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
      ∫ w, ((z - w)⁻¹).re ∂gapAMu c) ∧
    (∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
      ∫ w, ((z - w)⁻¹).im ∂gapAMu c) := by
  have hshift :=
    shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit c hz
  have hgap :=
    gapAMu_hasShiftedSubseqCauchyTransformLimit c hz
  exact ⟨tendsto_nhds_unique hshift.1 hgap.1,
    tendsto_nhds_unique hshift.2 hgap.2⟩

/-- Complex Cauchy-transform equality for the shifted compactness limit and the
GAP-A limiting/Riesz measure on the basin.  This is the uniqueness substrate for
identifying the shifted cluster with `μ_c`. -/
theorem shiftedLimitingBrolinMeasure_cauchyIntegral_complex_eq_gapAMu_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    ∫ w, (z - w)⁻¹ ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (z - w)⁻¹ ∂gapAMu c := by
  have hpair := shiftedLimitingBrolinMeasure_cauchyIntegral_eq_gapAMu_on_basin
    (c := c) (z := z) hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  haveI : IsProbabilityMeasure (shiftedLimitingBrolinMeasure c) :=
    (shiftedLimitingBrolinMeasure_isProbOn_filledJulia c).1
  haveI : IsProbabilityMeasure (gapAMu c) :=
    (gapAMu_isProbOn_filledJulia c).1
  have hshiftInt :
      Integrable (fun w : ℂ => (z - w)⁻¹)
        (shiftedLimitingBrolinMeasure c) :=
    cauchyKernel_integrable_of_greenSublevel_support
      (c := c) (z := z) (μ := shiftedLimitingBrolinMeasure c)
      (ε := ε) (δ := δ)
      (shiftedLimitingBrolinMeasure_greenSublevel_compl_of_pos c hεpos)
      hδpos hsep
  have hgapInt :
      Integrable (fun w : ℂ => (z - w)⁻¹) (gapAMu c) := by
    rw [gapAMu_eq_brolinMu, brolinMu]
    exact cauchyKernel_integrable_of_greenSublevel_support
      (c := c) (z := z) (μ := limitingBrolinMeasure c)
      (ε := ε) (δ := δ)
      (limitingBrolinMeasure_greenSublevel_compl_of_pos c hεpos)
      hδpos hsep
  apply Complex.ext
  · rw [← Complex.reCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hshiftInt]
    rw [← Complex.reCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hgapInt]
    exact hpair.1
  · rw [← Complex.imCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hshiftInt]
    rw [← Complex.imCLM_apply,
      ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hgapInt]
    exact hpair.2

/-- On the basin, the shifted limiting measure has the same Cauchy transform
after pushing its integration variable through `f_c`.  This is the analytic form
of the already-proved measure pushforward
`(f_c)_* shiftedLimitingBrolinMeasure = gapAMu`, combined with the complex
Cauchy-transform identification above. -/
theorem shiftedLimitingBrolinMeasure_cauchyIntegral_eq_comp_quadratic_on_basin
    {c z : ℂ} (hz : z ∉ filledJulia c) :
    ∫ w, (z - w)⁻¹ ∂shiftedLimitingBrolinMeasure c =
      ∫ w, (z - quadratic c w)⁻¹ ∂shiftedLimitingBrolinMeasure c := by
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  haveI : IsProbabilityMeasure (gapAMu c) :=
    (gapAMu_isProbOn_filledJulia c).1
  have hgapInt :
      Integrable (fun y : ℂ => (z - y)⁻¹) (gapAMu c) := by
    rw [gapAMu_eq_brolinMu, brolinMu]
    exact cauchyKernel_integrable_of_greenSublevel_support
      (c := c) (z := z) (μ := limitingBrolinMeasure c)
      (ε := ε) (δ := δ)
      (limitingBrolinMeasure_greenSublevel_compl_of_pos c hεpos)
      hδpos hsep
  calc
    ∫ w, (z - w)⁻¹ ∂shiftedLimitingBrolinMeasure c
        = ∫ y, (z - y)⁻¹ ∂gapAMu c := by
          exact shiftedLimitingBrolinMeasure_cauchyIntegral_complex_eq_gapAMu_on_basin hz
    _ = ∫ w, (z - quadratic c w)⁻¹ ∂shiftedLimitingBrolinMeasure c := by
      rw [← map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c]
      rw [integral_map]
      · exact (continuous_quadratic c).measurable.aemeasurable
      · simpa [map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c] using
          hgapInt.aestronglyMeasurable

theorem gapAMu_hDiscZeroTargetCauchyCore (c : ℂ) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      HasSubseqCauchyTransformLimit c (gapAMu c) ∧
      HasShiftedSubseqCauchyTransformLimit c (gapAMu c) ∧
      HasShiftedSubseqCauchyTransformLimit c (shiftedLimitingBrolinMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        ((∫ w, ((z - w)⁻¹).re ∂shiftedLimitingBrolinMeasure c =
            ∫ w, ((z - w)⁻¹).re ∂gapAMu c) ∧
          (∫ w, ((z - w)⁻¹).im ∂shiftedLimitingBrolinMeasure c =
            ∫ w, ((z - w)⁻¹).im ∂gapAMu c)) ∧
        ∫ w, (z - w)⁻¹ ∂shiftedLimitingBrolinMeasure c =
          ∫ w, (z - w)⁻¹ ∂gapAMu c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · exact gapAMu_hasSubseqCauchyTransformLimit c
  · exact gapAMu_hasShiftedSubseqCauchyTransformLimit c
  · exact shiftedLimitingBrolinMeasure_hasShiftedSubseqCauchyTransformLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro z hz
    exact ⟨
      shiftedLimitingBrolinMeasure_cauchyIntegral_eq_gapAMu_on_basin hz,
      shiftedLimitingBrolinMeasure_cauchyIntegral_complex_eq_gapAMu_on_basin hz⟩

noncomputable def truncatedCauchyKernelOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => truncatedCauchyKernel z δ (w : ℂ),
      (continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val⟩

theorem integral_truncatedCauchyKernel_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, truncatedCauchyKernel z δ w ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, truncatedCauchyKernel z δ (w : ℂ)
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedCauchyKernel (z := z) hδ).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedCauchyKernel z δ w ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, truncatedCauchyKernel z δ (w : ℂ)
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (continuous_truncatedCauchyKernel (z := z) hδ).aestronglyMeasurable

noncomputable def truncatedCauchyKernelReOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => (truncatedCauchyKernel z δ (w : ℂ)).re,
      Complex.continuous_re.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

noncomputable def truncatedCauchyKernelImOnTargetEscapeDisk
    (c a z : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    BoundedContinuousFunction (targetEscapeDisk c a) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun w : targetEscapeDisk c a => (truncatedCauchyKernel z δ (w : ℂ)).im,
      Complex.continuous_im.comp
        ((continuous_truncatedCauchyKernel (z := z) hδ).comp continuous_subtype_val)⟩

theorem integral_truncatedCauchyKernel_re_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂preBrolinMeasureAt c a n =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂preBrolinMeasureAtOnTargetEscapeDisk c a n := by
  rw [preBrolinMeasureAt_eq_map_preBrolinMeasureAtOnTargetEscapeDisk, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_re_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_re.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem integral_truncatedCauchyKernel_im_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a =
      ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
        ∂(brolinLimitAtOnTargetEscapeDisk c a :
          Measure (targetEscapeDisk c a)) := by
  rw [limitingBrolinMeasureAt, integral_map]
  · exact measurable_subtype_coe.aemeasurable
  · exact (Complex.continuous_im.comp
      (continuous_truncatedCauchyKernel (z := z) hδ)).aestronglyMeasurable

theorem truncatedCauchyKernel_re_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).re
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedCauchyKernelReOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedCauchyKernelReOnTargetEscapeDisk] using h

theorem truncatedCauchyKernel_im_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(preBrolinProbabilityAtOnTargetEscapeDisk c a
              (brolinLimitAtSubsequence c a k) :
            Measure (targetEscapeDisk c a)))
      atTop
      (𝓝 (∫ w : targetEscapeDisk c a, (truncatedCauchyKernel z δ (w : ℂ)).im
          ∂(brolinLimitAtOnTargetEscapeDisk c a :
            Measure (targetEscapeDisk c a)))) := by
  have h :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (preBrolinProbabilityAtOnTargetEscapeDisk_subseq_tendsto c a))
      (truncatedCauchyKernelImOnTargetEscapeDisk c a z δ hδ)
  simpa [truncatedCauchyKernelImOnTargetEscapeDisk] using h

theorem truncatedCauchyKernel_re_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedCauchyKernel_re_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedCauchyKernel_re_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_re_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  rfl

theorem truncatedCauchyKernel_im_preBrolinMeasureAt_subseq_integral_tendsto_limiting
    (c a z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun k =>
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k))
      atTop
      (𝓝 (∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a)) := by
  have h :=
    truncatedCauchyKernel_im_preBrolinProbabilityAtOnTargetEscapeDisk_subseq_integral_tendsto
      c a z hδ
  rw [integral_truncatedCauchyKernel_im_limitingBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with k _hk
  rw [integral_truncatedCauchyKernel_im_preBrolinMeasureAt_eq_integral_targetEscapeDisk
    c a z hδ]
  rfl

theorem eventually_cauchyIntegral_re_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) =
        ∫ w, (truncatedCauchyKernel z δ w).re
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem eventually_cauchyIntegral_im_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∀ᶠ k in atTop,
      ∫ w, ((z - w)⁻¹).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) =
        ∫ w, (truncatedCauchyKernel z δ w).im
          ∂preBrolinMeasureAt c a (brolinLimitAtSubsequence c a k) := by
  filter_upwards [eventually_preBrolinMeasureAt_subseq_greenSublevel_compl_of_pos
    c a hε] with k hk
  exact cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    hk hδ hsep

theorem cauchyIntegral_re_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).re ∂limitingBrolinMeasureAt c a =
      ∫ w, (truncatedCauchyKernel z δ w).re ∂limitingBrolinMeasureAt c a :=
  cauchyIntegral_re_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hδ hsep

theorem cauchyIntegral_im_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
    (c a z : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hsep : ∀ w : ℂ, w ∈ greenSublevel c ε → δ ≤ ‖z - w‖) :
    ∫ w, ((z - w)⁻¹).im ∂limitingBrolinMeasureAt c a =
      ∫ w, (truncatedCauchyKernel z δ w).im ∂limitingBrolinMeasureAt c a :=
  cauchyIntegral_im_eq_integral_truncatedCauchyKernel_of_greenSublevel_support
    (limitingBrolinMeasureAt_greenSublevel_compl_of_pos c a hε) hδ hsep

def HasSubseqCauchyTransformLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => ∫ w, ((z - w)⁻¹).re ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto (fun k => ∫ w, ((z - w)⁻¹).im ∂preBrolinMeasureAt c a (ψ k))
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt (c a : ℂ) :
    HasSubseqCauchyTransformLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hGne : greenFunctionDyn c z ≠ 0 := by
    intro hzero
    exact hz ((greenFunctionDyn_eq_zero_iff c z).mp hzero)
  have hGpos : 0 < greenFunctionDyn c z :=
    lt_of_le_of_ne (greenFunctionDyn_nonneg c z) (by simpa [eq_comm] using hGne)
  let ε : ℝ := greenFunctionDyn c z / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hεlt : ε < greenFunctionDyn c z := by
    dsimp [ε]
    linarith
  obtain ⟨δ, hδpos, hsep⟩ :=
    exists_pos_le_norm_of_greenSublevel_of_lt_green
      (c := c) (z := z) (ε := ε) hεlt
  have htruncRe :=
    truncatedCauchyKernel_re_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have htruncIm :=
    truncatedCauchyKernel_im_preBrolinMeasureAt_subseq_integral_tendsto_limiting
      c a z hδpos
  have hlimRe :=
    cauchyIntegral_re_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have hlimIm :=
    cauchyIntegral_im_limitingBrolinMeasureAt_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have heventRe :=
    eventually_cauchyIntegral_re_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  have heventIm :=
    eventually_cauchyIntegral_im_preBrolinMeasureAt_subseq_eq_integral_truncatedCauchyKernel
      c a z hεpos hδpos hsep
  constructor
  · rw [hlimRe]
    exact htruncRe.congr' (by
      filter_upwards [heventRe] with k hk
      exact hk.symm)
  · rw [hlimIm]
    exact htruncIm.congr' (by
      filter_upwards [heventIm] with k hk
      exact hk.symm)

theorem brolinMuOne_hasSubseqCauchyTransformLimitAt (c : ℂ) :
    HasSubseqCauchyTransformLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOne c) := by
  simpa [brolinMuOne] using
    limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt c 1

/-- The algebraic finite logarithmic derivatives converge, componentwise, to
the Cauchy transform of the limiting measure.  This is the bridge from the
finite pullback identity to the hDisc period kernel. -/
def HasSubseqNormalizedLogDerivativeLimitAt
    (c a : ℂ) (ψ : ℕ → ℕ) (μ : Measure ℂ) : Prop :=
  ∀ ⦃z : ℂ⦄, z ∉ filledJulia c →
    Tendsto (fun k => (finiteBrolinNormalizedLogDerivativeAt c a z (ψ k)).re)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).re ∂μ)) ∧
    Tendsto (fun k => (finiteBrolinNormalizedLogDerivativeAt c a z (ψ k)).im)
      atTop (𝓝 (∫ w, ((z - w)⁻¹).im ∂μ))

theorem eventually_finiteBrolinNormalizedLogDerivativeAt_subseq_valid
    {c a z : ℂ} (hz : z ∉ filledJulia c) :
    ∀ᶠ k in atTop,
      (quadratic c)^[brolinLimitAtSubsequence c a k] z - a ≠ 0 := by
  obtain ⟨N, hN⟩ :=
    eventually_atTop.1 (eventually_iterate_ne_of_not_mem_filledJulia hz a)
  filter_upwards [eventually_ge_atTop N] with k hk
  exact sub_ne_zero.mpr
    (hN (brolinLimitAtSubsequence c a k)
      (le_trans hk (le_brolinLimitAtSubsequence c a k)))

theorem limitingBrolinMeasureAt_hasSubseqNormalizedLogDerivativeLimitAt
    (c a : ℂ) :
    HasSubseqNormalizedLogDerivativeLimitAt c a (brolinLimitAtSubsequence c a)
      (limitingBrolinMeasureAt c a) := by
  intro z hz
  have hcauchy :=
    limitingBrolinMeasureAt_hasSubseqCauchyTransformLimitAt c a hz
  have hvalid := eventually_finiteBrolinNormalizedLogDerivativeAt_subseq_valid
    (c := c) (a := a) hz
  constructor
  · exact hcauchy.1.congr' (by
      filter_upwards [hvalid] with k hk
      exact integral_cauchy_re_preBrolinMeasureAt_eq_derivative_div hk)
  · exact hcauchy.2.congr' (by
      filter_upwards [hvalid] with k hk
      exact integral_cauchy_im_preBrolinMeasureAt_eq_derivative_div hk)

theorem brolinMuOne_hasSubseqNormalizedLogDerivativeLimitAt (c : ℂ) :
    HasSubseqNormalizedLogDerivativeLimitAt c 1 (brolinLimitAtSubsequence c 1)
      (brolinMuOne c) := by
  simpa [brolinMuOne] using
    limitingBrolinMeasureAt_hasSubseqNormalizedLogDerivativeLimitAt c 1

/-- Expanded hDisc-side analytic core for the constructed measure.  This is
the no-Riesz-interface package: probability/support, weak construction,
exterior potential, Cauchy-transform convergence, and finite logarithmic
derivative convergence. -/
theorem brolinMuOne_hDiscAnalyticCore (c : ℂ) :
    IsProbOn (brolinMuOne c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolinAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqLogPotentialLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqCauchyTransformLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      HasSubseqNormalizedLogDerivativeLimitAt c 1 (brolinLimitAtSubsequence c 1)
        (brolinMuOne c) ∧
      ∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (brolinMuOne c) z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuOne_hDiscCore c).1
  · exact (brolinMuOne_hDiscCore c).2.1
  · exact (brolinMuOne_hDiscCore c).2.2.1
  · exact brolinMuOne_hasSubseqCauchyTransformLimitAt c
  · exact brolinMuOne_hasSubseqNormalizedLogDerivativeLimitAt c
  · exact (brolinMuOne_hDiscCore c).2.2.2

/-- Full potential representation from the exterior logarithmic-kernel limit
and the zero-potential boundary condition on `K_c`. -/
theorem hasGreenPotentialRepresentation_of_subseqLogPotentialLimit
    {c : ℂ} {μ : Measure ℂ}
    (hpot : HasSubseqLogPotentialLimit c μ)
    (hK : ∀ z, z ∈ filledJulia c → - logPotential μ z = 0) :
    HasGreenPotentialRepresentation c μ := by
  rw [hasGreenPotentialRepresentation_iff]
  intro z
  by_cases hz : z ∈ filledJulia c
  · rw [(greenFunctionDyn_eq_zero_iff c z).mpr hz, hK z hz]
  · exact green_eq_neg_logPotential_on_basin_of_subseqLogPotentialLimit hpot hz

end Bottcher
