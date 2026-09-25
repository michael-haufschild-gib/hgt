import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv

open MeasureTheory Set Filter Complex Topology

noncomputable def realCauchyTransform (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (z + (t : ℂ))⁻¹ ∂μ

theorem differentiableAt_realCauchyTransform_offReal
    (μ : Measure ℝ) [IsFiniteMeasure μ] {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) :
    DifferentiableAt ℂ (realCauchyTransform μ) z₀ := by
  let δ : ℝ := |z₀.im| / 2
  have hδ : 0 < δ := by dsimp [δ]; have := abs_pos.mpr hz₀; linarith
  let s : Set ℂ := {z | δ < |z.im|}
  have hsOpen : IsOpen s :=
    isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)
  have hs₀ : z₀ ∈ s := by
    dsimp [s, δ]
    have := abs_pos.mpr hz₀
    linarith
  have hs : s ∈ 𝓝 z₀ := hsOpen.mem_nhds hs₀
  let F : ℂ → ℝ → ℂ := fun z t => (z + (t : ℂ))⁻¹
  let F' : ℂ → ℝ → ℂ := fun z t => -((z + (t : ℂ)) ^ 2)⁻¹
  have hnorm (z : ℂ) (hz : z ∈ s) (t : ℝ) :
      δ ≤ ‖z + (t : ℂ)‖ := by
    have him : (z + (t : ℂ)).im = z.im := by simp
    have hle : |z.im| ≤ ‖z + (t : ℂ)‖ := by
      simpa only [him] using Complex.abs_im_le_norm (z + (t : ℂ))
    exact (le_of_lt hz).trans hle
  have hnonzero (z : ℂ) (hz : z ∈ s) (t : ℝ) :
      z + (t : ℂ) ≠ 0 := by
    intro hzero
    have hzeroNorm : ‖z + (t : ℂ)‖ = 0 := by rw [hzero]; simp
    have := hnorm z hz t
    linarith
  have hFmeas : ∀ᶠ z : ℂ in 𝓝 z₀, AEStronglyMeasurable (F z) μ := by
    filter_upwards with z
    exact (show Measurable (F z) by dsimp [F]; fun_prop).aestronglyMeasurable
  have hFint : Integrable (F z₀) μ := by
    refine Integrable.of_bound
      (show AEStronglyMeasurable (F z₀) μ from
        (show Measurable (F z₀) by dsimp [F]; fun_prop).aestronglyMeasurable)
      δ⁻¹ (Eventually.of_forall fun t => ?_)
    have hn := hnorm z₀ hs₀ t
    have hpos : 0 < ‖z₀ + (t : ℂ)‖ := lt_of_lt_of_le hδ hn
    change ‖(z₀ + (t : ℂ))⁻¹‖ ≤ δ⁻¹
    rw [norm_inv]
    exact (inv_le_inv₀ hpos hδ).2 hn
  have hF'meas : AEStronglyMeasurable (F' z₀) μ :=
    (show Measurable (F' z₀) by dsimp [F']; fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ t : ℝ ∂μ, ∀ z ∈ s, ‖F' z t‖ ≤ (δ ^ 2)⁻¹ := by
    filter_upwards with t z hz
    have hn := hnorm z hz t
    have hnpos : 0 < ‖z + (t : ℂ)‖ := lt_of_lt_of_le hδ hn
    have hsq : δ ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ hδ.le hn 2
    have hinv := (inv_le_inv₀ (pow_pos hnpos 2) (pow_pos hδ 2)).2 hsq
    simpa only [F', norm_neg, norm_inv, norm_pow] using hinv
  have hboundInt : Integrable (fun _ : ℝ => (δ ^ 2)⁻¹) μ := integrable_const _
  have hderiv : ∀ᵐ t : ℝ ∂μ, ∀ z ∈ s,
      HasDerivAt (fun w => F w t) (F' z t) z := by
    filter_upwards with t z hz
    have hlin : HasDerivAt (fun w : ℂ => w + (t : ℂ)) 1 z :=
      (hasDerivAt_id z).add_const (t : ℂ)
    convert (hasDerivAt_inv (hnonzero z hz t)).comp z hlin using 1
    all_goals first | rfl | simp [F, F']
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => (δ ^ 2)⁻¹)
    hs hFmeas hFint hF'meas hbound hboundInt hderiv
  exact hmain.2.differentiableAt
