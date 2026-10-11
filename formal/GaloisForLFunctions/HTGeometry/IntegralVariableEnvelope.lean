import GaloisForLFunctions.HTGeometry.QuantileCoupling

/-! A nonnegative error dominated by a converging integrable envelope has vanishing integral. -/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem tendsto_integral_zero_of_variable_envelope
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {f g : ι → α → ℝ} {G : α → ℝ}
    (hfm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfnn : ∀ i, 0 ≤ᵐ[μ] f i) (hdom : ∀ i, f i ≤ᵐ[μ] g i)
    (hgi : ∀ i, Integrable (g i) μ) (hGi : Integrable G μ) (hGnn : 0 ≤ᵐ[μ] G)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 0))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (G x)))
    (hint : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 (∫ x, G x ∂μ))) :
    Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 0) := by
  have hgnn (i : ι) : 0 ≤ᵐ[μ] g i := (hfnn i).trans (hdom i)
  have hfi (i : ι) : Integrable (f i) μ := by
    apply (hgi i).mono' (hfm i)
    filter_upwards [hfnn i, hdom i] with x hx hdx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hdx
  let H (i : ι) (x : α) := min (f i x) (G x)
  have hHm (i : ι) : AEStronglyMeasurable (H i) μ :=
    ((hfm i).aemeasurable.min hGi.aemeasurable).aestronglyMeasurable
  have hHbound (i : ι) : ∀ᵐ x ∂μ, ‖H i x‖ ≤ G x := by
    filter_upwards [hfnn i, hGnn] with x hx hGx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx hGx)]
    exact min_le_right _ _
  have hHi (i : ι) : Integrable (H i) μ := hGi.mono' (hHm i) (hHbound i)
  have hHlim : Tendsto (fun i => ∫ x, H i x ∂μ) l (𝓝 0) := by
    have h : Tendsto (fun i => ∫ x, H i x ∂μ) l (𝓝 (∫ _ : α, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_filter_of_dominated_convergence G
        (Eventually.of_forall hHm) (Eventually.of_forall hHbound) hGi
      filter_upwards [hf, hGnn] with x hx hGx
      have h := hx.min (tendsto_const_nhds (x := G x))
      rw [min_eq_left (show (0 : ℝ) ≤ G x from hGx)] at h
      exact h
    simpa only [integral_zero] using h
  have hgap : Tendsto (fun i => ∫ x, |g i x - G x| ∂μ) l (𝓝 0) :=
    tendsto_integral_abs_sub_of_tendsto hgi hGi hgnn hGnn hg hint
  have hlim : Tendsto (fun i => (∫ x, |g i x - G x| ∂μ) + ∫ x, H i x ∂μ) l (𝓝 0) := by
    simpa only [add_zero] using hgap.add hHlim
  apply squeeze_zero (fun i => integral_nonneg_of_ae (hfnn i)) (fun i => ?_) hlim
  calc
    _ ≤ ∫ x, |g i x - G x| + H i x ∂μ := by
      apply integral_mono_ae (hfi i) (((hgi i).sub hGi).abs.add (hHi i))
      filter_upwards [hdom i] with x hx
      dsimp [H]
      by_cases hle : f i x ≤ G x
      · rw [min_eq_left hle]
        linarith only [abs_nonneg (g i x - G x)]
      · rw [min_eq_right (le_of_not_ge hle)]
        linarith only [le_abs_self (g i x - G x), hx]
    _ = _ := integral_add ((hgi i).sub hGi).abs (hHi i)

end GaloisForLFunctions.HTGeometry
