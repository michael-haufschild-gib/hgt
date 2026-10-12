import GaloisForLFunctions.HTGeometry.IntegralVariableEnvelope

/-! Convergence of real integrals under a varying, converging integrable envelope. -/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem tendsto_integral_abs_sub_of_variable_envelope
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {f g : ι → α → ℝ} {F G : α → ℝ}
    (hfi : ∀ i, Integrable (f i) μ) (hFi : Integrable F μ)
    (hdom : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ g i x)
    (hgi : ∀ i, Integrable (g i) μ) (hGi : Integrable G μ) (hGnn : 0 ≤ᵐ[μ] G)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (F x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (G x)))
    (hint : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 (∫ x, G x ∂μ))) :
    Tendsto (fun i => ∫ x, |f i x - F x| ∂μ) l (𝓝 0) := by
  apply tendsto_integral_zero_of_variable_envelope
    (g := fun i x => g i x + |F x|) (G := fun x => G x + |F x|)
  · exact fun i => ((hfi i).sub hFi).abs.aestronglyMeasurable
  · exact fun _ => Eventually.of_forall fun _ => abs_nonneg _
  · intro i
    filter_upwards [hdom i] with x hx
    have hx' : |f i x| ≤ g i x := by simpa only [Real.norm_eq_abs] using hx
    linarith only [abs_sub (f i x) (F x), hx']
  · exact fun i => (hgi i).add hFi.abs
  · exact hGi.add hFi.abs
  · exact hGnn.mono fun x hx => add_nonneg hx (abs_nonneg _)
  · filter_upwards [hf] with x hx
    simpa only [sub_self, abs_zero] using (hx.sub (tendsto_const_nhds (x := F x))).abs
  · exact hg.mono fun _ hx => hx.add_const _
  · simp_rw [integral_add (hgi _) hFi.abs, integral_add hGi hFi.abs]
    exact hint.add_const _

theorem tendsto_integral_of_variable_envelope
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {f g : ι → α → ℝ} {F G : α → ℝ}
    (hfi : ∀ i, Integrable (f i) μ) (hFi : Integrable F μ)
    (hdom : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ g i x)
    (hgi : ∀ i, Integrable (g i) μ) (hGi : Integrable G μ) (hGnn : 0 ≤ᵐ[μ] G)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (F x)))
    (hg : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (G x)))
    (hint : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 (∫ x, G x ∂μ))) :
    Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 (∫ x, F x ∂μ)) := by
  have h := tendsto_integral_abs_sub_of_variable_envelope hfi hFi hdom hgi hGi hGnn hf hg hint
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun i => ?_) h
  rw [dist_eq_norm, ← integral_sub (hfi i) hFi]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f i x - F x)

end GaloisForLFunctions.HTGeometry
