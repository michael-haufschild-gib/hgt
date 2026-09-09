import GaloisForLFunctions.RHTower.FokasLenellsCausalSharpComplexResolvent

/-! Strong decay of the actual causal Cauchy completion, proved from its dense rational eigenvectors.
The operator norm remains one, so this decay is specific to each fixed input. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Exact exponential norm decay of each actual rational Cauchy eigenvector. -/
theorem causalCauchyEigenvector_orbit_norm (t : ℝ≥0) (w : {z : ℂ // 0 < z.im}) :
    ‖causalLowerCauchyEvolution t (causalCauchyEigenvector w)‖ =
      Real.exp ((t : ℝ)*(causalPoleRate w.val).re) * ‖causalCauchyEigenvector w‖ := by
  rw [causalLowerCauchyEvolution_eigenvector, norm_smul, causalAnalyticPhase_rate, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Every actual rational Cauchy eigenvector decays to zero under the completed causal evolution. -/
theorem causalCauchyEigenvector_orbit_tendsto (w : {z : ℂ // 0 < z.im}) :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t (causalCauchyEigenvector w))
      atTop (𝓝 0) := by
  have hc := causalPoleRate_re_neg w
  have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
  have he : Tendsto (fun t : ℝ≥0 => Real.exp ((t : ℝ)*(causalPoleRate w.val).re)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop (neg_pos.mpr hc) ht) using 1
    funext t
    simp only [Function.comp_apply]
    ring
  have hn : Tendsto (fun t : ℝ≥0 =>
      Real.exp ((t : ℝ)*(causalPoleRate w.val).re)*‖causalCauchyEigenvector w‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul_const ‖causalCauchyEigenvector w‖
  exact squeeze_zero_norm' (Eventually.of_forall (fun t => (causalCauchyEigenvector_orbit_norm t w).le)) hn

private theorem rational_span_orbit_tendsto (u : hardyL2ᗮ)
    (hu : u ∈ Submodule.span ℂ (Set.range causalCauchyEigenvector)) :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t u) atTop (𝓝 0) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    exact causalCauchyEigenvector_orbit_tendsto w
  | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : hardyL2ᗮ)) atTop (𝓝 0))
  | add u v _ _ ihu ihv => simpa only [map_add, add_zero] using ihu.add ihv
  | smul c u _ ihu => simpa only [map_smul, smul_zero] using ihu.const_smul c

/-- Every fixed completed lower Hardy input tends to zero under the actual causal semigroup. -/
theorem causalLowerCauchyEvolution_strong_tendsto (u : hardyL2ᗮ) :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t u) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hd : u ∈ closure (Submodule.span ℂ (Set.range causalCauchyEigenvector) : Set (hardyL2ᗮ)) := by
    rw [← Submodule.topologicalClosure_coe, topologicalClosure_span_causalCauchyEigenvector_eq_top]
    trivial
  obtain ⟨v, hv, huv⟩ := Metric.mem_closure_iff.1 hd (ε/2) (half_pos hε)
  have hvsmall := Metric.tendsto_nhds.1 (rational_span_orbit_tendsto v hv) (ε/2) (half_pos hε)
  filter_upwards [hvsmall] with t ht
  rw [dist_zero_right] at ht ⊢
  rw [dist_eq_norm] at huv
  have he : causalLowerCauchyEvolution t u =
      causalLowerCauchyEvolution t (u-v) + causalLowerCauchyEvolution t v := by
    rw [map_sub, sub_add_cancel]
  have hsmall : ‖causalLowerCauchyEvolution t (u-v)‖ < ε/2 :=
    lt_of_le_of_lt (causalLowerCauchyEvolution_norm_le t (u-v)) huv
  have hb := (norm_add_le (causalLowerCauchyEvolution t (u-v))
    (causalLowerCauchyEvolution t v)).trans_lt (add_lt_add hsmall ht)
  rw [← he, add_halves] at hb
  exact hb

/-- The actual causal operators do not tend to zero in operator norm, despite decay of every input. -/
theorem causalLowerCauchyEvolution_not_norm_tendsto :
    ¬ Tendsto (fun t : ℝ≥0 => ‖causalLowerCauchyEvolution t‖) atTop (𝓝 (0 : ℝ)) := by
  simp only [norm_causalLowerCauchyEvolution]
  intro h
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  exact one_ne_zero he

end
end RHTower.FokasLenells
