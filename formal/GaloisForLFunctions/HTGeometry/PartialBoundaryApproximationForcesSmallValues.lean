import GaloisForLFunctions.HTGeometry.LogQuotientDerivativeCeiling

/-!
# Partial boundary approximation forces small values

Suppose `f` vanishes at the centre of a disc and `g` approximates `f` relatively on all
but a short boundary arc. Either `g` has a zero in the disc, or the omitted arc carries
a definite logarithmic reciprocal mass and an exponentially deep relative small value.

The proof applies Jensen's inequality to `1 - f/g`, whose central value is one.
No counting estimate for zeros is involved.
-/

open Complex Metric Real Filter Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The logarithmic reciprocal size of `g` relative to `f` along a circle. -/
def reciprocalGapLog (f g : ℂ → ℂ) (c : ℂ) (R θ : ℝ) : ℝ :=
  Real.log (1 + ‖f (circleMap c R θ)‖ / ‖g (circleMap c R θ)‖)

private theorem continuous_reciprocalGapLog {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0) :
    Continuous (reciprocalGapLog f g c R) := by
  have hm (θ : ℝ) : circleMap c R θ ∈ closedBall c R :=
    sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)
  have hfc : Continuous (fun θ => f (circleMap c R θ)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (hf _ (hm θ)).continuousAt.comp (continuous_circleMap c R).continuousAt
  have hgc : Continuous (fun θ => g (circleMap c R θ)) :=
    continuous_iff_continuousAt.mpr fun θ =>
      (hg _ (hm θ)).continuousAt.comp (continuous_circleMap c R).continuousAt
  have hc : Continuous (fun θ =>
      1 + ‖f (circleMap c R θ)‖ / ‖g (circleMap c R θ)‖) :=
    continuous_const.add (hfc.norm.div hgc.norm
      (fun θ => norm_ne_zero_iff.mpr (hg0 _ (hm θ))))
  exact hc.log (fun θ => ne_of_gt (by positivity))

private theorem analytic_circleMap_ae_ne_zero {q : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hq : AnalyticOnNhd ℂ q (closedBall c R)) (hqc : q c ≠ 0)
    (a b : ℝ) :
    ∀ᵐ θ ∂volume.restrict (Icc a b), q (circleMap c R θ) ≠ 0 := by
  have hd := hq.preimage_zero_mem_codiscreteWithin hqc
    (mem_closedBall_self hR.le) (isConnected_closedBall hR.le)
  have hs : q ⁻¹' {0}ᶜ ∈ codiscreteWithin (sphere c |R|) := by
    rw [abs_of_pos hR]
    exact codiscreteWithin_mono sphere_subset_closedBall hd
  exact ae_restrict_le_codiscreteWithin measurableSet_Icc
    (codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete hR.ne' hs))

/-- A zero-free approximant must pay for long-arc accuracy with logarithmic reciprocal
mass on the omitted arc. Boundary zeros of the relative error are removed only almost
everywhere; no boundary nonvanishing assumption on that error is needed. -/
theorem shortArc_reciprocal_budget {f g : ℂ → ℂ} {c : ℂ} {R δ η : ℝ}
    (hR : 0 < R) (hδ : 0 ≤ δ) (hδπ : δ ≤ 2 * π) (_hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfc : f c = 0)
    (hg0 : ∀ z ∈ closedBall c R, g z ≠ 0)
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖g (circleMap c R θ) - f (circleMap c R θ)‖ ≤ η * ‖g (circleMap c R θ)‖) :
    -(2 * π - δ) * Real.log η ≤ ∫ θ in 0..δ, reciprocalGapLog f g c R θ := by
  let q : ℂ → ℂ := fun z => 1 - f z / g z
  have hq : AnalyticOnNhd ℂ q (closedBall c R) :=
    analyticOnNhd_const.sub (hf.div hg hg0)
  have hqc : q c = 1 := by simp [q, hfc]
  have hqc0 : q c ≠ 0 := by rw [hqc]; exact one_ne_zero
  have hm (θ : ℝ) : circleMap c R θ ∈ closedBall c R :=
    sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)
  have hi : IntervalIntegrable (fun θ => Real.log ‖q (circleMap c R θ)‖)
      volume 0 (2 * π) := by
    apply MeromorphicOn.circleIntegrable_log_norm
    rw [abs_of_pos hR]
    exact (hq.mono sphere_subset_closedBall).meromorphicOn
  have his := hi.mono_set (show uIcc 0 δ ⊆ uIcc 0 (2 * π) by
    rw [uIcc_of_le hδ, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact Icc_subset_Icc le_rfl hδπ)
  have hil := hi.mono_set (show uIcc δ (2 * π) ⊆ uIcc 0 (2 * π) by
    rw [uIcc_of_le hδπ, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
    exact Icc_subset_Icc hδ le_rfl)
  have hj := log_norm_le_circleAverage_log_norm hR hq hqc0
  rw [hqc, norm_one, Real.log_one, circleAverage_def, smul_eq_mul] at hj
  have hj' : 0 ≤ ∫ θ in 0..2 * π, Real.log ‖q (circleMap c R θ)‖ := by
    exact nonneg_of_mul_nonneg_right hj (by positivity : 0 < (2 * π)⁻¹)
  have hlong : (∫ θ in δ..2 * π, Real.log ‖q (circleMap c R θ)‖) ≤
      (2 * π - δ) * Real.log η := by
    have hb : (fun θ => Real.log ‖q (circleMap c R θ)‖) ≤ᵐ[volume.restrict
        (Icc δ (2 * π))] (fun _ => Real.log η) := by
      filter_upwards [analytic_circleMap_ae_ne_zero hR hq hqc0 δ (2 * π),
        ae_restrict_mem measurableSet_Icc] with θ hne hθ
      apply Real.log_le_log (norm_pos_iff.mpr hne)
      have hgz := hg0 _ (hm θ)
      calc
        ‖q (circleMap c R θ)‖ =
            ‖g (circleMap c R θ) - f (circleMap c R θ)‖ /
              ‖g (circleMap c R θ)‖ := by
          dsimp [q]
          rw [← norm_div, sub_div, div_self hgz]
        _ ≤ η := (div_le_iff₀ (norm_pos_iff.mpr hgz)).mpr (hreturn θ hθ)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_ae_restrict hδπ hil intervalIntegrable_const hb
  have hshort : (∫ θ in 0..δ, Real.log ‖q (circleMap c R θ)‖) ≤
      ∫ θ in 0..δ, reciprocalGapLog f g c R θ := by
    apply intervalIntegral.integral_mono_on hδ his
      ((continuous_reciprocalGapLog hR hf hg hg0).intervalIntegrable 0 δ)
    intro θ _
    have hnorm : ‖q (circleMap c R θ)‖ ≤
        1 + ‖f (circleMap c R θ)‖ / ‖g (circleMap c R θ)‖ := by
      simpa only [q, norm_one, norm_div] using
        norm_sub_le (1 : ℂ) (f (circleMap c R θ) / g (circleMap c R θ))
    by_cases hzero : q (circleMap c R θ) = 0
    · simp only [hzero, norm_zero, Real.log_zero]
      exact Real.log_nonneg (le_add_of_nonneg_right
        (div_nonneg (norm_nonneg _) (norm_nonneg _)))
    · exact Real.log_le_log (norm_pos_iff.mpr hzero) hnorm
  have hsplit := intervalIntegral.integral_add_adjacent_intervals his hil
  linarith

/-- Long-arc relative approximation yields a zero in the disc or an exact reciprocal
mass lower bound on the missing arc. -/
theorem zero_or_shortArc_reciprocal_budget {f g : ℂ → ℂ} {c : ℂ} {R δ η : ℝ}
    (hR : 0 < R) (hδ : 0 ≤ δ) (hδπ : δ ≤ 2 * π) (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfc : f c = 0)
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖g (circleMap c R θ) - f (circleMap c R θ)‖ ≤ η * ‖g (circleMap c R θ)‖) :
    (∃ z ∈ closedBall c R, g z = 0) ∨
      -(2 * π - δ) * Real.log η ≤ ∫ θ in 0..δ, reciprocalGapLog f g c R θ := by
  by_cases hz : ∃ z ∈ closedBall c R, g z = 0
  · exact Or.inl hz
  · exact Or.inr (shortArc_reciprocal_budget hR hδ hδπ hη hf hg hfc
      (fun z hz' hzero => hz ⟨z, hz', hzero⟩) hreturn)

/-- A zero-free return has an exponentially deep relative small value somewhere on
the missing arc. The exponent is the long-to-short arc ratio times the log accuracy. -/
theorem zero_or_shortArc_small_value {f g : ℂ → ℂ} {c : ℂ} {R δ η : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hδπ : δ ≤ 2 * π) (hη : 0 < η)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hfc : f c = 0)
    (hreturn : ∀ θ ∈ Icc δ (2 * π),
      ‖g (circleMap c R θ) - f (circleMap c R θ)‖ ≤ η * ‖g (circleMap c R θ)‖) :
    (∃ z ∈ closedBall c R, g z = 0) ∨
      ∃ θ ∈ Icc 0 δ,
        (Real.exp (-(2 * π - δ) * Real.log η / δ) - 1) *
          ‖g (circleMap c R θ)‖ ≤ ‖f (circleMap c R θ)‖ := by
  by_cases hz : ∃ z ∈ closedBall c R, g z = 0
  · exact Or.inl hz
  have hg0 : ∀ z ∈ closedBall c R, g z ≠ 0 :=
    fun z hz' hzero => hz ⟨z, hz', hzero⟩
  have hc := continuous_reciprocalGapLog hR hf hg hg0
  obtain ⟨θ, hθ, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hδ.le) hc.continuousOn
  have hb := shortArc_reciprocal_budget hR hδ.le hδπ hη hf hg hfc hg0 hreturn
  have hi : (∫ t in 0..δ, reciprocalGapLog f g c R t) ≤
      δ * reciprocalGapLog f g c R θ := by
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using
      intervalIntegral.integral_mono_on hδ.le (hc.intervalIntegrable (μ := volume) 0 δ)
        intervalIntegrable_const (fun t ht => hmax ht)
  have hk : -(2 * π - δ) * Real.log η / δ ≤ reciprocalGapLog f g c R θ :=
    (div_le_iff₀ hδ).mpr (by nlinarith [hb.trans hi])
  have hpos : 0 < 1 + ‖f (circleMap c R θ)‖ / ‖g (circleMap c R θ)‖ := by positivity
  have he := Real.exp_le_exp.mpr hk
  rw [reciprocalGapLog, Real.exp_log hpos] at he
  have hgz : 0 < ‖g (circleMap c R θ)‖ := norm_pos_iff.mpr
    (hg0 _ (sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)))
  exact Or.inr ⟨θ, hθ, (le_div_iff₀ hgz).mp (by linarith [he])⟩

#print axioms zero_or_shortArc_reciprocal_budget
#print axioms zero_or_shortArc_small_value

end GaloisForLFunctions.HTGeometry
