import GaloisForLFunctions.HTGeometry.HillBoundsTwoSided

/-!
# Stability in the frequency, in both time directions

The comparison of two Hill flows was proved forward in time. Reversing the time variable in the
difference alone gives the backward half, exactly as for the energy: the differential inequality the
difference satisfies is invariant under `t ↦ -t`.

With that, the fibre is continuous in the spatial frequency at every time, not only at nonnegative
ones — the form the synthesis needs on a two-sided neighbourhood of an event.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Metric

section Backward

variable {ω₁ ω₂ : ℝ → ℝ} {M δ b : ℝ}

/-- **The comparison of two flows, backward in time.** -/
theorem norm_hillFlow_sub_le_neg (hω₁ : Continuous ω₁) (hω₂ : Continuous ω₂) (hM1 : 1 ≤ M)
    (hM₁ : ∀ s, ω₁ s ^ 2 ≤ M) (hM₂ : ∀ s, ω₂ s ^ 2 ≤ M)
    (hδ : ∀ s, |ω₁ s ^ 2 - ω₂ s ^ 2| ≤ δ) (hδ0 : 0 ≤ δ) (y₀ : ℝ × ℝ)
    {t : ℝ} (ht : t ∈ Icc (-b) 0) :
    ‖hillFlow ω₁ y₀ t - hillFlow ω₂ y₀ t‖ ≤
      gronwallBound 0 M (δ * (‖y₀‖ * Real.exp (M * b))) (-t) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hd₁ := fun s => hasDerivAt_hillFlow hω₁ hM1 hM₁ y₀ s
  have hd₂ := fun s => hasDerivAt_hillFlow hω₂ hM1 hM₂ y₀ s
  set F : ℝ → ℝ × ℝ := fun s => hillFlow ω₁ y₀ (-s) - hillFlow ω₂ y₀ (-s) with hF
  have hFderiv : ∀ s : ℝ, HasDerivAt F
      (-(hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s)) - hillField ω₂ (-s) (hillFlow ω₂ y₀ (-s)))) s := by
    intro s
    have hbase := (hd₁ (-s)).sub (hd₂ (-s))
    have hcomp := HasDerivAt.scomp s hbase (hasDerivAt_neg s)
    have hval : (-1 : ℝ) • (hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s)) -
        hillField ω₂ (-s) (hillFlow ω₂ y₀ (-s)))
        = -(hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s)) -
            hillField ω₂ (-s) (hillFlow ω₂ y₀ (-s))) := by
      simp
    rw [hval] at hcomp
    exact hcomp
  have hsize : ∀ s ∈ Icc (0 : ℝ) b, ‖hillFlow ω₂ y₀ (-s)‖ ≤ ‖y₀‖ * Real.exp (M * b) := by
    intro s hs
    have hbase := norm_volterraSolution_le (f := fun _ : ℝ => y₀)
      (K := fun _ r => hillField ω₂ r) continuous_const (continuous_hillField hω₂) hM0
      (norm_nonneg y₀) (fun _ r => norm_hillField_le hM1 hM₂ r) (fun _ => le_rfl) (-s)
    have habs : |(-s)| ≤ b := by
      rw [abs_neg, abs_of_nonneg hs.1]
      exact hs.2
    have hexp : Real.exp (M * |(-s)|) ≤ Real.exp (M * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hM0)
    calc ‖hillFlow ω₂ y₀ (-s)‖ ≤ ‖y₀‖ * Real.exp (M * |(-s)|) := hbase
      _ ≤ ‖y₀‖ * Real.exp (M * b) := mul_le_mul_of_nonneg_left hexp (norm_nonneg y₀)
  have hbound : ∀ s ∈ Ico (0 : ℝ) b,
      ‖-(hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s)) -
          hillField ω₂ (-s) (hillFlow ω₂ y₀ (-s)))‖ ≤
        M * ‖F s‖ + δ * (‖y₀‖ * Real.exp (M * b)) := by
    intro s hs
    rw [norm_neg]
    have hsplit : hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s)) -
        hillField ω₂ (-s) (hillFlow ω₂ y₀ (-s))
        = hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s) - hillFlow ω₂ y₀ (-s))
          + (hillField ω₁ (-s) - hillField ω₂ (-s)) (hillFlow ω₂ y₀ (-s)) := by
      simp [ContinuousLinearMap.map_sub]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h₁ : ‖hillField ω₁ (-s) (hillFlow ω₁ y₀ (-s) - hillFlow ω₂ y₀ (-s))‖ ≤ M * ‖F s‖ := by
      refine ((hillField ω₁ (-s)).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right (norm_hillField_le hM1 hM₁ (-s)) (norm_nonneg _)
    have h₂ : ‖(hillField ω₁ (-s) - hillField ω₂ (-s)) (hillFlow ω₂ y₀ (-s))‖
        ≤ δ * (‖y₀‖ * Real.exp (M * b)) := by
      refine ((hillField ω₁ (-s) - hillField ω₂ (-s)).le_opNorm _).trans ?_
      have hsz := hsize s ⟨hs.1, le_of_lt hs.2⟩
      have hop := norm_hillField_sub_le hδ hδ0 (-s)
      have hnn : (0 : ℝ) ≤ ‖hillFlow ω₂ y₀ (-s)‖ := norm_nonneg _
      nlinarith [norm_nonneg (hillFlow ω₂ y₀ (-s)), mul_nonneg hδ0 hnn]
    linarith
  have hcont : ContinuousOn F (Icc 0 b) := fun s _ =>
    ((hFderiv s).continuousAt).continuousWithinAt
  have hzero : ‖F 0‖ ≤ 0 := by
    have h0 : F 0 = hillFlow ω₁ y₀ 0 - hillFlow ω₂ y₀ 0 := by
      rw [hF]
      simp
    rw [h0, hillFlow_zero hω₁ hM1 hM₁, hillFlow_zero hω₂ hM1 hM₂, sub_self, norm_zero]
  have hmem : (-t) ∈ Icc (0 : ℝ) b := by
    constructor
    · linarith [ht.2]
    · have := ht.1
      linarith
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hFderiv s).hasDerivWithinAt) hzero hbound (-t) hmem
  have hFt : F (-t) = hillFlow ω₁ y₀ t - hillFlow ω₂ y₀ t := by
    rw [hF]
    simp
  rw [hFt] at hgron
  simpa using hgron

/-- **The comparison of two flows, in both directions.** -/
theorem norm_hillFlow_sub_le_abs (hω₁ : Continuous ω₁) (hω₂ : Continuous ω₂) (hM1 : 1 ≤ M)
    (hM₁ : ∀ s, ω₁ s ^ 2 ≤ M) (hM₂ : ∀ s, ω₂ s ^ 2 ≤ M)
    (hδ : ∀ s, |ω₁ s ^ 2 - ω₂ s ^ 2| ≤ δ) (hδ0 : 0 ≤ δ) (y₀ : ℝ × ℝ) {t : ℝ} (hb : |t| ≤ b) :
    ‖hillFlow ω₁ y₀ t - hillFlow ω₂ y₀ t‖ ≤
      gronwallBound 0 M (δ * (‖y₀‖ * Real.exp (M * b))) |t| := by
  rcases le_or_gt 0 t with htpos | htneg
  · have hmem : t ∈ Icc (0 : ℝ) b := ⟨htpos, by rwa [abs_of_nonneg htpos] at hb⟩
    have h := norm_hillFlow_sub_le hω₁ hω₂ hM1 hM₁ hM₂ hδ hδ0 y₀ hmem
    rwa [abs_of_nonneg htpos]
  · have hmem : t ∈ Icc (-b) 0 := by
      constructor
      · have : -t ≤ b := by rwa [abs_of_neg htneg] at hb
        linarith
      · exact le_of_lt htneg
    have h := norm_hillFlow_sub_le_neg hω₁ hω₂ hM1 hM₁ hM₂ hδ hδ0 y₀ hmem
    rwa [abs_of_neg htneg]

end Backward

section MassiveContinuity

variable {c : ℝ → ℝ} {m C : ℝ}

/-- **The massive fibre is continuous in the spatial frequency at every time.** -/
theorem continuousAt_hillFlow_massive_all (hm : 0 < m) (hc : Continuous c)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (y₀ : ℝ × ℝ) (t : ℝ) (s₀ : ℝ) :
    ContinuousAt (fun s => hillFlow (massiveFreq m c s) y₀ t) s₀ := by
  set S : ℝ := |s₀| + 1 with hSdef
  have hs₀ : s₀ ^ 2 ≤ S ^ 2 := by
    have h1 : |s₀| ≤ S := by simp [hSdef]
    nlinarith [sq_abs s₀, abs_nonneg s₀]
  set M : ℝ := max 1 (m ^ 2 + C ^ 2 * S ^ 2) with hM
  set b : ℝ := |t| with hb
  set B : ℝ := ‖y₀‖ * Real.exp (M * b) with hB
  have hnear : ∀ᶠ s in nhds s₀, s ^ 2 ≤ S ^ 2 := by
    refine Filter.eventually_of_mem (ball_mem_nhds s₀ one_pos) fun s hs => ?_
    have hdist : |s - s₀| < 1 := by simpa [Real.dist_eq] using hs
    have hpair := abs_lt.mp hdist
    have habs : |s| ≤ S := by
      cases abs_cases s with
      | inl h => rw [hSdef]; cases abs_cases s₀ with
        | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
        | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
      | inr h => rw [hSdef]; cases abs_cases s₀ with
        | inl h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
        | inr h2 => linarith [h.1, h2.1, hpair.1, hpair.2]
    nlinarith [sq_abs s, abs_nonneg s]
  have hle : ∀ᶠ s in nhds s₀,
      dist (hillFlow (massiveFreq m c s) y₀ t) (hillFlow (massiveFreq m c s₀) y₀ t) ≤
        gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t| := by
    filter_upwards [hnear] with s hs
    rw [dist_eq_norm]
    have hδ : ∀ r, |massiveFreq m c s r ^ 2 - massiveFreq m c s₀ r ^ 2|
        ≤ C ^ 2 * |s ^ 2 - s₀ ^ 2| := by
      intro r
      rw [massiveFreq_sq hm, massiveFreq_sq hm]
      have hfac : m ^ 2 + (c r * s) ^ 2 - (m ^ 2 + (c r * s₀) ^ 2)
          = c r ^ 2 * (s ^ 2 - s₀ ^ 2) := by ring
      rw [hfac, abs_mul, abs_of_nonneg (sq_nonneg (c r))]
      exact mul_le_mul_of_nonneg_right (hC r) (abs_nonneg _)
    exact norm_hillFlow_sub_le_abs (continuous_massiveFreq hc m s)
      (continuous_massiveFreq hc m s₀) (le_max_left _ _)
      (fun r => (massiveFreq_sq_le hm hC hs r).trans (le_max_right _ _))
      (fun r => (massiveFreq_sq_le hm hC hs₀ r).trans (le_max_right _ _)) hδ
      (mul_nonneg (sq_nonneg _) (abs_nonneg _)) y₀ le_rfl
  have hzero : Filter.Tendsto
      (fun s => gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t|) (nhds s₀) (nhds 0) := by
    have hcontε : Continuous fun ε : ℝ => gronwallBound 0 M ε |t| :=
      gronwallBound_continuous_ε 0 M |t|
    have hmap : Filter.Tendsto (fun s : ℝ => C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) (nhds s₀) (nhds 0) := by
      have hcont : Continuous fun s : ℝ => C ^ 2 * |s ^ 2 - s₀ ^ 2| * B := by fun_prop
      simpa using hcont.tendsto s₀
    have hcomp := (hcontε.tendsto 0).comp hmap
    have hval : ((fun ε : ℝ => gronwallBound 0 M ε |t|) ∘
        fun s : ℝ => C ^ 2 * |s ^ 2 - s₀ ^ 2| * B)
        = fun s : ℝ => gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t| := rfl
    rw [hval] at hcomp
    simpa [gronwallBound_ε0_δ0] using hcomp
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hzero' := Metric.tendsto_nhds.mp hzero ε hε
  filter_upwards [hle, hzero'] with s hs hz
  have habs : abs (gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t|) < ε := by
    simpa [Real.dist_eq] using hz
  calc dist (hillFlow (massiveFreq m c s) y₀ t) (hillFlow (massiveFreq m c s₀) y₀ t)
      ≤ gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t| := hs
    _ ≤ abs (gronwallBound 0 M (C ^ 2 * |s ^ 2 - s₀ ^ 2| * B) |t|) := le_abs_self _
    _ < ε := habs

end MassiveContinuity

end GaloisForLFunctions.HTGeometry
