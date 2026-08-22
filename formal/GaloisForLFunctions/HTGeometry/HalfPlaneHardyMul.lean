import GaloisForLFunctions.HTGeometry.HalfPlaneHardy

/-!
# Bounded holomorphic multipliers of the Hardy space of a half-plane

Multiplying by a function holomorphic and bounded on the right half-plane keeps a Hardy function in
the Hardy space and multiplies the mass bound by the square of the bound.  This is the mechanism by
which Burnol divides by `s`, by `s - w`, or by `(s-1)/s` inside `A^s H²` (arXiv:math/0203120, §4).

## Main results

* `isHalfPlaneHardy_mul_of_bounded`
* `isHalfPlaneHardy_add`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

/-- **A bounded holomorphic multiplier preserves the Hardy space.** -/
theorem isHalfPlaneHardy_mul_of_bounded {F g : ℂ → ℂ} {M C : ℝ} (hF : IsHalfPlaneHardy F M)
    (hg : DifferentiableOn ℂ g {w : ℂ | 0 < w.re})
    (hgb : ∀ w : ℂ, 0 < w.re → ‖g w‖ ≤ C) :
    IsHalfPlaneHardy (fun w => F w * g w) (C ^ 2 * M) where
  holo := hF.holo.mul hg
  memLp := by
    intro σ hσ
    have hmem := hF.memLp σ hσ
    have hcont : ContinuousOn g {w : ℂ | 0 < w.re} := hg.continuousOn
    have hmap : Continuous fun ξ : ℝ => rayLine σ ξ := by
      unfold rayLine
      fun_prop
    have hgmeas : Continuous fun ξ : ℝ => g (rayLine σ ξ) := by
      refine hcont.comp_continuous hmap (fun ξ => ?_)
      simpa using hσ
    have hdom : MemLp (fun ξ : ℝ => C * ‖F (rayLine σ ξ)‖) 2 volume :=
      (hmem.norm).const_mul C
    refine MemLp.mono' hdom ?_ ?_
    · exact hmem.aestronglyMeasurable.mul hgmeas.aestronglyMeasurable
    · filter_upwards with ξ
      have hb : ‖g (rayLine σ ξ)‖ ≤ C := by
        refine hgb _ ?_
        simpa using hσ
      rw [norm_mul]
      calc ‖F (rayLine σ ξ)‖ * ‖g (rayLine σ ξ)‖ ≤ ‖F (rayLine σ ξ)‖ * C :=
            mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = C * ‖F (rayLine σ ξ)‖ := by ring
  bound := by
    intro σ hσ
    have hmem := hF.memLp σ hσ
    have hsqF : Integrable (fun ξ : ℝ => ‖F (rayLine σ ξ)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    have hcont : ContinuousOn g {w : ℂ | 0 < w.re} := hg.continuousOn
    have hmap : Continuous fun ξ : ℝ => rayLine σ ξ := by
      unfold rayLine
      fun_prop
    have hgmeas : Continuous fun ξ : ℝ => g (rayLine σ ξ) := by
      refine hcont.comp_continuous hmap (fun ξ => ?_)
      simpa using hσ
    have hptwise : ∀ ξ : ℝ, ‖F (rayLine σ ξ) * g (rayLine σ ξ)‖ ^ 2
        ≤ C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2 := by
      intro ξ
      have hb : ‖g (rayLine σ ξ)‖ ≤ C := by
        refine hgb _ ?_
        simpa using hσ
      rw [norm_mul, mul_pow]
      have h1 : ‖g (rayLine σ ξ)‖ ^ 2 ≤ C ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) hb 2
      nlinarith [sq_nonneg ‖F (rayLine σ ξ)‖, norm_nonneg (F (rayLine σ ξ))]
    have hsq : Integrable (fun ξ : ℝ => ‖F (rayLine σ ξ) * g (rayLine σ ξ)‖ ^ 2) volume := by
      refine Integrable.mono' (hsqF.const_mul (C ^ 2)) ?_ ?_
      · exact ((hmem.aestronglyMeasurable.mul hgmeas.aestronglyMeasurable).norm.pow 2)
      · filter_upwards with ξ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hptwise ξ
    calc (∫ ξ : ℝ, ‖F (rayLine σ ξ) * g (rayLine σ ξ)‖ ^ 2)
        ≤ ∫ ξ : ℝ, C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2 :=
          integral_mono hsq (hsqF.const_mul (C ^ 2)) hptwise
      _ = C ^ 2 * ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2 := MeasureTheory.integral_const_mul _ _
      _ ≤ C ^ 2 * M := by
          refine mul_le_mul_of_nonneg_left (hF.bound σ hσ) (by positivity)

/-! ### Multipliers bounded away from one point -/

/-- On a vertical line the points within `δ` of `w₀` form a bounded set of frequencies. -/
theorem rayLine_ball_subset (σ : ℝ) (w₀ : ℂ) {δ : ℝ} :
    {ξ : ℝ | ‖rayLine σ ξ - w₀‖ < δ}
      ⊆ Icc ((w₀.im - δ) / (2 * Real.pi)) ((w₀.im + δ) / (2 * Real.pi)) := by
  intro ξ hξ
  have hδ : ‖rayLine σ ξ - w₀‖ < δ := hξ
  have him : (rayLine σ ξ - w₀).im = 2 * Real.pi * ξ - w₀.im := by
    simp [rayLine]
  have h1 : |2 * Real.pi * ξ - w₀.im| ≤ ‖rayLine σ ξ - w₀‖ := by
    rw [← him]
    exact Complex.abs_im_le_norm _
  have h2 : |2 * Real.pi * ξ - w₀.im| < δ := lt_of_le_of_lt h1 hδ
  rw [abs_lt] at h2
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  · rw [div_le_iff₀ hpi]
    nlinarith [h2.1]
  · rw [le_div_iff₀ hpi]
    nlinarith [h2.2]

/-- **A product which is holomorphic on the half-plane, bounded near one point, and a bounded
multiple of a Hardy function away from it, is itself a Hardy function.** -/
theorem isHalfPlaneHardy_of_bounded_off_ball {F g H : ℂ → ℂ} {M C B δ : ℝ} {w₀ : ℂ}
    (hF : IsHalfPlaneHardy F M) (hH : DifferentiableOn ℂ H {w : ℂ | 0 < w.re})
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hHeq : ∀ w : ℂ, 0 < w.re → δ ≤ ‖w - w₀‖ → H w = F w * g w)
    (hgb : ∀ w : ℂ, 0 < w.re → δ ≤ ‖w - w₀‖ → ‖g w‖ ≤ C)
    (hHB : ∀ w : ℂ, 0 < w.re → ‖w - w₀‖ < δ → ‖H w‖ ≤ B) :
    IsHalfPlaneHardy H (C ^ 2 * M + δ * B ^ 2) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set lo : ℝ := (w₀.im - δ) / (2 * Real.pi) with hlo
  set hi : ℝ := (w₀.im + δ) / (2 * Real.pi) with hhi
  have hlen : hi - lo = δ / Real.pi := by
    rw [hlo, hhi, div_sub_div_same]
    field_simp
    ring
  have hcontH : ∀ σ : ℝ, 0 < σ → Continuous fun ξ : ℝ => H (rayLine σ ξ) := by
    intro σ hσ
    have hmap : Continuous fun ξ : ℝ => rayLine σ ξ := by
      unfold rayLine
      fun_prop
    refine hH.continuousOn.comp_continuous hmap (fun ξ => ?_)
    simpa using hσ
  have hnorm : ∀ (σ : ℝ), 0 < σ → ∀ ξ : ℝ,
      ‖H (rayLine σ ξ)‖
        ≤ C * ‖F (rayLine σ ξ)‖ + B * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ := by
    intro σ hσ ξ
    have hre : (0 : ℝ) < (rayLine σ ξ).re := by simpa using hσ
    by_cases hball : ‖rayLine σ ξ - w₀‖ < δ
    · have hmem : ξ ∈ Icc lo hi := rayLine_ball_subset σ w₀ hball
      rw [Set.indicator_of_mem hmem, mul_one]
      have := hHB _ hre hball
      nlinarith [norm_nonneg (F (rayLine σ ξ))]
    · have hge : δ ≤ ‖rayLine σ ξ - w₀‖ := not_lt.1 hball
      have hbnd := hgb _ hre hge
      have hnn : (0 : ℝ) ≤ B * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ := by
        have h0 : (0 : ℝ) ≤ (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        positivity
      rw [hHeq _ hre hge, norm_mul]
      nlinarith [norm_nonneg (F (rayLine σ ξ))]
  have hsq : ∀ (σ : ℝ), 0 < σ → ∀ ξ : ℝ,
      ‖H (rayLine σ ξ)‖ ^ 2
        ≤ C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2 + B ^ 2 * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ := by
    intro σ hσ ξ
    have hre : (0 : ℝ) < (rayLine σ ξ).re := by simpa using hσ
    by_cases hball : ‖rayLine σ ξ - w₀‖ < δ
    · have hmem : ξ ∈ Icc lo hi := rayLine_ball_subset σ w₀ hball
      rw [Set.indicator_of_mem hmem, mul_one]
      have h1 : ‖H (rayLine σ ξ)‖ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hHB _ hre hball) 2
      nlinarith [sq_nonneg (C * ‖F (rayLine σ ξ)‖), sq_nonneg ‖F (rayLine σ ξ)‖]
    · have hge : δ ≤ ‖rayLine σ ξ - w₀‖ := not_lt.1 hball
      have hbnd := hgb _ hre hge
      have hnn : (0 : ℝ) ≤ B ^ 2 * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ := by
        have h0 : (0 : ℝ) ≤ (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) _
        positivity
      have h1 : ‖H (rayLine σ ξ)‖ ^ 2 ≤ C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2 := by
        rw [hHeq _ hre hge, norm_mul, mul_pow]
        have h2 : ‖g (rayLine σ ξ)‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbnd 2
        nlinarith [sq_nonneg ‖F (rayLine σ ξ)‖]
      linarith
  have hindint : Integrable (fun ξ : ℝ => B ^ 2 * (Icc lo hi).indicator
      (fun _ => (1 : ℝ)) ξ) volume := by
    refine Integrable.const_mul ?_ _
    refine (integrable_indicator_iff measurableSet_Icc).2 ?_
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hindval : (∫ ξ : ℝ, B ^ 2 * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ)
      = B ^ 2 * (δ / Real.pi) := by
    have hle : lo ≤ hi := by
      rw [← sub_nonneg, hlen]
      positivity
    rw [MeasureTheory.integral_const_mul, integral_indicator_const _ measurableSet_Icc,
      smul_eq_mul, mul_one, Real.volume_real_Icc_of_le hle, hlen]
  refine ⟨hH, ?_, ?_⟩
  · intro σ hσ
    have hmem := hF.memLp σ hσ
    have hdom : MemLp (fun ξ : ℝ => C * ‖F (rayLine σ ξ)‖
        + B * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ) 2 volume := by
      refine MemLp.add ((hmem.norm).const_mul C) ?_
      refine MemLp.const_mul ?_ B
      refine (memLp_indicator_iff_restrict measurableSet_Icc).2 ?_
      exact memLp_const (1 : ℝ)
    refine MemLp.mono' hdom (hcontH σ hσ).aestronglyMeasurable ?_
    filter_upwards with ξ
    exact hnorm σ hσ ξ
  · intro σ hσ
    have hmem := hF.memLp σ hσ
    have hsqF : Integrable (fun ξ : ℝ => ‖F (rayLine σ ξ)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    have hmaj : Integrable (fun ξ : ℝ => C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2
        + B ^ 2 * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ) volume :=
      (hsqF.const_mul (C ^ 2)).add hindint
    have hsqint : Integrable (fun ξ : ℝ => ‖H (rayLine σ ξ)‖ ^ 2) volume := by
      refine Integrable.mono' hmaj ((hcontH σ hσ).norm.pow 2).aestronglyMeasurable ?_
      filter_upwards with ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hsq σ hσ ξ
    have hpi1 : (1 : ℝ) ≤ Real.pi := by
      have := Real.pi_gt_three
      linarith
    calc (∫ ξ : ℝ, ‖H (rayLine σ ξ)‖ ^ 2)
        ≤ ∫ ξ : ℝ, (C ^ 2 * ‖F (rayLine σ ξ)‖ ^ 2
            + B ^ 2 * (Icc lo hi).indicator (fun _ => (1 : ℝ)) ξ) :=
          integral_mono hsqint hmaj (hsq σ hσ)
      _ = C ^ 2 * (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2) + B ^ 2 * (δ / Real.pi) := by
          rw [MeasureTheory.integral_add (hsqF.const_mul (C ^ 2)) hindint,
            MeasureTheory.integral_const_mul, hindval]
      _ ≤ C ^ 2 * M + δ * B ^ 2 := by
          have h1 : C ^ 2 * (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2) ≤ C ^ 2 * M :=
            mul_le_mul_of_nonneg_left (hF.bound σ hσ) (by positivity)
          have h2 : B ^ 2 * (δ / Real.pi) ≤ δ * B ^ 2 := by
            have hnn : (0 : ℝ) ≤ B ^ 2 * δ := by positivity
            have heq : B ^ 2 * (δ / Real.pi) = (B ^ 2 * δ) / Real.pi := by ring
            rw [heq, div_le_iff₀ (by linarith : (0:ℝ) < Real.pi)]
            nlinarith
          linarith

/-- **A holomorphic multiplier bounded away from one point still preserves the Hardy space**, as
soon as the product itself stays bounded near that point. -/
theorem isHalfPlaneHardy_mul_of_bounded_off_ball {F g : ℂ → ℂ} {M C B δ : ℝ} {w₀ : ℂ}
    (hF : IsHalfPlaneHardy F M) (hg : DifferentiableOn ℂ g {w : ℂ | 0 < w.re})
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hgb : ∀ w : ℂ, 0 < w.re → δ ≤ ‖w - w₀‖ → ‖g w‖ ≤ C)
    (hFB : ∀ w : ℂ, 0 < w.re → ‖w - w₀‖ < δ → ‖F w * g w‖ ≤ B) :
    IsHalfPlaneHardy (fun w => F w * g w) (C ^ 2 * M + δ * B ^ 2) :=
  isHalfPlaneHardy_of_bounded_off_ball hF (hF.holo.mul hg) hC hB hδ (fun _ _ _ => rfl) hgb hFB

/-- **Dividing a Hardy function by a zero of the required order.**  If `H` is holomorphic on the
half-plane, continuous at `w₀`, and satisfies `H·(w - w₀)^l = F` away from `w₀`, then `H` is itself
a Hardy function. -/
theorem isHalfPlaneHardy_of_div_pow {F H : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {w₀ : ℂ} {l : ℕ} (hH : DifferentiableOn ℂ H {w : ℂ | 0 < w.re})
    (hcont : ContinuousAt H w₀)
    (hHeq : ∀ w : ℂ, 0 < w.re → w ≠ w₀ → H w * (w - w₀) ^ l = F w) :
    ∃ N : ℝ, IsHalfPlaneHardy H N := by
  have hev : ∀ᶠ w in 𝓝 w₀, ‖H w‖ ≤ ‖H w₀‖ + 1 := by
    have h : Filter.Tendsto (fun w : ℂ => ‖H w‖) (𝓝 w₀) (𝓝 ‖H w₀‖) := hcont.norm
    exact (h.eventually (gt_mem_nhds (by linarith : ‖H w₀‖ < ‖H w₀‖ + 1))).mono
      fun w hw => le_of_lt hw
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨_, isHalfPlaneHardy_of_bounded_off_ball (g := fun w => (((w - w₀) ^ l))⁻¹)
    (w₀ := w₀) hF hH (C := (δ ^ l)⁻¹) (B := ‖H w₀‖ + 1) (δ := δ) (by positivity)
    (by positivity) hδ0.le ?_ ?_ ?_⟩
  · intro w hw hge
    have hne : w - w₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hge
      linarith
    have hpow : (w - w₀) ^ l ≠ 0 := pow_ne_zero _ hne
    have hwne : w ≠ w₀ := sub_ne_zero.1 hne
    rw [← hHeq w hw hwne]
    field_simp
  · intro w _ hge
    have hne : w - w₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hge
      linarith
    rw [norm_inv, norm_pow]
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_left₀ hδ0.le hge l
  · intro w _ hball
    exact hδ (by simpa [dist_eq_norm] using hball)


end

end GaloisForLFunctions.HTGeometry
