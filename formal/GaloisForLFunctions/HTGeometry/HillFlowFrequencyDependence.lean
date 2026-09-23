import GaloisForLFunctions.HTGeometry.HillOscillatorBounds

/-!
# The Hill flow depends continuously on the frequency

A synthesis over frequencies needs the fibrewise solution to be measurable in the frequency, and the
cheapest honest route to that is a quantitative stability estimate: two Hill flows started at the
same datum but run with different frequencies stay close, with a bound linear in the difference of
the squared frequencies.

The estimate is Grönwall applied to the difference. Writing `A₁y₁ - A₂y₂ = A₁(y₁-y₂) + (A₁-A₂)y₂`,
the first term is controlled by the common bound on the generator and the second by the difference of
the frequencies times the size of the second flow, which the Volterra series already bounds.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

section Stability

variable {ω₁ ω₂ : ℝ → ℝ} {M δ b : ℝ}

/-- The generators of two Hill systems differ by the difference of the squared frequencies. -/
theorem norm_hillField_sub_le (hδ : ∀ s, |ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)| ≤ δ) (hδ0 : 0 ≤ δ) (s : ℝ) :
    ‖hillField ω₁ s - hillField ω₂ s‖ ≤ δ := by
  refine ContinuousLinearMap.opNorm_le_bound _ hδ0 fun y => ?_
  have hval : (hillField ω₁ s - hillField ω₂ s) y = (0, -(ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)) * y.1) := by
    have h₁ : (hillField ω₁ s - hillField ω₂ s) y = hillField ω₁ s y - hillField ω₂ s y := rfl
    rw [h₁, hillField_apply, hillField_apply]
    refine Prod.ext ?_ ?_
    · simp
    · show -(ω₁ s ^ (2 : ℕ)) * y.1 - -(ω₂ s ^ (2 : ℕ)) * y.1 = -(ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)) * y.1
      ring
  rw [hval, Prod.norm_def]
  refine max_le ?_ ?_
  · simp [mul_nonneg hδ0 (norm_nonneg y)]
  · have hy1 : ‖y.1‖ ≤ ‖y‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hnorm : ‖-(ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)) * y.1‖ = |ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)| * ‖y.1‖ := by
      rw [norm_mul, norm_neg, Real.norm_eq_abs]
    rw [hnorm]
    have hs := hδ s
    nlinarith [norm_nonneg y.1, norm_nonneg y, abs_nonneg (ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ))]

/-- **Quantitative dependence of the Hill flow on its frequency.** -/
theorem norm_hillFlow_sub_le (hω₁ : Continuous ω₁) (hω₂ : Continuous ω₂) (hM1 : 1 ≤ M)
    (hM₁ : ∀ s, ω₁ s ^ (2 : ℕ) ≤ M) (hM₂ : ∀ s, ω₂ s ^ (2 : ℕ) ≤ M)
    (hδ : ∀ s, |ω₁ s ^ (2 : ℕ) - ω₂ s ^ (2 : ℕ)| ≤ δ) (hδ0 : 0 ≤ δ) (y₀ : ℝ × ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ‖hillFlow ω₁ y₀ t - hillFlow ω₂ y₀ t‖ ≤
      gronwallBound 0 M (δ * (‖y₀‖ * Real.exp (M * b))) t := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hd₁ := fun s => hasDerivAt_hillFlow hω₁ hM1 hM₁ y₀ s
  have hd₂ := fun s => hasDerivAt_hillFlow hω₂ hM1 hM₂ y₀ s
  have hdiff : ∀ s : ℝ, HasDerivAt (fun r => hillFlow ω₁ y₀ r - hillFlow ω₂ y₀ r)
      (hillField ω₁ s (hillFlow ω₁ y₀ s) - hillField ω₂ s (hillFlow ω₂ y₀ s)) s :=
    fun s => (hd₁ s).sub (hd₂ s)
  have hsize : ∀ s ∈ Icc (0 : ℝ) b, ‖hillFlow ω₂ y₀ s‖ ≤ ‖y₀‖ * Real.exp (M * b) := by
    intro s hs
    have hbase := norm_volterraSolution_le (f := fun _ : ℝ => y₀)
      (K := fun _ s => hillField ω₂ s) continuous_const (continuous_hillField hω₂) hM0
      (norm_nonneg y₀) (fun _ r => norm_hillField_le hM1 hM₂ r) (fun _ => le_rfl) s
    have habs : |s| ≤ b := by
      rw [abs_of_nonneg hs.1]
      exact hs.2
    have hexp : Real.exp (M * |s|) ≤ Real.exp (M * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hM0)
    calc ‖hillFlow ω₂ y₀ s‖ ≤ ‖y₀‖ * Real.exp (M * |s|) := hbase
      _ ≤ ‖y₀‖ * Real.exp (M * b) := mul_le_mul_of_nonneg_left hexp (norm_nonneg y₀)
  have hbound : ∀ s ∈ Ico (0 : ℝ) b,
      ‖hillField ω₁ s (hillFlow ω₁ y₀ s) - hillField ω₂ s (hillFlow ω₂ y₀ s)‖ ≤
        M * ‖hillFlow ω₁ y₀ s - hillFlow ω₂ y₀ s‖ + δ * (‖y₀‖ * Real.exp (M * b)) := by
    intro s hs
    have hsplit : hillField ω₁ s (hillFlow ω₁ y₀ s) - hillField ω₂ s (hillFlow ω₂ y₀ s)
        = hillField ω₁ s (hillFlow ω₁ y₀ s - hillFlow ω₂ y₀ s)
          + (hillField ω₁ s - hillField ω₂ s) (hillFlow ω₂ y₀ s) := by
      simp [ContinuousLinearMap.map_sub]
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have h₁ : ‖hillField ω₁ s (hillFlow ω₁ y₀ s - hillFlow ω₂ y₀ s)‖
        ≤ M * ‖hillFlow ω₁ y₀ s - hillFlow ω₂ y₀ s‖ := by
      refine ((hillField ω₁ s).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right (norm_hillField_le hM1 hM₁ s) (norm_nonneg _)
    have h₂ : ‖(hillField ω₁ s - hillField ω₂ s) (hillFlow ω₂ y₀ s)‖
        ≤ δ * (‖y₀‖ * Real.exp (M * b)) := by
      refine ((hillField ω₁ s - hillField ω₂ s).le_opNorm _).trans ?_
      have hsz := hsize s ⟨hs.1, le_of_lt hs.2⟩
      have hop := norm_hillField_sub_le hδ hδ0 s
      have hnn : (0 : ℝ) ≤ ‖hillFlow ω₂ y₀ s‖ := norm_nonneg _
      nlinarith [norm_nonneg (hillFlow ω₂ y₀ s), mul_nonneg hδ0 hnn]
    linarith
  have hcont : ContinuousOn (fun r => hillFlow ω₁ y₀ r - hillFlow ω₂ y₀ r) (Icc 0 b) :=
    fun s _ => ((hdiff s).continuousAt).continuousWithinAt
  have hzero : ‖hillFlow ω₁ y₀ 0 - hillFlow ω₂ y₀ 0‖ ≤ 0 := by
    rw [hillFlow_zero hω₁ hM1 hM₁, hillFlow_zero hω₂ hM1 hM₂, sub_self, norm_zero]
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hdiff s).hasDerivWithinAt) hzero hbound t ht
  simpa using hgron

end Stability

/-! ## The scaled family -/

section Scaled

variable {c : ℝ → ℝ} {C S b : ℝ}

/-- **The flow of the scaled family `ω = c·s`, compared at two scales.** -/
theorem norm_hillFlow_scaled_sub_le (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    {s₁ s₂ : ℝ} (hs₁ : |s₁| ≤ S) (hs₂ : |s₂| ≤ S) (hS : 0 ≤ S) (y₀ : ℝ × ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ‖hillFlow (fun r => c r * s₁) y₀ t - hillFlow (fun r => c r * s₂) y₀ t‖ ≤
      gronwallBound 0 (max 1 (C ^ (2 : ℕ) * S ^ (2 : ℕ)))
        (C ^ (2 : ℕ) * |s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)| *
          (‖y₀‖ * Real.exp (max 1 (C ^ (2 : ℕ) * S ^ (2 : ℕ)) * b))) t := by
  have hsq : ∀ s : ℝ, |s| ≤ S → s ^ (2 : ℕ) ≤ S ^ (2 : ℕ) := by
    intro s hs
    have := abs_nonneg s
    nlinarith [sq_abs s]
  have hM1 : (1 : ℝ) ≤ max 1 (C ^ (2 : ℕ) * S ^ (2 : ℕ)) := le_max_left _ _
  have hbound : ∀ (s : ℝ), |s| ≤ S → ∀ r, (c r * s) ^ (2 : ℕ) ≤ max 1 (C ^ (2 : ℕ) * S ^ (2 : ℕ)) := by
    intro s hs r
    have h1 : (c r * s) ^ (2 : ℕ) = c r ^ (2 : ℕ) * s ^ (2 : ℕ) := by ring
    have h2 : c r ^ (2 : ℕ) * s ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * S ^ (2 : ℕ) := by
      have hcr : (0 : ℝ) ≤ c r ^ (2 : ℕ) := sq_nonneg _
      have hss : (0 : ℝ) ≤ s ^ (2 : ℕ) := sq_nonneg _
      nlinarith [hC r, hsq s hs, sq_nonneg C, sq_nonneg S]
    exact h1 ▸ h2.trans (le_max_right _ _)
  have hδ : ∀ r, |(c r * s₁) ^ (2 : ℕ) - (c r * s₂) ^ (2 : ℕ)| ≤ C ^ (2 : ℕ) * |s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)| := by
    intro r
    have hfac : (c r * s₁) ^ (2 : ℕ) - (c r * s₂) ^ (2 : ℕ) = c r ^ (2 : ℕ) * (s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (sq_nonneg (c r))]
    exact mul_le_mul_of_nonneg_right (hC r) (abs_nonneg _)
  have hδ0 : 0 ≤ C ^ (2 : ℕ) * |s₁ ^ (2 : ℕ) - s₂ ^ (2 : ℕ)| := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  exact norm_hillFlow_sub_le (hc.mul continuous_const) (hc.mul continuous_const) hM1
    (hbound s₁ hs₁) (hbound s₂ hs₂) hδ hδ0 y₀ ht

/-- **The flow is continuous in the frequency scale.** -/
theorem continuousAt_hillFlow_scaled (hc : Continuous c) (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ))
    (y₀ : ℝ × ℝ) {t : ℝ} (ht : t ∈ Icc 0 b) (s₀ : ℝ) :
    ContinuousAt (fun s => hillFlow (fun r => c r * s) y₀ t) s₀ := by
  set S : ℝ := |s₀| + 1 with hS
  have hS0 : 0 ≤ S := by positivity
  have hs₀ : |s₀| ≤ S := by simp [hS]
  set M : ℝ := max 1 (C ^ (2 : ℕ) * S ^ (2 : ℕ)) with hM
  set B : ℝ := ‖y₀‖ * Real.exp (M * b) with hB
  have hnear : ∀ᶠ s in nhds s₀, |s| ≤ S := by
    have hball : Metric.ball s₀ 1 ∈ nhds s₀ := Metric.ball_mem_nhds s₀ one_pos
    refine Filter.eventually_of_mem hball fun s hs => ?_
    have : |s - s₀| < 1 := by simpa [Real.dist_eq] using hs
    have habs : |s| ≤ |s - s₀| + |s₀| := by
      have := abs_sub_abs_le_abs_sub s s₀
      cases abs_cases (s - s₀) with
      | inl h => cases abs_cases s with
        | inl h1 => cases abs_cases s₀ with
          | inl h2 => linarith [h.1, h1.1, h2.1]
          | inr h2 => linarith [h.1, h1.1, h2.1]
        | inr h1 => cases abs_cases s₀ with
          | inl h2 => linarith [h.1, h1.1, h2.1]
          | inr h2 => linarith [h.1, h1.1, h2.1]
      | inr h => cases abs_cases s with
        | inl h1 => cases abs_cases s₀ with
          | inl h2 => linarith [h.1, h1.1, h2.1]
          | inr h2 => linarith [h.1, h1.1, h2.1]
        | inr h1 => cases abs_cases s₀ with
          | inl h2 => linarith [h.1, h1.1, h2.1]
          | inr h2 => linarith [h.1, h1.1, h2.1]
    rw [hS]
    linarith
  have hle : ∀ᶠ s in nhds s₀,
      dist (hillFlow (fun r => c r * s) y₀ t) (hillFlow (fun r => c r * s₀) y₀ t) ≤
        gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := by
    filter_upwards [hnear] with s hs
    rw [dist_eq_norm]
    exact norm_hillFlow_scaled_sub_le hc hC hs hs₀ hS0 y₀ ht
  have hzero : Filter.Tendsto
      (fun s => gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t) (nhds s₀) (nhds 0) := by
    have hcontε : Continuous fun ε : ℝ => gronwallBound 0 M ε t :=
      gronwallBound_continuous_ε 0 M t
    have hmap : Filter.Tendsto (fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) (nhds s₀) (nhds 0) := by
      have hcont : Continuous fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B := by fun_prop
      have := hcont.tendsto s₀
      simpa using this
    have hcomp := (hcontε.tendsto 0).comp hmap
    have hval : ((fun ε : ℝ => gronwallBound 0 M ε t) ∘
        fun s : ℝ => C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B)
        = fun s : ℝ => gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := rfl
    rw [hval] at hcomp
    simpa [gronwallBound_ε0_δ0] using hcomp
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hzero' := Metric.tendsto_nhds.mp hzero ε hε
  filter_upwards [hle, hzero'] with s hs hz
  have hnn : (0 : ℝ) ≤ gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t :=
    le_trans dist_nonneg hs
  have : |gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t| < ε := by
    simpa [Real.dist_eq] using hz
  calc dist (hillFlow (fun r => c r * s) y₀ t) (hillFlow (fun r => c r * s₀) y₀ t)
      ≤ gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t := hs
    _ ≤ |gronwallBound 0 M (C ^ (2 : ℕ) * |s ^ (2 : ℕ) - s₀ ^ (2 : ℕ)| * B) t| := le_abs_self _
    _ < ε := this

end Scaled

end GaloisForLFunctions.HTGeometry
