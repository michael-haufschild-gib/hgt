import GaloisForLFunctions.RHTower.MobiusCausalMultiplierBounds

/-!
# Fisher flatness of the normalized signed-coisometry form

The squarefree normalization multiplies the causal source by `1/Z_ω`, where
`Z_ω = ζ(1+2ω)/ζ(2+4ω)` is the squarefree partition at the shifted parameter.  Both

```text
1/Z_ω → 0        and        ∂_ω(1/Z_ω) → 2ζ(2)
```

as `ω → 0+`, so the Leibniz rule turns the two bounded boundary energies — of the multiplier and
of its parameter derivative — into a Fisher-scaled limit that still vanishes:

```text
(4ω)² ∫ ‖∂_ω (M_ω/Z_ω)(iτ)‖² dτ → 0 .
```
-/

open MeasureTheory Filter Topology Complex

namespace RHTower

noncomputable section

/-- The reciprocal squarefree normalization at the shifted parameter. -/
def invSquarefreeNorm (ω : ℝ) : ℂ :=
  riemannZeta (2 + 4 * (ω : ℂ)) / riemannZeta (1 + 2 * (ω : ℂ))

/-- Its parameter derivative. -/
def invSquarefreeNormDeriv (ω : ℝ) : ℂ :=
  (4 * deriv riemannZeta (2 + 4 * (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ)) -
      riemannZeta (2 + 4 * (ω : ℂ)) * (2 * deriv riemannZeta (1 + 2 * (ω : ℂ)))) /
    riemannZeta (1 + 2 * (ω : ℂ)) ^ 2

theorem two_add_four_mul_ne_one (ω : ℝ) (hω : 0 < ω) : (2 : ℂ) + 4 * (ω : ℂ) ≠ 1 := by
  intro h
  have hre : ((2 : ℂ) + 4 * (ω : ℂ)).re = (1 : ℂ).re := by rw [h]
  simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.im_ofNat, mul_zero, sub_zero, Complex.one_re] at hre
  linarith

theorem hasDerivAt_zeta_two_add_four_mul {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (fun w : ℝ => riemannZeta (2 + 4 * (w : ℂ)))
      (4 * deriv riemannZeta (2 + 4 * (ω : ℂ))) ω := by
  have hlin : HasDerivAt (fun w : ℝ => 2 + 4 * (w : ℂ)) 4 ω := by
    have h : HasDerivAt (fun w : ℝ => ((w : ℝ) : ℂ)) 1 ω := Complex.ofRealCLM.hasDerivAt
    simpa using (h.const_mul (4 : ℂ)).const_add (2 : ℂ)
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (2 + 4 * (ω : ℂ))) (2 + 4 * (ω : ℂ)) :=
    (differentiableAt_riemannZeta (two_add_four_mul_ne_one ω hω)).hasDerivAt
  have h := hζ.scomp ω hlin
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

theorem hasDerivAt_zeta_one_add_two_mul {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt (fun w : ℝ => riemannZeta (1 + 2 * (w : ℂ)))
      (2 * deriv riemannZeta (1 + 2 * (ω : ℂ))) ω := by
  have h := hasDerivAt_zeta_shift (z := 0) hω (by simp)
  simpa using h

theorem hasDerivAt_invSquarefreeNorm {ω : ℝ} (hω : 0 < ω) :
    HasDerivAt invSquarefreeNorm (invSquarefreeNormDeriv ω) ω := by
  have hζ0 : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hω
  have h := (hasDerivAt_zeta_two_add_four_mul hω).div (hasDerivAt_zeta_one_add_two_mul hω) hζ0
  refine h.congr_deriv ?_
  rw [invSquarefreeNormDeriv]

/-! ### The two critical limits -/

theorem tendsto_zeta_two_add_four_mul :
    Tendsto (fun ω : ℝ => riemannZeta (2 + 4 * (ω : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (riemannZeta 2)) := by
  have hne : (2 : ℂ) ≠ 1 := by norm_num
  have hcont : ContinuousAt riemannZeta 2 := (differentiableAt_riemannZeta hne).continuousAt
  have hmap : Tendsto (fun ω : ℝ => (2 : ℂ) + 4 * (ω : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 2) := by
    have hc : Continuous fun ω : ℝ => (2 : ℂ) + 4 * (ω : ℂ) := by fun_prop
    have h0 : (2 : ℂ) + 4 * ((0 : ℝ) : ℂ) = 2 := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hcont.tendsto.comp hmap

theorem tendsto_deriv_zeta_two_add_four_mul :
    Tendsto (fun ω : ℝ => deriv riemannZeta (2 + 4 * (ω : ℂ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv riemannZeta 2)) := by
  have hana : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
    have hdiffOn : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro s hs
      exact (differentiableAt_riemannZeta (by simpa using hs)).differentiableWithinAt
    exact hdiffOn.analyticOnNhd isOpen_compl_singleton
  have hmem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    norm_num
  have hcont : ContinuousAt (deriv riemannZeta) 2 := (hana _ hmem).deriv.continuousAt
  have hmap : Tendsto (fun ω : ℝ => (2 : ℂ) + 4 * (ω : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 2) := by
    have hc : Continuous fun ω : ℝ => (2 : ℂ) + 4 * (ω : ℂ) := by fun_prop
    have h0 : (2 : ℂ) + 4 * ((0 : ℝ) : ℂ) = 2 := by push_cast; ring
    have h := hc.tendsto (0 : ℝ)
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact hcont.tendsto.comp hmap

/-- **The normalization vanishes at the critical parameter.** -/
theorem tendsto_invSquarefreeNorm :
    Tendsto invSquarefreeNorm (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hinv := tendsto_inv_riemannZeta_one_add_two_mul
  have hprod := tendsto_zeta_two_add_four_mul.mul hinv
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω0
  have hωpos : (0 : ℝ) < ω := hω0
  have hζ : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hωpos
  rw [invSquarefreeNorm, div_eq_mul_inv]

/-- **The normalization has a finite critical derivative.** -/
theorem tendsto_invSquarefreeNormDeriv :
    Tendsto invSquarefreeNormDeriv (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * riemannZeta 2)) := by
  have hP := tendsto_two_mul_riemannZeta_one_add_two_mul
  have hQ := tendsto_sq_mul_deriv_riemannZeta_one_add_two_mul
  have hinv := tendsto_inv_riemannZeta_one_add_two_mul
  -- the first summand tends to zero
  have h1 : Tendsto (fun ω : ℝ => 4 * deriv riemannZeta (2 + 4 * (ω : ℂ)) *
      (riemannZeta (1 + 2 * (ω : ℂ)))⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := ((tendsto_const_nhds (x := (4 : ℂ))).mul
      tendsto_deriv_zeta_two_add_four_mul).mul hinv
    rw [mul_zero] at h
    exact h
  -- the second summand
  have hden : Tendsto (fun ω : ℝ => ((2 * (ω : ℂ)) * riemannZeta (1 + 2 * (ω : ℂ))) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    have := hP.pow 2
    simpa using this
  have hdiv := hQ.div hden (one_ne_zero)
  rw [div_one] at hdiv
  have h2 := tendsto_zeta_two_add_four_mul.mul hdiv
  have hcomb := h1.sub (h2.const_mul (2 : ℂ))
  rw [zero_sub] at hcomb
  have hval : -((2 : ℂ) * (riemannZeta 2 * (-1))) = 2 * riemannZeta 2 := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ω hω0
  have hωpos : (0 : ℝ) < ω := hω0
  have hωne : ((ω : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hωpos
  have hζ : riemannZeta (1 + 2 * (ω : ℂ)) ≠ 0 := riemannZeta_one_add_two_mul_ne_zero hωpos
  simp only [Pi.div_apply]
  rw [invSquarefreeNormDeriv]
  field_simp

/-! ### The normalized causal source and its Fisher-scaled flatness -/

/-- The normalized coupled causal multiplier `M_ω/Z_ω`. -/
def normalizedMobiusCausal (ω : ℝ) (z : ℂ) : ℂ :=
  mobiusCausalMultiplier ω z * invSquarefreeNorm ω

/-- Its parameter derivative, by the Leibniz rule. -/
def normalizedMobiusCausalDeriv (ω : ℝ) (z : ℂ) : ℂ :=
  mobiusCausalMultiplierDeriv ω z * invSquarefreeNorm ω +
    mobiusCausalMultiplier ω z * invSquarefreeNormDeriv ω

theorem hasDerivAt_normalizedMobiusCausal {ω : ℝ} (hω : 0 < ω) {z : ℂ} (hz : 0 ≤ z.re)
    (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℝ => normalizedMobiusCausal w z) (normalizedMobiusCausalDeriv ω z) ω := by
  have h := (hasDerivAt_mobiusCausalMultiplier hω hz hz0).mul (hasDerivAt_invSquarefreeNorm hω)
  exact h

/-- The two normalization factors are bounded near the critical parameter. -/
theorem exists_normalization_bound :
    ∃ ω₃ M : ℝ, 0 < ω₃ ∧ 0 ≤ M ∧ ∀ ω : ℝ, 0 < ω → ω ≤ ω₃ →
      ‖invSquarefreeNorm ω‖ ≤ M ∧ ‖invSquarefreeNormDeriv ω‖ ≤ M := by
  have h1 := tendsto_invSquarefreeNorm
  have h2 := tendsto_invSquarefreeNormDeriv
  have hev1 : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      invSquarefreeNorm ω ∈ Metric.ball (0 : ℂ) 1 :=
    h1.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))
  have hev2 : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      invSquarefreeNormDeriv ω ∈ Metric.ball (2 * riemannZeta 2) 1 :=
    h2.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev1 hev2
  obtain ⟨ε₁, hε₁, h₁⟩ := hev1
  obtain ⟨ε₂, hε₂, h₂⟩ := hev2
  refine ⟨min (ε₁ / 2) (ε₂ / 2), 1 + ‖2 * riemannZeta 2‖,
    lt_min (by linarith) (by linarith), by positivity, fun ω hω hωle => ?_⟩
  have hd₁ : dist ω (0 : ℝ) < ε₁ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hω]
    have : ω ≤ ε₁ / 2 := le_trans hωle (min_le_left _ _)
    linarith
  have hd₂ : dist ω (0 : ℝ) < ε₂ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hω]
    have : ω ≤ ε₂ / 2 := le_trans hωle (min_le_right _ _)
    linarith
  have hm₁ := h₁ hd₁ hω
  have hm₂ := h₂ hd₂ hω
  rw [Metric.mem_ball, dist_zero_right] at hm₁
  rw [Metric.mem_ball, dist_eq_norm] at hm₂
  constructor
  · have : (0 : ℝ) ≤ ‖2 * riemannZeta 2‖ := norm_nonneg _
    linarith
  · have hsplit : ‖invSquarefreeNormDeriv ω‖
        ≤ ‖invSquarefreeNormDeriv ω - 2 * riemannZeta 2‖ + ‖2 * riemannZeta 2‖ := by
      have := norm_add_le (invSquarefreeNormDeriv ω - 2 * riemannZeta 2) (2 * riemannZeta 2)
      simpa using this
    linarith

/-- **The card's `(14)`: the normalized signed-coisometry form is Fisher-flat.** -/
theorem tendsto_fisher_scaled_normalized_energy :
    Tendsto (fun ω : ℝ => (4 * ω) ^ 2 *
        ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨ω₁, K₁, hω₁, hK₁, hbound₁⟩ := exists_uniform_boundary_bound
  obtain ⟨ω₂, K₂, hω₂, hK₂, hbound₂⟩ := exists_uniform_multiplier_bound
  obtain ⟨ω₃, M, hω₃, hM, hnorm⟩ := exists_normalization_bound
  set K : ℝ := max K₁ K₂ with hKdef
  have hK : 0 ≤ K := le_trans hK₁ (le_max_left _ _)
  set ω₀ : ℝ := min (min ω₁ ω₂) ω₃ with hω₀def
  have hω₀ : 0 < ω₀ := lt_min (lt_min hω₁ hω₂) hω₃
  -- the pointwise majorant for the normalized derivative
  have hmaj : ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ → ∀ τ : ℝ, τ ≠ 0 →
      ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ≤ (2 * M) * boundaryMajorant K τ := by
    intro ω hω hωle τ hτ
    have hle₁ : ω ≤ ω₁ := le_trans hωle (le_trans (min_le_left _ _) (min_le_left _ _))
    have hle₂ : ω ≤ ω₂ := le_trans hωle (le_trans (min_le_left _ _) (min_le_right _ _))
    have hle₃ : ω ≤ ω₃ := le_trans hωle (min_le_right _ _)
    obtain ⟨hn1, hn2⟩ := hnorm ω hω hle₃
    have hb₁ := hbound₁ ω hω hle₁ τ hτ
    have hb₂ := hbound₂ ω hω hle₂ τ hτ
    have hmaj₁ : boundaryMajorant K₁ τ ≤ boundaryMajorant K τ := by
      by_cases hτ9 : |τ| ≤ 9
      · rw [boundaryMajorant_near hτ9, boundaryMajorant_near hτ9]
        exact le_max_left _ _
      · rw [not_le] at hτ9
        rw [boundaryMajorant_far hτ9, boundaryMajorant_far hτ9]
    have hmaj₂ : boundaryMajorant K₂ τ ≤ boundaryMajorant K τ := by
      by_cases hτ9 : |τ| ≤ 9
      · rw [boundaryMajorant_near hτ9, boundaryMajorant_near hτ9]
        exact le_max_right _ _
      · rw [not_le] at hτ9
        rw [boundaryMajorant_far hτ9, boundaryMajorant_far hτ9]
    have hmajnn : 0 ≤ boundaryMajorant K τ := boundaryMajorant_nonneg hK τ
    rw [normalizedMobiusCausalDeriv]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul]
    have hp₁ : ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ * ‖invSquarefreeNorm ω‖
        ≤ boundaryMajorant K τ * M :=
      mul_le_mul (le_trans hb₁ hmaj₁) hn1 (norm_nonneg _) hmajnn
    have hp₂ : ‖mobiusCausalMultiplier ω ((τ : ℂ) * Complex.I)‖ * ‖invSquarefreeNormDeriv ω‖
        ≤ boundaryMajorant K τ * M :=
      mul_le_mul (le_trans hb₂ hmaj₂) hn2 (norm_nonneg _) hmajnn
    nlinarith [hmajnn, hM]
  -- measurability
  have hmeasfun : ∀ ω : ℝ, 0 < ω →
      AEStronglyMeasurable (fun τ : ℝ =>
        ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2) volume := by
    intro ω hω
    have h1 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_mobiusCausalMultiplierDeriv_line hω)
    have h2 := aestronglyMeasurable_of_continuousOn_ne_zero
      (continuousOn_mobiusCausalMultiplier_line hω)
    have h3 : AEStronglyMeasurable (fun τ : ℝ =>
        normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)) volume := by
      have ha := h1.mul (aestronglyMeasurable_const (b := invSquarefreeNorm ω))
      have hb := h2.mul (aestronglyMeasurable_const (b := invSquarefreeNormDeriv ω))
      exact ha.add hb
    exact (h3.norm.pow 2)
  -- the integral bound
  have hint : ∀ ω : ℝ, 0 < ω → ω ≤ ω₀ →
      (∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2)
        ≤ (2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ := by
    intro ω hω hωle
    have hdom : ∀ᵐ τ : ℝ, ‖‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2‖
        ≤ ((2 * M) ^ 2 * boundaryBound K τ) := by
      filter_upwards [compl_mem_ae_iff.2 Real.volume_singleton] with τ hτmem
      have hτ : τ ≠ 0 := hτmem
      have h1 := hmaj ω hω hωle τ hτ
      have h2 : (0 : ℝ) ≤ ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ := norm_nonneg _
      have hsq : ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
          ≤ ((2 * M) * boundaryMajorant K τ) ^ 2 := pow_le_pow_left₀ h2 h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), boundaryBound_eq K τ]
      nlinarith [sq_nonneg (boundaryMajorant K τ), sq_nonneg (2 * M)]
    have hintegrable : Integrable (fun τ : ℝ =>
        ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2) := by
      refine Integrable.mono (((integrable_boundaryBound K).const_mul ((2 * M) ^ 2)))
        (hmeasfun ω hω) ?_
      filter_upwards [hdom] with τ hτ
      have hnn : (0 : ℝ) ≤ (2 * M) ^ 2 * boundaryBound K τ := by
        have hbn := boundaryBound_nonneg K τ
        positivity
      have hrhs : ‖(2 * M) ^ 2 * boundaryBound K τ‖ = (2 * M) ^ 2 * boundaryBound K τ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      rw [hrhs]
      exact hτ
    have hmono := integral_mono_ae hintegrable
      ((integrable_boundaryBound K).const_mul ((2 * M) ^ 2)) ?_
    · calc (∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ ∫ τ : ℝ, (2 * M) ^ 2 * boundaryBound K τ := hmono
        _ = (2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ := by
            rw [integral_const_mul]
    · filter_upwards [hdom] with τ hτ
      have hnn : (0 : ℝ) ≤ ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn] at hτ
      exact hτ
  -- squeeze
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ω ∧ ω ≤ ω₀ := by
    filter_upwards [Ioc_mem_nhdsGT hω₀] with ω hω
    exact ⟨hω.1, hω.2⟩
  have hupper : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (4 * ω) ^ 2 * ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
        ≤ (4 * ω) ^ 2 * ((2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ) := by
    filter_upwards [hev] with ω hω
    exact mul_le_mul_of_nonneg_left (hint ω hω.1 hω.2) (by positivity)
  have hlower : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (0 : ℝ) ≤ (4 * ω) ^ 2 *
        ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 := by
    filter_upwards [hev] with ω hω
    have hnn : (0 : ℝ) ≤ ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2 :=
      integral_nonneg fun τ => by positivity
    positivity
  have hzero : Tendsto (fun ω : ℝ => (4 * ω) ^ 2 * ((2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun ω : ℝ => (4 * ω) ^ 2 * ((2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ)) :=
      by continuity
    have h := hc.tendsto (0 : ℝ)
    have h0 : (4 * (0 : ℝ)) ^ 2 * ((2 * M) ^ 2 * ∫ τ : ℝ, boundaryBound K τ) = 0 := by norm_num
    rw [h0] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzero hlower hupper

/-! ### The no-go -/

/-- **The card's no-go.**  The Fisher-scaled boundary energy of the assembled causal derivative
cannot stay above any positive threshold: identifying a nonzero completed contact tangent with the
critical parameter derivative of the coupled causal source is impossible. -/
theorem not_eventually_fisher_energy_ge {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ (4 * ω) ^ 2 *
      ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2) : False := by
  have hlim := tendsto_fisher_scaled_boundary_energy
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (4 * ω) ^ 2 * ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
        ∈ Metric.ball (0 : ℝ) c :=
    hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hc)
  have hboth := hev.and h
  obtain ⟨ω, hω⟩ := hboth.exists
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hω
  have h1 := hω.1
  have h2 := hω.2
  have h3 : (4 * ω) ^ 2 * ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
      ≤ |(4 * ω) ^ 2 * ∫ τ : ℝ, ‖mobiusCausalMultiplierDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2| :=
    le_abs_self _
  linarith

/-- The same no-go for the normalized signed-coisometry form. -/
theorem not_eventually_normalized_fisher_energy_ge {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), c ≤ (4 * ω) ^ 2 *
      ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2) : False := by
  have hlim := tendsto_fisher_scaled_normalized_energy
  have hev : ∀ᶠ ω : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (4 * ω) ^ 2 * ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
        ∈ Metric.ball (0 : ℝ) c :=
    hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hc)
  have hboth := hev.and h
  obtain ⟨ω, hω⟩ := hboth.exists
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hω
  have h1 := hω.1
  have h2 := hω.2
  have h3 : (4 * ω) ^ 2 * ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2
      ≤ |(4 * ω) ^ 2 * ∫ τ : ℝ, ‖normalizedMobiusCausalDeriv ω ((τ : ℂ) * Complex.I)‖ ^ 2| :=
    le_abs_self _
  linarith

end

end RHTower
