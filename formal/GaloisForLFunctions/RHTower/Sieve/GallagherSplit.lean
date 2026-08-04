import GaloisForLFunctions.RHTower.Sieve.GallagherTail

/-!
# Gallagher's identity, split at a frequency height

The weight has total mass `δ` and carries at most `1/(π²W)` beyond height `W` on each side.  So a
bound on the Dirichlet polynomial valid only for `|w| ≤ W`, together with the trivial bound valid
everywhere, gives

    ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du ≤ M₁·δ + M₂·2/(π²W) .

This is the shape a frequency-restricted cancellation estimate is consumed in: the good range pays
the total mass, the bad range pays only the tail.
-/

namespace RHTower.Sieve

open Complex MeasureTheory FourierTransform

/-- The left tail of the weight equals the right tail, by evenness. -/
theorem integral_Iic_fourier_triC_re_eq {δ : ℝ} (hδ : 0 < δ) (W : ℝ) :
    (∫ w in Set.Iic (-W), (𝓕 (triC δ) w).re)
      = ∫ w in Set.Ioi W, (𝓕 (triC δ) w).re := by
  have hcongr : (∫ w in Set.Iic (-W), (𝓕 (triC δ) w).re)
      = ∫ w in Set.Iic (-W), (𝓕 (triC δ) (-w)).re :=
    setIntegral_congr_fun measurableSet_Iic
      (fun x _ => by rw [fourier_triC_even hδ])
  rw [hcongr]
  have := integral_comp_neg_Iic (-W) (fun x : ℝ => (𝓕 (triC δ) x).re)
  simpa using this

/-- **The mass of the weight outside a symmetric band.** -/
theorem integral_compl_Icc_fourier_triC_re_le {δ : ℝ} (hδ : 0 < δ) {W : ℝ} (hW : 0 < W) :
    (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re) ≤ 2 / (Real.pi ^ 2 * W) := by
  have hK : Integrable fun w : ℝ => (𝓕 (triC δ) w).re := (integrable_fourier_triC hδ).re
  have hnn : 0 ≤ᵐ[volume] fun w : ℝ => (𝓕 (triC δ) w).re :=
    Filter.Eventually.of_forall (fourier_triC_re_nonneg hδ)
  have hsub : (Set.Icc (-W) W)ᶜ ⊆ Set.Iic (-W) ∪ Set.Ioi W := by
    intro x hx
    rcases le_or_gt x (-W) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rcases le_or_gt x W with h' | h'
      · exact absurd (Set.mem_Icc.2 ⟨h.le, h'⟩) hx
      · exact h'
  have hdisj : Disjoint (Set.Iic (-W)) (Set.Ioi W) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ -W := hx
    have h2 : W < x := hx'
    linarith
  have hunion : (∫ w in Set.Iic (-W) ∪ Set.Ioi W, (𝓕 (triC δ) w).re)
      = (∫ w in Set.Iic (-W), (𝓕 (triC δ) w).re)
        + ∫ w in Set.Ioi W, (𝓕 (triC δ) w).re :=
    setIntegral_union hdisj measurableSet_Ioi hK.integrableOn hK.integrableOn
  have hmono : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re)
      ≤ ∫ w in Set.Iic (-W) ∪ Set.Ioi W, (𝓕 (triC δ) w).re :=
    setIntegral_mono_set hK.integrableOn (ae_restrict_of_ae hnn)
      (Filter.Eventually.of_forall hsub)
  have htail := integral_Ioi_fourier_triC_re_le hδ hW
  rw [hunion, integral_Iic_fourier_triC_re_eq hδ] at hmono
  have hW2 : (0 : ℝ) < Real.pi ^ 2 * W := by positivity
  calc (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re)
      ≤ (∫ w in Set.Ioi W, (𝓕 (triC δ) w).re)
          + ∫ w in Set.Ioi W, (𝓕 (triC δ) w).re := hmono
    _ ≤ 1 / (Real.pi ^ 2 * W) + 1 / (Real.pi ^ 2 * W) := by linarith
    _ = 2 / (Real.pi ^ 2 * W) := by ring

/-- **Gallagher's identity, split at a frequency height.** -/
theorem gallagher_split (a : ℕ → ℂ) (s : Finset ℕ) {δ M₁ M₂ W : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) :
    (∫ u : ℝ, ‖logWindowSum a s δ u‖ ^ 2) ≤ M₁ * δ + M₂ * (2 / (Real.pi ^ 2 * W)) := by
  have hK : Integrable fun w : ℝ => (𝓕 (triC δ) w).re := (integrable_fourier_triC hδ).re
  have hnn : 0 ≤ᵐ[volume] fun w : ℝ => (𝓕 (triC δ) w).re :=
    Filter.Eventually.of_forall (fourier_triC_re_nonneg hδ)
  have hF : Integrable fun w : ℝ => (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2 :=
    integrable_gallagher_weight_mul hδ a s
  rw [gallagher_identity a s hδ]
  rw [← integral_add_compl (measurableSet_Icc (a := -W) (b := W)) hF]
  have hin : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2) ≤ M₁ * δ := by
    have hstep : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re * M₁ := by
      refine setIntegral_mono_on hF.integrableOn (hK.mul_const M₁).integrableOn
        measurableSet_Icc fun w hw => ?_
      exact mul_le_mul_of_nonneg_left (h₁ w hw) (fourier_triC_re_nonneg hδ w)
    refine le_trans hstep ?_
    rw [integral_mul_const]
    have hmass : (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re) ≤ δ := by
      have h := setIntegral_le_integral (s := Set.Icc (-W) W) hK hnn
      rwa [integral_fourier_triC_re hδ] at h
    calc (∫ w in Set.Icc (-W) W, (𝓕 (triC δ) w).re) * M₁ ≤ δ * M₁ :=
          mul_le_mul_of_nonneg_right hmass hM₁
      _ = M₁ * δ := by ring
  have hout : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
      ≤ M₂ * (2 / (Real.pi ^ 2 * W)) := by
    have hstep : (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * ‖logPoly a s w‖ ^ 2)
        ≤ ∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re * M₂ := by
      refine setIntegral_mono_on hF.integrableOn (hK.mul_const M₂).integrableOn
        (measurableSet_Icc.compl) fun w _ => ?_
      exact mul_le_mul_of_nonneg_left (h₂ w) (fourier_triC_re_nonneg hδ w)
    refine le_trans hstep ?_
    rw [integral_mul_const]
    have hmass := integral_compl_Icc_fourier_triC_re_le hδ hW
    calc (∫ w in (Set.Icc (-W) W)ᶜ, (𝓕 (triC δ) w).re) * M₂
        ≤ (2 / (Real.pi ^ 2 * W)) * M₂ := mul_le_mul_of_nonneg_right hmass hM₂
      _ = M₂ * (2 / (Real.pi ^ 2 * W)) := by ring
  linarith

end RHTower.Sieve
