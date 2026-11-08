import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# Charged Weil profiles have strong subsequential limits

The physical profile is precompact under bounded Weil energy and eighth mass.
A bounded scalar pole coordinate survives a further subsequence, preserving
the joint normalization exactly.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RHTower SpacingScaleHarmonicAnalysis

/-- Jointly normalized profiles and pole coordinates retain unit joint mass in a strong limit. -/
theorem exists_strong_charged_limit_of_bounded_weilQuad {V : ℕ → ℝ → ℝ} {β : ℕ → ℝ}
    (hVd : ∀ k, ContDiff ℝ 2 (V k)) (hVc : ∀ k, HasCompactSupport (V k))
    (hnorm : ∀ k, (∫ u, V k u ^ 2) + β k ^ 2 = 1)
    {M₈ : ℝ} (hM₈0 : 0 ≤ M₈)
    (hV₈ : ∀ k, (∫ u, V k u ^ 2 * Real.exp (-(8 * u))) ≤ M₈)
    (hsupp : ∀ (k : ℕ) (u : ℝ), 1 / ((k : ℝ) + 1) < u → V k u = 0)
    {b : ℝ} (hVq : ∀ k, weilQuad (V k) ≤ b) :
    ∃ (F : ℝ → ℝ) (β₀ : ℝ) (s : ℕ → ℕ), StrictMono s ∧
      Measurable F ∧ Integrable F ∧ Integrable (fun u => F u ^ 2) ∧
      (∫ u, F u ^ 2) + β₀ ^ 2 = 1 ∧
      Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))) ∧
      (∫ u, F u ^ 2 * Real.exp (-(8 * u))) ≤ M₈ ∧
      (∀ u, 0 ≤ u → F u = 0) ∧
      Tendsto (fun j => ∫ u, (V (s j) u - F u) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun j => ∫ u, ‖V (s j) u - F u‖) atTop (𝓝 0) ∧
      Tendsto (fun j => β (s j)) atTop (𝓝 β₀) := by
  have hmass : ∀ k, (∫ u, V k u ^ 2) ≤ 1 := fun k => by
    have hh := hnorm k
    linarith only [hh, sq_nonneg (β k)]
  have hβ : ∀ k, β k ∈ Icc (-1 : ℝ) 1 := by
    intro k
    have h0 : 0 ≤ ∫ u, V k u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hsq : β k ^ 2 ≤ 1 := by linarith only [hnorm k, h0]
    constructor <;> nlinarith only [hsq, sq_nonneg (β k + 1), sq_nonneg (β k - 1)]
  obtain ⟨F, s, hs, hFm, hFi, hF2, hFmass, hF8, hF8bound, hFzero, hL2, hL1, hmasslim⟩ :=
    exists_strong_negative_limit_of_bounded_weilQuad hVd hVc hmass hM₈0 hV₈ hsupp hVq
  obtain ⟨β₀, _, t, ht, hβlim⟩ := isCompact_Icc.isSeqCompact (fun k => hβ (s k))
  have hsum : Tendsto (fun j => (∫ u, V (s (t j)) u ^ 2) + β (s (t j)) ^ 2)
      atTop (𝓝 ((∫ u, F u ^ 2) + β₀ ^ 2)) :=
    (hmasslim.comp ht.tendsto_atTop).add (hβlim.pow 2)
  have hnormlim : (∫ u, F u ^ 2) + β₀ ^ 2 = 1 :=
    tendsto_nhds_unique hsum (by simpa only [hnorm] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  exact ⟨F, β₀, s ∘ t, hs.comp ht, hFm, hFi, hF2, hnormlim, hF8, hF8bound,
    hFzero, hL2.comp ht.tendsto_atTop, hL1.comp ht.tendsto_atTop, hβlim⟩

#print axioms exists_strong_charged_limit_of_bounded_weilQuad
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
