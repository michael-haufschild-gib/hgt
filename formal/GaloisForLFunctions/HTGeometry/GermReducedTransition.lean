import GaloisForLFunctions.HTGeometry.GermCoprimeOpen
import GaloisForLFunctions.HTGeometry.GermRatioBound
import GaloisForLFunctions.HTGeometry.GermTranslationFactorial

/-!
# The transition bound for reduced local presentations

Two reduced presentations of the same meromorphic germ have associated denominators, hence
representatives whose ratio is bounded both ways.  Reducedness is a condition at one point, but a
chartwise comparison happens on the *overlap* of two charts, away from either centre.  Coprimality
of germs is an open condition, so reducedness at the centre already gives reducedness at every
nearby point, and the comparison constant exists on the whole overlap.

This is the bound a chartwise Siegel-type count needs, and the one a global entire presentation
cannot supply: the ratio of two arbitrary presentations of the same meromorphic function is
unbounded along the divisor the two numerators and denominators share.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Reduced presentations of the same germ fraction have associated denominators**, at an
arbitrary point of `ℂ^n`. -/
theorem associated_den_of_reduced_at {w : Fin n → ℂ} {A₁ B₁ A₂ B₂ : (Fin n → ℂ) → ℂ}
    (hA₁ : AnalyticAt ℂ A₁ w) (hB₁ : AnalyticAt ℂ B₁ w)
    (hA₂ : AnalyticAt ℂ A₂ w) (hB₂ : AnalyticAt ℂ B₂ w)
    (hred₁ : IsRelPrime (analyticGermOf hA₁) (analyticGermOf hB₁))
    (hred₂ : IsRelPrime (analyticGermOf hA₂) (analyticGermOf hB₂))
    (hcross : (fun v => A₁ v * B₂ v) =ᶠ[𝓝 w] fun v => A₂ v * B₁ v) :
    Associated (analyticGermOf hB₁) (analyticGermOf hB₂) := by
  letI := uniqueFactorizationMonoid_analyticGerm w
  refine associated_den_of_reduced hred₁ hred₂ ?_
  rw [← analyticGermOf_mul hA₁ hB₂, ← analyticGermOf_mul hA₂ hB₁]
  exact analyticGermOf_congr _ _ hcross

/-- **The two-sided comparison of two reduced denominators.** -/
theorem exists_two_sided_ratio_bound_of_reduced_at {w : Fin n → ℂ}
    {A₁ B₁ A₂ B₂ : (Fin n → ℂ) → ℂ}
    (hA₁ : AnalyticAt ℂ A₁ w) (hB₁ : AnalyticAt ℂ B₁ w)
    (hA₂ : AnalyticAt ℂ A₂ w) (hB₂ : AnalyticAt ℂ B₂ w)
    (hred₁ : IsRelPrime (analyticGermOf hA₁) (analyticGermOf hB₁))
    (hred₂ : IsRelPrime (analyticGermOf hA₂) (analyticGermOf hB₂))
    (hcross : (fun v => A₁ v * B₂ v) =ᶠ[𝓝 w] fun v => A₂ v * B₁ v) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ (∀ v ∈ ball w r, ‖B₂ v‖ ≤ C * ‖B₁ v‖)
      ∧ ∀ v ∈ ball w r, ‖B₁ v‖ ≤ C * ‖B₂ v‖ := by
  have hassoc : Associated (analyticGermOf hB₁) (analyticGermOf hB₂) :=
    associated_den_of_reduced_at hA₁ hB₁ hA₂ hB₂ hred₁ hred₂ hcross
  obtain ⟨r₁, C₁, hr₁, hC₁, hspec₁⟩ := exists_ratio_bound_of_associated hB₁ hB₂ hassoc
  obtain ⟨r₂, C₂, hr₂, hC₂, hspec₂⟩ := exists_ratio_bound_of_associated hB₂ hB₁ hassoc.symm
  refine ⟨min r₁ r₂, max C₁ C₂, lt_min hr₁ hr₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_, ?_⟩
  · intro v hv
    refine le_trans (hspec₁ v (ball_subset_ball (min_le_left _ _) hv)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · intro v hv
    refine le_trans (hspec₂ v (ball_subset_ball (min_le_right _ _) hv)) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- **The transition bound on an overlap.**  Two presentations that are reduced at their own
centres are boundedly comparable near every point of the overlap of the two charts, wherever they
present the same fraction. -/
theorem eventually_ratio_bound_of_reduced_centres {c₁ c₂ : Fin (n + 1) → ℂ}
    {A₁ B₁ A₂ B₂ : (Fin (n + 1) → ℂ) → ℂ}
    (hA₁ : AnalyticAt ℂ A₁ c₁) (hB₁ : AnalyticAt ℂ B₁ c₁)
    (hA₂ : AnalyticAt ℂ A₂ c₂) (hB₂ : AnalyticAt ℂ B₂ c₂)
    (hred₁ : IsRelPrime (analyticGermOf hA₁) (analyticGermOf hB₁))
    (hred₂ : IsRelPrime (analyticGermOf hA₂) (analyticGermOf hB₂)) :
    ∀ᶠ w in 𝓝 c₁ ⊓ 𝓝 c₂,
      ∀ (_h₁ : AnalyticAt ℂ A₁ w) (_h₂ : AnalyticAt ℂ B₁ w) (_h₃ : AnalyticAt ℂ A₂ w)
        (_h₄ : AnalyticAt ℂ B₂ w),
        ((fun v => A₁ v * B₂ v) =ᶠ[𝓝 w] fun v => A₂ v * B₁ v) →
        ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ (∀ v ∈ ball w r, ‖B₂ v‖ ≤ C * ‖B₁ v‖)
          ∧ ∀ v ∈ ball w r, ‖B₁ v‖ ≤ C * ‖B₂ v‖ := by
  have hprop₁ := eventually_isRelPrime_germ hA₁ hB₁ hred₁
  have hprop₂ := eventually_isRelPrime_germ hA₂ hB₂ hred₂
  have hp₁ : ∀ᶠ w in 𝓝 c₁ ⊓ 𝓝 c₂, ∀ (h₁ : AnalyticAt ℂ A₁ w) (h₂ : AnalyticAt ℂ B₁ w),
      IsRelPrime (analyticGermOf h₁) (analyticGermOf h₂) :=
    hprop₁.filter_mono inf_le_left
  have hp₂ : ∀ᶠ w in 𝓝 c₁ ⊓ 𝓝 c₂, ∀ (h₃ : AnalyticAt ℂ A₂ w) (h₄ : AnalyticAt ℂ B₂ w),
      IsRelPrime (analyticGermOf h₃) (analyticGermOf h₄) :=
    hprop₂.filter_mono inf_le_right
  filter_upwards [hp₁, hp₂] with w hw₁ hw₂ h₁ h₂ h₃ h₄ hcross
  exact exists_two_sided_ratio_bound_of_reduced_at h₁ h₂ h₃ h₄ (hw₁ h₁ h₂) (hw₂ h₃ h₄) hcross

end GaloisForLFunctions.HTGeometry
