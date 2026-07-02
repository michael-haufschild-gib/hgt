/-
# The dendrite-tip obstruction at β, conditional on the sector connector

Glues the basis family produced by the linearization collapse (`koenigs_basis_family`) into the
single-scale obstruction interface (`false_of_global_basin_branch_analytic_basisApproach`):
for a real dendrite parameter, no relation with separable nondegenerate fibre at the extreme
Julia point `β` can carry a modulus-preserving basin branch — conditionally on
`SectorConnectorProp` (Open Problem 1), which is the ONLY remaining input.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.ScaleCollapse
import GaloisForLFunctions.Bottcher.RelativeDenseApproach

open Complex Set Metric

namespace Bottcher

/-- **A2: the htip discharge at the extreme Julia point** (conditional on Open Problem 1).
For real dendrite `c`, a cleared relation with separable nondegenerate fibre at
`z₀ = β = betaFixed c` admitting a modulus-preserving continuous basin branch near `β`
is impossible. -/
theorem false_of_basin_branch_at_betaFixed {c : ℝ} (hc0 : c ≤ 0)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀32 : ρ₀ ≤ 1 / 32)
    (hfund : SectorConnectorProp (c:ℂ) ((betaFixed c : ℝ) : ℂ) ρ₀)
    (hden : interior (filledJulia (c:ℂ)) = ∅)
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) ((betaFixed c : ℝ) : ℂ))
    (hlead : a N ((betaFixed c : ℝ) : ℂ) ≠ 0)
    (hsep : (fibrePoly a s ((betaFixed c : ℝ) : ℂ)).Separable)
    {β : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hβc : ContinuousOn β
      (Metric.ball ((betaFixed c : ℝ) : ℂ) r ∩ (filledJulia (c:ℂ))ᶜ))
    (hβrel : ∀ z ∈ Metric.ball ((betaFixed c : ℝ) : ℂ) r ∩ (filledJulia (c:ℂ))ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ z ∈ Metric.ball ((betaFixed c : ℝ) : ℂ) r ∩ (filledJulia (c:ℂ))ᶜ,
        ‖β z‖ = Real.exp (greenFunctionDyn (c:ℂ) z)) :
    False := by
  classical
  obtain ⟨rT, hrT, hfam⟩ := koenigs_basis_family hc0 hρ₀ hρ₀32 hfund
  -- the working radius and the T-function via choice
  set r' : ℝ := min r rT with hr'def
  have hr' : 0 < r' := lt_min hr hrT
  have hchoice : ∀ t : ℝ, ∃ T : Set ℂ,
      (0 < t → t ≤ r' →
        T ⊆ Metric.ball ((betaFixed c : ℝ) : ℂ) t ∩ (filledJulia (c:ℂ))ᶜ ∧
        IsPreconnected T ∧
        (filledJulia (c:ℂ))ᶜ ∩ Metric.ball ((betaFixed c : ℝ) : ℂ) (t/2) ⊆ T) := by
    intro t
    by_cases hcase : 0 < t ∧ t ≤ r'
    · obtain ⟨T, hT⟩ := hfam t hcase.1 (le_trans hcase.2 (min_le_right _ _))
      exact ⟨T, fun _ _ => hT⟩
    · refine ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hcase⟩
  choose T hT using hchoice
  refine false_of_global_basin_branch_analytic_basisApproach
    (T := T) (β := β) hsupp hN hN1 ha hlead hsep hr'
    (betaFixed_mem_filledJulia hc0) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- empty interior on the ball
    rw [hden, Set.inter_empty]
  · intro t ht htle
    exact (hT t ht htle).1
  · intro t ht htle
    exact (hT t ht htle).2.1
  · intro t ht htle
    exact (hT t ht htle).2.2
  · exact hβc.mono (Set.inter_subset_inter_left _
      (Metric.ball_subset_ball (min_le_left _ _)))
  · intro z hz
    exact hβrel z ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  · intro z hz
    exact hβmod z ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩

end Bottcher
