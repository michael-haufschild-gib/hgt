/-
# `hno` from a single-scale basis-family basin branch (A6, consumer variant)

`RelativeRigidityCapstone.noRelation_phiMero_of_basin_branch` reduces the connected-case bivariate
no-relation to a per-relation geometric datum whose dendrite-tip clause is the *all-scales*
punctured-basin preconnectivity `∀ρ, IsPreconnected (ball z₀ ρ ∩ K_{c₁}ᶜ)`.  The linearization
collapse (`ScaleCollapse` / `DendriteTipDischarge`) shows that datum is only ever consumed at ONE
scale, and produces instead a shrinking **preconnected basis family** `T t` with a fat-margin clause.

This file supplies the matching consumer: the same reduction with the all-scales clause replaced by
the three `T`-family clauses, delegating to `false_of_global_basin_branch_analytic_basisApproach`
instead of `false_of_global_basin_branch_analytic`.  It is the exact interface the
`SectorConnectorProp`-conditional discharge (`false_of_basin_branch_at_betaFixed`) plugs into.
Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RelativeRigidityCapstone
import GaloisForLFunctions.Bottcher.RelativeDenseApproach

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **`hno` from a basis-family basin branch (T-family variant of
`noRelation_phiMero_of_basin_branch`).** For each nonzero cleared relation vanishing on `U`, given a
continued analytic coefficient family `a` with separable nondegenerate fibre at a dendrite tip
`z₀ ∈ J_{c₁}` (`hempty`), a shrinking preconnected basis family `T t ⊆ ball z₀ t ∩ K_{c₁}ᶜ` with
fat-margin coverage of `K_{c₁}ᶜ ∩ ball z₀ (t/2)`, and a basin Böttcher branch `β` carrying the
relation and the genuine modulus on the basin sector `ball z₀ r ∩ K_{c₁}ᶜ`, the pair carries no
bivariate relation over `ℂ(z)`.  `false_of_global_basin_branch_analytic_basisApproach` does the rest.
This is the single-scale replacement for `noRelation_phiMero_of_basin_branch`. -/
theorem noRelation_phiMero_of_basin_branch_basisApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (a : ℕ → ℂ → ℂ) (N : ℕ) (z₀ : ℂ) (r : ℝ) (β : ℂ → ℂ) (T : ℝ → Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀) ∧
          a N z₀ ≠ 0 ∧ (fibrePoly a s z₀).Separable ∧
          0 < r ∧ z₀ ∈ filledJulia c₁ ∧ ball z₀ r ∩ interior (filledJulia c₁) = ∅ ∧
          (∀ t : ℝ, 0 < t → t ≤ r → T t ⊆ ball z₀ t ∩ (filledJulia c₁)ᶜ) ∧
          (∀ t : ℝ, 0 < t → t ≤ r → IsPreconnected (T t)) ∧
          (∀ t : ℝ, 0 < t → t ≤ r → (filledJulia c₁)ᶜ ∩ ball z₀ (t/2) ⊆ T t) ∧
          ContinuousOn β (ball z₀ r ∩ (filledJulia c₁)ᶜ) ∧
          (∀ z ∈ ball z₀ r ∩ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0) ∧
          (∀ z ∈ ball z₀ r ∩ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨a, N, z₀, r, β, T, hsupp, hN, hN1, ha, hlead, hsep, hr, hz₀, hempty,
    hT_sub, hT_pre, hT_fat, hβc, hβrel, hβmod⟩ := hinput Q s hnt hEqOn
  exact false_of_global_basin_branch_analytic_basisApproach hsupp hN hN1 ha hlead hsep hr hz₀
    hempty hT_sub hT_pre hT_fat hβc hβrel hβmod

end Bottcher
