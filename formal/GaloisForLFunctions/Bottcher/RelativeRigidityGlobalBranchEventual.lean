import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranch
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62 frontier-analytic endpoint with asymptotic `c₂` production.**

This is the event-data version of
`q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable_repellingG`.
The `φ_{c₂}` transcendence input is produced internally from finite eventual support for
multiplier-one roots, pointwise analytic-order bounds on that support, and eventual containment of
non-strong roots.  The remaining `c₁` datum is the native frontier separable nonresonant periodic
fibre required by the hRigid branch. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable_eventualG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c₂ p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
              analyticOrderAt (fun y : ℂ => (fixedPointPoly c₂ p).eval y) z ≤
                ((Lz + 1 : ℕ) : ℕ∞)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c₂ p ⊆ E))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβfront : AnalyticOnNhd ℂ β (frontier (filledJulia c₁)))
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ : ℂ) (p : ℕ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          (quadratic c₁)^[p] z₀ = z₀ ∧
          (∀ m : ℕ, 1 ≤ m →
            (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseAnalyticOrder_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod
      hγan hγfront hγmatch hinput)

end Bottcher
