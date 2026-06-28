import GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary
import GaloisForLFunctions.Bottcher.Q62ConnectedAssembly
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from level-root branches, sparse generic crossing, common-basin geometry, and an
abstract natural-boundary predicate.** The level-root towers construct the basin branches internally; the
natural-boundary input is a callback applying to any basin branch matching the Böttcher germ on
`escapeOpen c₁`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγpow : ∀ n, ∀ z ∈ escapeLevel c₂ n,
      (γlev n z) ^ (2 ^ n) = bottcherCoord c₂ ((quadratic c₂)^[n] z))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, _hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hβanalytic hβpow hβne hβanchorEsc
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₂ γlev hγanalytic hγpow hγne hγanchorEsc
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan
    (fun z hz => hγesc z (hU₂ hz)) (hnb β hβan hβesc) (hinput γ hγan hγesc)

/-- **hRigid from level-root branches, sparse generic crossing, common-basin geometry, and an abstract
natural-boundary predicate.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_level_roots_offOther_crossing`. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγpow : ∀ n, ∀ z ∈ escapeLevel c₂ n,
      (γlev n z) ^ (2 ^ n) = bottcherCoord c₂ ((quadratic c₂)^[n] z))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hnb hinput)

/-- **Connected-case `q62` endpoint from abstract natural-boundary level-root crossing.** This is the
level-root counterpart of the square-root endpoint below: once the natural-boundary obstruction and
common-basin crossing geometry are constructed, the result feeds the connected `q62` carrier directly. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγpow : ∀ n, ∀ z ∈ escapeLevel c₂ n,
      (γlev n z) ^ (2 ^ n) = bottcherCoord c₂ ((quadratic c₂)^[n] z))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hnb hinput)

/-- **Connected-case natural-boundary level-root crossing with `φ_{c₂}` transcendence produced
internally.** This removes the abstract `hG` input from
`q62_independence_connected_of_naturalBoundary_commonBasin_level_roots_offOther_crossing` using the
finite fixed-point avoidance transcendence interface. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_level_roots_offOther_crossing_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ p : ℕ,
          squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c₂ hU₂ P hP0 hPrel hPmin p) ∅ <
            (strongFixedPointRoots c₂ p).card)
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγpow : ∀ n, ∀ z ∈ escapeLevel c₂ n,
      (γlev n z) ^ (2 ^ n) = bottcherCoord c₂ ((quadratic c₂)^[n] z))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_naturalBoundary_commonBasin_level_roots_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hnb hinput

/-- **NoRelation from square-root towers, sparse generic crossing, common-basin geometry, and an
    abstract natural-boundary predicate.** The square-root families now construct the modulus-carrying
global basin branches directly; the `2^n` power laws are internal to
`exists_global_branch_of_sqrt_family_modulus`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ 2 = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ 2 = γlev n (quadratic c₂ z))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, _hβmod⟩ :=
    exists_global_branch_of_sqrt_family_modulus c₁ βlev hβanalytic hβne hβanchorEsc hβsqrt
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_sqrt_family_modulus c₂ γlev hγanalytic hγne hγanchorEsc hγsqrt
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan
    (fun z hz => hγesc z (hU₂ hz)) (hnb β hβan hβesc) (hinput γ hγan hγesc)

/-- **hRigid from square-root towers, sparse generic crossing, common-basin geometry, and an abstract
natural-boundary predicate.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing`. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ 2 = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ 2 = γlev n (quadratic c₂ z))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput)

/-- **Connected-case `q62` endpoint from abstract natural-boundary square-root crossing.** This is the
E-vS-facing analogue of the empty-interior square-root endpoint: once the natural-boundary obstruction
and common-basin crossing geometry are constructed, the result feeds the connected `q62` carrier
directly. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ 2 = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ 2 = γlev n (quadratic c₂ z))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput)

/-- **Connected-case natural-boundary square-root crossing with `φ_{c₂}` transcendence produced
internally.** This removes the abstract `hG` input from
`q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing` using the
finite fixed-point avoidance transcendence interface. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ p : ℕ,
          squarefreeBadDegreeBudget P
              (chosenCompRelDenom hUo hUne c₂ hU₂ P hP0 hPrel hPmin p) ∅ <
            (strongFixedPointRoots c₂ p).card)
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ 2 = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ 2 = γlev n (quadratic c₂ z))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput

/-- **Connected-case natural-boundary square-root crossing with asymptotic `c₂` production.**
This is the same hRigid endpoint as
`q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_repellingG`,
but the absolute `c₂` input no longer hand-picks a period or proves a direct cardinality inequality.
It supplies finite eventual supports for the non-strong and multiplier-one fixed roots, plus a uniform
local duplicate-excess bound on the multiplier-one support.  Lean builds the content denominator,
derives the root-defect inequality, supplies exponential domination, and chooses a large period
internally. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_eventualG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E F : Finset ℂ) (L : ℕ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
            multiplierOneFixedPointRoots c₂ p ⊆ F ∧
            (∀ z ∈ (fixedPointPoly c₂ p).roots.toFinset, z ∈ F →
              (fixedPointPoly c₂ p).roots.count z - 1 ≤ L)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c₂ p ⊆ E))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ 2 = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ 2 = γlev n (quadratic c₂ z))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_eventually_multiplierOne_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput

/-- **NoRelation from simply-connected escape levels, sparse crossing, common-basin geometry, and an
abstract natural-boundary predicate.** This removes the terminal square-root tower data from the
natural-boundary crossing route: if each successor escape level for both parameters is simply connected,
`exists_sqrt_family_of_simplyConnected_levels` creates the two coherent square-root families, and the
existing square-root endpoint creates the modulus-carrying global basin branches. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_simplyConnectedLevels_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hβsc : ∀ n, IsSimplyConnected (escapeLevel c₁ (n + 1)))
    (hγsc : ∀ n, IsSimplyConnected (escapeLevel c₂ (n + 1)))
    (hnb : ∀ β : ℂ → ℂ,
        AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨βlev, hβanalytic, hβne, hβanchorEsc, hβsqrt⟩ :=
    exists_sqrt_family_of_simplyConnected_levels c₁ hβsc
  obtain ⟨γlev, hγanalytic, hγne, hγanchorEsc, hγsqrt⟩ :=
    exists_sqrt_family_of_simplyConnected_levels c₂ hγsc
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput

/-- **NoRelation from empty interior, simply-connected escape levels, and common-basin crossing.**
This is the dendrite/empty-interior specialization of
`noRelation_phiMero_of_naturalBoundary_commonBasin_simplyConnectedLevels_offOther_crossing`: the
natural-boundary predicate and the two coherent square-root towers are both created internally.  The
remaining input is the common-basin sparse crossing geometry for the continued `c₂` branch. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_simplyConnectedLevels_offOther_crossing
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hβsc : ∀ n, IsSimplyConnected (escapeLevel c₁ (n + 1)))
    (hγsc : ∀ n, IsSimplyConnected (escapeLevel c₂ (n + 1)))
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ),
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
            V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨βlev, hβanalytic, hβne, hβanchorEsc, hβsqrt⟩ :=
    exists_sqrt_family_of_simplyConnected_levels c₁ hβsc
  obtain ⟨γlev, hγanalytic, hγne, hγanchorEsc, hγsqrt⟩ :=
    exists_sqrt_family_of_simplyConnected_levels c₂ hγsc
  exact noRelation_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput

end Bottcher
