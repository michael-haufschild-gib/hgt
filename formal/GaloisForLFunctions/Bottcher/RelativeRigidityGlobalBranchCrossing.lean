/-
# hRigid global branch endpoint with sparse generic crossing

This file removes one terminal datum from the strongest global-branch hRigid endpoint:
the selected frontier fibre is no longer assumed separable pointwise.  Instead, a
single full-degree separable fibre on a preconnected analytic region plus an
accumulating target set produces the required separable frontier point by the
resultant/discriminant crossing lemma in `RelativeFibreGeneric`.

New focused file, kept separate from `RelativeRigidityGlobalBranch.lean`.
-/
import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranch
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.RepellingPeriodicFrontier
import GaloisForLFunctions.Bottcher.ConnectedRepellingPeriodicAvoidance
import GaloisForLFunctions.Bottcher.ConnectedRepellingStrongRoots
import Mathlib.Topology.ClusterPt

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from global branches and sparse generic crossing.**  The callback no longer supplies
`(fibrePoly ... z₀).Separable` directly.  It supplies an analytic preconnected region, one full-degree
separable specialization, and an accumulating set of frontier periodic nonresonant targets; sparse
generic crossing chooses the target where the fibre is separable. -/
theorem noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
          (∀ z₀ ∈ S, z₀ ∈ frontier (filledJulia c₁) ∧
            ∃ p : ℕ,
              (quadratic c₁)^[p] z₀ = z₀ ∧
              ∀ m : ℕ, 1 ≤ m →
                (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum, hgeom⟩ := hinput Q s hnt hEqOn
        let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
        obtain ⟨z₀, hz₀S, _hlead₀, hsep₀⟩ :=
          exists_sparse_fibre_separable_crossing (a := a) (s := s) (N := N)
            hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum
        obtain ⟨hfront, p, hFz, hres⟩ := hgeom z₀ hz₀S
        exact ⟨z₀, p, hsep₀, hfront, hFz, hres⟩)

/-- **hRigid from global branches and sparse generic crossing.** This is the
`TranscendentalOverAdjoin` package of
`noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
          (∀ z₀ ∈ S, z₀ ∈ frontier (filledJulia c₁) ∧
            ∃ p : ℕ,
              (quadratic c₁)^[p] z₀ = z₀ ∧
              ∀ m : ℕ, 1 ≤ m →
                (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **Connected q62 endpoint from global branches and sparse generic crossing, with `φ_{c₂}`
transcendence produced internally.** The remaining callback is geometric/dynamical: it supplies an
accumulating set of frontier periodic nonresonant targets plus one full-degree separable specialization;
the chosen separable target is produced internally. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
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
          (∀ z₀ ∈ S, z₀ ∈ frontier (filledJulia c₁) ∧
            ∃ p : ℕ,
              (quadratic c₁)^[p] z₀ = z₀ ∧
              ∀ m : ℕ, 1 ≤ m →
                (deriv ((quadratic c₁)^[p]) z₀) ^ m ≠ ((2 ^ p : ℕ) : ℂ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **hRigid from global branches and sparse generic crossing, deriving the frontier and
canonical nonresonance data from strong periodic repulsion.**  The callback only supplies an
accumulating set of periodic targets with the hRigid orbit-product bound. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum, hgeom⟩ := hinput Q s hnt hEqOn
        refine ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum, ?_⟩
        intro z₀ hz₀S
        obtain ⟨p, hFz, hnorm⟩ := hgeom z₀ hz₀S
        exact ⟨mem_frontier_of_strongly_repelling_periodic_orbitProduct hFz hnorm, p, hFz,
          deriv_nonresonant_of_strongly_repelling_periodic_orbitProduct hnorm⟩)

/-- **hRigid from global branches and local infinite strong-periodic supply.**

The callback no longer has to manufacture the accumulating point.  It supplies an infinite set of
strongly repelling periodic targets trapped in a closed ball contained in the analytic crossing region;
compactness of the Julia frontier creates the accumulation point internally. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w a : ℂ) (r : ℝ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          S.Infinite ∧
          S ⊆ Metric.closedBall a r ∧
          Metric.closedBall a r ⊆ Ω ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, a, r, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hSinf, hSball, hballΩ, hgeom⟩ := hinput Q s hnt hEqOn
        obtain ⟨z₁, hz₁Ω, _hz₁front, haccum⟩ :=
          exists_omega_accumulation_of_infinite_strongly_repelling_periodic_set_closedBall
            hSinf hSball hballΩ hgeom
        exact ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hz₁Ω, accPt_iff_frequently_nhdsNE.mp haccum, hgeom⟩)

/-- **hRigid from an interior strong-periodic accumulation point.**

This is the local-density bridge for the closed-ball route: the callback supplies an accumulation
point of strong-periodic targets in the interior of the analytic crossing region, and Lean shrinks it
to an infinite closed-ball supply inside that region. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ interior Ω ∧
          AccPt z₁ (𝓟 S) ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hz₁Ω, hacc, hgeom⟩ := hinput Q s hnt hEqOn
        obtain ⟨r, Slocal, _hr, hSinf, hSball, hballΩ, hgeomLocal⟩ :=
          exists_closedBall_strongly_repelling_periodic_set_of_accPt_in_interior
            (c := c₁) (p := z₁) (Ω := Ω) hz₁Ω hacc hgeom
        exact ⟨N, Ω, w, z₁, r, Slocal, hsupp, hN, hN1, hΩc, ha, hw, hleadw,
          hsepw, hSinf, hSball, hballΩ, hgeomLocal⟩)

/-- **hRigid from global branches, perfect Julia frontier, and dense strong periodic targets.**

The callback supplies a frontier seed inside the analytic crossing region.  Perfectness of the Julia
frontier and density of strong fixed roots create the local closed-ball strong-periodic supply
internally. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ interior Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hpfront, hpΩ⟩ := hinput Q s hnt hEqOn
        obtain ⟨r, S, _hr, hSinf, hSball, hballΩ, hgeom⟩ :=
          exists_closedBall_strongFixedPointRoots_supply_of_perfect_frontier_dense
            hfront hpfront hpΩ hdense
        exact ⟨N, Ω, w, p, r, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hSinf, hSball, hballΩ, hgeom⟩)

/-- **hRigid from connected empty-interior Julia set and frontier-dense strong roots.**

This is the non-`Perfect` variant of
`hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall`:
preconnectedness and empty interior of `K_{c₁}` supply the local frontier uncountability needed by
the strong-root density bridge. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ interior Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hpK, hpΩ⟩ := hinput Q s hnt hEqOn
        obtain ⟨r, S, _hr, hSinf, hSball, hballΩ, hgeom⟩ :=
          exists_closedBall_strongFixedPointRoots_supply_of_frontier_dense
            hKconn hempty hpK hpΩ hdense
        exact ⟨N, Ω, w, p, r, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw,
          hSinf, hSball, hballΩ, hgeom⟩)

/-- **Connected q62 from connected empty-interior Julia set and frontier-dense strong roots.**

This is the q62 form of
`hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall`. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ interior Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hKconn hempty hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch hinput)

/-- **Connected q62 endpoint from global β/γ branches and sparse generic crossing, deriving
frontier membership and canonical nonresonance from strong periodic repulsion.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
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
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_orbitNorm_autoFrontierNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **Connected q62 endpoint from global β/γ branches and local infinite strong-periodic supply.**

This is the q62 form of
`hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum`:
the `c₁` side supplies a local infinite strong-periodic target set, and Lean creates the accumulated
frontier target needed by sparse crossing. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w a : ℂ) (r : ℝ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          S.Infinite ∧
          S ⊆ Metric.closedBall a r ∧
          Metric.closedBall a r ⊆ Ω ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_closedBallStrongOrbitNorm_autoAccum
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **Connected q62 endpoint from an interior strong-periodic accumulation point.**

This is the q62 form of
`hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall`:
the callback supplies an accumulation point in the interior of the analytic crossing region, and Lean
shrinks it to the closed-ball strong-periodic supply consumed by the hRigid route. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ interior Ω ∧
          AccPt z₁ (𝓟 S) ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_accumulationInteriorStrongOrbitNorm_closedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **Connected q62 from global β/γ branches, perfect Julia frontier, and dense strong periodic
targets.**  The `c₁` callback supplies only a frontier seed in the analytic crossing region; the local
closed-ball strong-periodic supply is created internally from perfectness and density. -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ interior Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hfront hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch hinput)

/-- **hRigid from perfect frontier, dense strong roots, and an open crossing region.**

This open-region form replaces the local callback hypothesis `p ∈ interior Ω` by
`IsOpen Ω` and `p ∈ Ω`. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hfront hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, hΩopen, ha, hw, hleadw, hsepw,
          hpfront, hpΩ⟩ := hinput Q s hnt hEqOn
        exact ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hpfront,
          mem_interior_iff_mem_nhds.mpr (hΩopen.mem_nhds hpΩ)⟩)

/-- **hRigid from connected empty-interior geometry, dense strong roots, and an open crossing
region.** -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hKconn hempty hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, hΩopen, ha, hw, hleadw, hsepw,
          hpK, hpΩ⟩ := hinput Q s hnt hEqOn
        exact ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hpK,
          mem_interior_iff_mem_nhds.mpr (hΩopen.mem_nhds hpΩ)⟩)

/-- **Connected q62 from perfect frontier, dense strong roots, and an open crossing region.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hfront hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch hinput)

/-- **Connected q62 from connected empty-interior geometry, dense strong roots, and an open crossing
region.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆
      closure {z : ℂ | ∃ q : ℕ, z ∈ strongFixedPointRoots c₁ q})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hKconn hempty hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch hinput)

/-- **hRigid from perfect frontier and natural orbit-product density in an open crossing region.** -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c₁)^[k] z‖})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hfront
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)
    β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput

/-- **hRigid from connected empty-interior geometry and natural orbit-product density in an open
crossing region.** -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c₁)^[k] z‖})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hKconn hempty
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)
    β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput

/-- **Connected q62 from perfect frontier and natural orbit-product density in an open crossing
region.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hfront : Perfect (frontier (filledJulia c₁)))
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c₁)^[k] z‖})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ frontier (filledJulia c₁) ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_perfectFrontierDenseStrongRoots_openRegion_autoClosedBall_repellingG
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne_params hx₁ hx₂ hGinput hfront
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)
    β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput

/-- **Connected q62 from connected empty-interior geometry and natural orbit-product density in an
open crossing region.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongOrbitNorm_openRegion_autoClosedBall_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        (2 ^ q : ℝ) < ‖∏ k ∈ Finset.range q, 2 * (quadratic c₁)^[k] z‖})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) :=
  q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseStrongRoots_openRegion_autoClosedBall_repellingG
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne_params hx₁ hx₂ hGinput hKconn hempty
    (dense_strongFixedPointRoots_of_dense_strongly_repelling_periodic hdense)
    β γ hβan hβfront hβesc hβmod hγan hγfront hγmatch hinput

/-- **hRigid from connected empty-interior geometry and dense nonresonant periodic frontier targets.**

This is the weaker native endpoint behind the strong-orbit route: the dynamical input only has to
produce frontier-dense periodic points satisfying the canonical derivative nonresonance required by
hRigid.  It does not require the stronger `(2^q : ℝ) < ‖(f^q)'‖` inequality. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseNonresonantPeriodic_openRegion_autoAccum
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c₁) ∧ ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c₁)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_crossing_derivNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, p, hsupp, hN, hN1, hΩc, hΩopen, ha, hw, hleadw, hsepw,
          hpK, hpΩ⟩ := hinput Q s hnt hEqOn
        obtain ⟨z₁, S, hz₁Ω, hacc, hgeom⟩ :=
          exists_accumulation_nonresonantPeriodic_of_frontier_dense_open
            hKconn hempty hΩopen hpK hpΩ hdense
        exact ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁Ω,
          accPt_iff_frequently_nhdsNE.mp hacc, hgeom⟩)

/-- **Connected q62 from connected empty-interior geometry and dense nonresonant periodic frontier
targets.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseNonresonantPeriodic_openRegion_autoAccum_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hdense : frontier (filledJulia c₁) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c₁) ∧ ∃ q : ℕ,
        (quadratic c₁)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c₁)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)})
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧ IsOpen Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧
          p ∈ Ω) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_connectedEmptyInteriorDenseNonresonantPeriodic_openRegion_autoAccum
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG hKconn hempty hdense β γ hβan hβfront hβesc
      hβmod hγan hγfront hγmatch hinput)

/-- **hRigid from global branches and countable-avoidance sparse crossing.**  The callback no
longer supplies an accumulating target set.  It supplies a target mechanism which can avoid every
countable analytic bad locus; the separable strongly-repelling frontier target is chosen internally. -/
theorem hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_countableAvoidance_orbitNorm_autoFrontierNonres
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_frontier_derivNonres_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan
      hγfront hγmatch (by
        intro Q s hnt hEqOn
        obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, havoid,
          hgeom⟩ := hinput Q s hnt hEqOn
        let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
        obtain ⟨z₀, hz₀S, _hlead₀, hsep₀⟩ :=
          exists_sparse_fibre_separable_countableAvoidance (a := a) (s := s) (N := N)
            hN1 hsupp hN hΩc ha hw hleadw hsepw havoid
        obtain ⟨p, hFz, hnorm⟩ := hgeom z₀ hz₀S
        exact ⟨z₀, p, hsep₀,
          mem_frontier_of_strongly_repelling_periodic_orbitProduct hFz hnorm, hFz,
          deriv_nonresonant_of_strongly_repelling_periodic_orbitProduct hnorm⟩)

/-- **Connected q62 endpoint from global β/γ branches and countable-avoidance sparse crossing.** -/
theorem q62_independence_connected_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_countableAvoidance_orbitNorm_autoFrontierNonres_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w : ℂ) (S : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
          (∀ z₀ ∈ S, ∃ p : ℕ,
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_repelling_global_modulus_auto_betaGamma_frontierAnalytic_countableAvoidance_orbitNorm_autoFrontierNonres
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβfront hβesc hβmod hγan hγfront
      hγmatch hinput)

/-- **Level-root hRigid from sparse generic crossing.** This is the practical level-root route: the
global `c₁` branch is built from level roots, while sparse generic crossing removes the pointwise
frontier-fibre `Separable` datum from the callback.  The remaining per-target geometry is a boundary
value of the constructed basin branch, periodicity, and the orbit-product repelling inequality. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          (∀ z₀ ∈ S, ∃ (w₀ : ℂ) (p : ℕ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_minBranch_frontier_orbitNorm_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan
      hγfront hγmatch (by
        intro β hβan hβesc hβmod Q s hnt hEqOn
        obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum, hgeom⟩ := hinput β hβan hβesc hβmod Q s hnt hEqOn
        let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
        obtain ⟨z₀, hz₀S, _hlead₀, hsep₀⟩ :=
          exists_sparse_fibre_separable_crossing (a := a) (s := s) (N := N)
            hN1 hsupp hN hΩc ha hw hleadw hsepw hz₁ haccum
        obtain ⟨w₀, p, hfront, hβlim, hFz, hnorm⟩ := hgeom z₀ hz₀S
        exact ⟨z₀, w₀, p, hsep₀, hfront, hβlim, hFz, hnorm⟩)

/-- **Level-root hRigid from sparse generic crossing, deriving frontier membership from repulsion.**
Compared with `hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm`,
the callback no longer supplies `z₀ ∈ frontier K_{c₁}`.  A periodic point with the strong
orbit-product bound lies on the frontier by `mem_frontier_of_strongly_repelling_periodic_orbitProduct`. -/
theorem hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          AccPt z₁ (𝓟 S) ∧
          (∀ z₀ ∈ S, ∃ (w₀ : ℂ) (p : ℕ),
            Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact
    hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan
      hγfront hγmatch (by
        intro β hβan hβesc hβmod Q s hnt hEqOn
        obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum, hgeom⟩ := hinput β hβan hβesc hβmod Q s hnt hEqOn
        have haccum' : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S :=
          accPt_iff_frequently_nhdsNE.mp haccum
        refine ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, ha, hw, hleadw, hsepw, hz₁,
          haccum', ?_⟩
        intro z₀ hz₀S
        obtain ⟨w₀, p, hβlim, hFz, hnorm⟩ := hgeom z₀ hz₀S
        exact ⟨w₀, p,
          mem_frontier_of_strongly_repelling_periodic_orbitProduct hFz hnorm,
          hβlim, hFz, hnorm⟩)

/-- **Connected q62 endpoint from level roots and sparse generic crossing, with `φ_{c₂}`
transcendence produced internally.** Compared with the prior level-root endpoint, the callback now
supplies an accumulating target set and one good specialization; the separable frontier target is
created internally. -/
theorem q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hGinput : ∀ P : Polynomial (Polynomial ℂ), P ≠ 0 → 1 ≤ P.natDegree →
        (∀ z ∈ U, ∑ i ∈ P.support, (P.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
        (∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support, (R.coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0) →
          P.natDegree ≤ R.natDegree) →
        {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c₂ z) ^ i = 0}.Countable →
        ∃ (p : ℕ) (lam w₀ d : ℂ) (z₀ : ℂ),
          (∑ i ∈ P.support, (P.coeff i).aeval z₀ * w₀ ^ i = 0) ∧
          HasDerivAt (fun w => ∑ i ∈ P.support, (P.coeff i).aeval z₀ * w ^ i) d w₀ ∧ d ≠ 0 ∧
          (quadratic c₂)^[p] z₀ = z₀ ∧ HasDerivAt ((quadratic c₂)^[p]) lam z₀ ∧
          w₀ ^ (2 ^ p) = w₀ ∧ w₀ ≠ 0 ∧ (2 ^ p : ℝ) < ‖lam‖)
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          (∀ z₀ ∈ S, ∃ (w₀ : ℂ) (p : ℕ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_input hUo hUc hUne hUinf c₂ hU₂ hGinput
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan
      hγfront hγmatch hinput)

/-- **Connected q62 endpoint from level roots and sparse generic crossing, deriving frontier
membership from periodic repulsion.** This is the current practical hRigid crossing endpoint: the
`c₁` callback does not prove `z₀ ∈ frontier K_{c₁}`, and the absolute `c₂` input no longer supplies a
squaring-fixed simple fibre root, a chosen fibre root, fibre-level degree/constant data, a single
point avoiding every possible denominator, pointwise fibre separability at the selected target, or the
full-degree squarefree witness specialization. -/
theorem q62_independence_connected_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier_repellingG
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne_params : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
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
    (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c₁ n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c₁ ((quadratic c₁)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (γ : ℂ → ℂ)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (β : ℂ → ℂ), AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) →
        (∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z)) →
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
          AccPt z₁ (𝓟 S) ∧
          (∀ z₀ ∈ S, ∃ (w₀ : ℂ) (p : ℕ),
            Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀) ∧
            (quadratic c₁)^[p] z₀ = z₀ ∧
            (2 ^ p : ℝ) < ‖∏ k ∈ Finset.range p, 2 * (quadratic c₁)^[k] z₀‖)) :
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
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne_params hx₁ hx₂ hG
    (hrig_phiMero_of_level_roots_modulus_auto_gamma_frontierAnalytic_crossing_orbitNorm_autoFrontier
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev hanalytic hpow hne hanchorEsc γ hγan
      hγfront hγmatch hinput)

end Bottcher
