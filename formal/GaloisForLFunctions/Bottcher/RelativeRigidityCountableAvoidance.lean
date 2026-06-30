import GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary
import GaloisForLFunctions.Bottcher.RelativeTranscendenceBridge
import GaloisForLFunctions.Bottcher.Q62ConnectedAssembly
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect
import GaloisForLFunctions.Bottcher.JuliaBasinCrossing

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from countable-avoidance sparse crossing and common-basin geometry.**

This is the countable-avoidance version of
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing`: the caller no longer
supplies an accumulating target set.  Instead, for each relation it supplies a target mechanism `S`
that can avoid every countable exceptional set inside the analytic region `Ω`.  The sparse fibre
constructor then avoids the analytic top-coefficient/resultant bad locus internally. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        havoid, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hgeom)

/-- **NoRelation from countable-avoidance sparse crossing and local-tip common-basin geometry.**
This is the local-radius replacement for the all-scale `htip` endpoint above: the selected target
only has to supply punctured-basin preconnectedness below a positive radius. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
          (∀ z₀ ∈ S, ∃ (r rTip : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        havoid, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_localTip
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hgeom)

/-- **hRigid from countable avoidance plus local-tip common-basin geometry.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip`
as the `TranscendentalOverAdjoin` input consumed by the connected q62 carrier bridge. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, ∃ (r rTip : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus local-tip common-basin geometry.** This is the
q62-facing form of
`hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip`. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, ∃ (r rTip : ℝ) (V : Set ℂ),
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **hRigid from countable-avoidance sparse crossing and common-basin geometry.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance` as the
`TranscendentalOverAdjoin` input consumed by the connected q62 carrier bridge. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable-avoidance sparse crossing and common-basin geometry.** This is the
direct q62-facing form of
`hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance`: the countable
analytic bad locus is still avoided internally by the sparse-fibre theorem, and the resulting
`TranscendentalOverAdjoin` input is fed straight into the connected carrier bridge. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from natural-boundary countable avoidance plus carrier-closure geometry.** This reduced
endpoint keeps the natural-boundary predicate `hnb` but no longer asks the per-target geometry to supply a
common-basin region `V`: `S ⊆ closure U` and punctured-sector preconnectedness build that internally. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_carrierClosure
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hSclosure hgeom)

/-- **hRigid from natural-boundary countable avoidance plus carrier-closure geometry.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure` as
the `TranscendentalOverAdjoin` input consumed by connected q62. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary countable avoidance plus carrier-closure geometry.** This is the
q62-facing natural-boundary endpoint after the common-basin component has been internalized. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from natural-boundary countable avoidance plus local-radius carrier-closure geometry.**
This reduced local-tip endpoint builds the common-basin component internally from `S ⊆ closure U`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_carrierClosure_localTip
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hSclosure hgeom)

/-- **hRigid from natural-boundary countable avoidance plus local-radius carrier-closure geometry.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary countable avoidance plus local-radius carrier-closure geometry.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from natural-boundary countable avoidance plus rotated local slit-sector targets.**
The caller supplies frontier/off-other targets in `closure U`; each target carries a direction and a
positive radius on which the rotated slit sector is inside the basin. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzfront, hzoff, u, rTip, hu, hrTip, hslit⟩ := hgeom z₀ hz₀S
      exact ⟨hzfront, hzoff, rTip, hrTip,
        local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
          (K := filledJulia c₁) (u := u) (z₀ := z₀) (R := rTip) hu hslit⟩)

/-- **hRigid from natural-boundary countable avoidance plus rotated local slit-sector targets.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary countable avoidance plus rotated local slit-sector targets.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from natural-boundary uncountably many all-scale rotated-slit-good frontier
targets.** This is the all-scale counterpart of the local-radius rotated endpoint: the all-scale
rotated sector input is converted to the local-radius interface with radius `1`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω) (G := {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ})
          (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal) hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hrot⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, hu, hslit⟩ := hrot
      exact ⟨hzfront, hzoff₂, u, (1 : ℝ), hu, by norm_num, fun ρ hρ _hρle => hslit ρ hρ⟩)

/-- **hRigid from natural-boundary uncountably many all-scale rotated-slit-good frontier targets.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary uncountably many all-scale rotated-slit-good frontier
targets.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from natural-boundary uncountably many local-radius rotated-slit-good frontier
targets.** This is the local-frontier supply form of
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω)
          (G := {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            (∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)})
          (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal) hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hrot⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, rTip, hu, hrTip, hslit⟩ := hrot
      exact ⟨hzfront, hzoff₂, u, rTip, hu, hrTip, hslit⟩)

/-- **hRigid from natural-boundary uncountably many local-radius rotated-slit-good frontier targets.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary uncountably many local-radius rotated-slit-good frontier
targets.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **Natural-boundary NoRelation from countable-avoidance slit-sector targets.** This is the
translated-slit analogue of the rotated local-tip endpoint: the caller supplies frontier/off-other
targets whose translated slit sectors lie in the basin, and the local `htip` preconnectedness is
derived internally. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzfront, hzoff, hslit⟩ := hgeom z₀ hz₀S
      exact ⟨hzfront, hzoff,
        local_tip_preconnected_of_translated_slitPlane_subset_compl
          (K := filledJulia c₁) (z₀ := z₀) hslit⟩)

/-- **Natural-boundary hRigid from countable-avoidance slit-sector targets.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary countable-avoidance slit-sector targets.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ frontier (filledJulia c₁) ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **Natural-boundary NoRelation from uncountably many translated-slit-good local frontier targets.**
Lean selects a point outside the relation's countable bad set and derives the local `htip` condition
from the translated slit sector. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_slit_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal)
          hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hslit⟩ := hSlocal z₀ hz₀S
      exact ⟨hzfront, hzoff₂,
        local_tip_preconnected_of_translated_slitPlane_subset_compl
          (K := filledJulia c₁) (z₀ := z₀) hslit⟩)

/-- **Natural-boundary hRigid from uncountably many translated-slit-good local frontier targets.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary uncountably many translated-slit-good local frontier targets.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from countable avoidance plus empty-interior carrier-closure geometry.** This is the
reduced-geometry countable-avoidance endpoint: the per-relation target mechanism supplies only countable
avoidance, target closure against the carrier `U`, filled/off-other membership, and punctured
`K_{c₁}ᶜ` preconnectedness.  The common-basin component and local sector inclusion are built internally. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_carrierClosure
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hempty hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hSclosure hgeom)

/-- **hRigid from countable avoidance plus empty-interior carrier-closure geometry.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure` as the
`TranscendentalOverAdjoin` input for the connected q62 carrier bridge. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus empty-interior carrier-closure geometry.** This is the
q62-facing reduced-geometry countable-avoidance endpoint. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      hinput)

/-- **NoRelation from countable avoidance plus local-radius carrier-closure geometry.**  This is the
local-tip version of the carrier-closure endpoint: the selected target set only has to give
punctured-basin preconnectedness below one positive radius. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_carrierClosure_localTip
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hempty hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hSclosure hgeom)

/-- **hRigid from countable avoidance plus local-radius carrier-closure geometry.** Packages the
local-tip carrier-closure endpoint as `TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus local-radius carrier-closure geometry.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from countable-avoidance rotated local slit-sector targets.**  The caller supplies a
countably unavoidable target set in `closure U`; each target carries a direction and a positive radius
on which the rotated slit sector is inside the basin. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzK, hzoff, u, rTip, hu, hrTip, hslit⟩ := hgeom z₀ hz₀S
      exact ⟨hzK, hzoff, rTip, hrTip,
        local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
          (K := filledJulia c₁) (u := u) (z₀ := z₀) (R := rTip) hu hslit⟩)

/-- **hRigid from countable-avoidance rotated local slit-sector targets.** -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable-avoidance rotated local slit-sector targets.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from countable-avoidance slit-sector targets.** This is the reduced target-set form
for the dendrite hRigid lane: the caller supplies a countably unavoidable set `S` in the analytic
region, contact with the carrier closure, filled/off-other membership, and a translated-slit sector
inside the local basin at each target. The punctured-basin preconnectedness required downstream is
derived internally from the slit-sector density bridge. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hSclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzK, hzoff, hslit⟩ := hgeom z₀ hz₀S
      exact ⟨hzK, hzoff,
        local_tip_preconnected_of_translated_slitPlane_subset_compl
          (K := filledJulia c₁) (z₀ := z₀) hslit⟩)

/-- **hRigid from countable-avoidance slit-sector targets.** Packages the slit-sector target-set
endpoint as `TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable-avoidance slit-sector targets.** This q62-facing endpoint consumes
a countably unavoidable target set whose points have translated slit sectors in the local basin; the
natural-boundary `htip` input is derived internally. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureSlitSector
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from a local perfect-frontier countable-avoidance target.** This is the most concrete
empty-interior countable-avoidance endpoint: for each relation the caller supplies a local seed point in
the analytic region, a local basin sector landing in the carrier `U`, an off-other basin ball, and
punctured-sector preconnectedness on that local frontier slice.  The uncountable/countable-avoidance
target set and the carrier-closure condition are built internally from perfection of `K_{c₁}`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, htip⟩ :=
        hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
          hrLocal hrOther hsector hother
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
      exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂, htip z₀ ⟨⟨hzball, hzfront⟩, hzoff₂⟩⟩)

/-- **hRigid from a local perfect-frontier countable-avoidance target.** Packages the concrete local
target-set endpoint as `TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from a local perfect-frontier countable-avoidance target.** This is the current
q62-facing endpoint with the countable-deletion target set constructed internally from local perfect
empty-interior frontier data. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from uncountably many slit-good local frontier targets.**  This is the countable-avoidance
form of the remaining slit geometry: for each relation it is enough to provide an uncountable local
frontier/off-other set in the analytic region on which the translated slit sector lies in the basin at
every scale.  Lean then selects a target avoiding the relation's countable bad set and derives `htip`
internally. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_slit_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal)
          hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hslit⟩ := hSlocal z₀ hz₀S
      exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
        local_tip_preconnected_of_translated_slitPlane_subset_compl
          (K := filledJulia c₁) (z₀ := z₀) hslit⟩)

/-- **hRigid from uncountably many slit-good local frontier targets.** Packages the slit-uncountable
countable-avoidance endpoint as `TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from uncountably many slit-good local frontier targets.** This q62-facing endpoint
reduces the slit local-topology branch to the uncountability of the local slit-good target supply. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from uncountably many rotated-slit-good local frontier targets.**  Unlike the fixed
translated-slit version, this lets the local excluded ray vary by target point.  This is still an
all-scale interface; the local-radius continuation theorem is the sharper route when the supply theorem
only controls sufficiently small sectors. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosure
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω) (G := {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ})
          (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal) hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hrot⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, hu, hslit⟩ := hrot
      exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
        local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl
          (K := filledJulia c₁) (u := u) (z₀ := z₀) hu hslit⟩)

/-- **hRigid from uncountably many rotated-slit-good local frontier targets.** Packages the
direction-varying all-scale rotated-slit target supply as `TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from uncountably many rotated-slit-good local frontier targets.** This is the
q62-facing endpoint for the direction-varying all-scale rotated local-tip supply. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from uncountably many local-radius rotated-slit-good frontier targets.**  This is the
local-radius replacement for the all-scale rotated endpoint: each target may choose a direction and only
has to control the rotated slit sector below one positive radius. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hsector, hunc⟩ := hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_good_target_set_countableAvoidance_closure_frontier
          (U := U) (Ω := Ω)
          (G := {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            (∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)})
          (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal) hunc hsector
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨_hzball, hzfront, hzoff₂, hrot⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, rTip, hu, hrTip, hslit⟩ := hrot
      exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂, u, rTip, hu, hrTip, hslit⟩)

/-- **hRigid from uncountably many local-radius rotated-slit-good frontier targets.** -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from uncountably many local-radius rotated-slit-good frontier targets.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          ¬ (((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩
            {z₀ : ℂ | ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              (∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)}) ∩ Ω).Countable)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitUncountableLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from a local translated-slit basin sector.**  This is the concrete local-frontier
endpoint with the `htip` preconnectedness discharged internally: the caller supplies only that the
translated slit sector lies in the basin on the target slice, and
`local_tip_preconnected_of_translated_slitPlane_subset_compl` turns the dense preconnected slit sector
into the full punctured-basin preconnectedness required by the natural-boundary engine. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTarget
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, hlocal⟩ :=
        hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, ?_⟩
      intro z₀ hz₀ ρ hρ
      exact local_tip_preconnected_of_translated_slitPlane_subset_compl
        (K := filledJulia c₁) (z₀ := z₀) (hlocal z₀ hz₀) ρ hρ)

/-- **hRigid from a local translated-slit basin sector.** Packages the slit-sector target endpoint as
`TranscendentalOverAdjoin`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from a local translated-slit basin sector.** This q62-facing endpoint consumes a
local slit sector for the selected frontier targets and derives the natural-boundary `htip` input
internally. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ →
              Metric.ball z₀ ρ ∩ {z | z - z₀ ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierSlitModel
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from countable avoidance plus empty-interior common-component geometry.**
This is the component-closure version of the carrier-closure endpoint above: the far-field carrier
`U` stays inside `escapeOpen c₁ ∩ escapeOpen c₂`, while the target set only has to accumulate on the
closure of the common-basin component containing `U`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
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
          (∃ u ∈ U, ∀ z₀ ∈ S,
            z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        havoid, hcomponent, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hempty hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid hcomponent hgeom)

/-- **hRigid from countable avoidance plus empty-interior common-component geometry.** -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∃ u ∈ U, ∀ z₀ ∈ S,
            z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus empty-interior common-component geometry.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
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
          (∃ u ∈ U, ∀ z₀ ∈ S,
            z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p u : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          u ∈ U ∧ p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_commonComponent
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, u, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, huU, hpK, hpΩ, hpcl, hrLocal, hrOther, hother, htip⟩ :=
        hinput Q s hnt hEqOn
      let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
      let V : Set ℂ := connectedComponentIn C u
      have hCo : IsOpen C :=
        (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
      have hVsubC : V ⊆ C := by
        simpa [V] using connectedComponentIn_subset C u
      have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
      have hpfront : p ∈ frontier (filledJulia c₁) := mem_frontier_of_mem_filledJulia_emptyInterior hempty hpK
      have hpoff₂ : p ∈ (filledJulia c₂)ᶜ := hother (Metric.mem_ball_self hrOther)
      set r : ℝ := min rLocal rOther with hrdef
      have hr : 0 < r := by rw [hrdef]; exact lt_min hrLocal hrOther
      have hr_le_local : r ≤ rLocal := by rw [hrdef]; exact min_le_left _ _
      have hr_le_other : r ≤ rOther := by rw [hrdef]; exact min_le_right _ _
      have hpLocal : p ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ :=
        ⟨⟨Metric.mem_ball_self hrLocal, hpfront⟩, hpoff₂⟩
      have hpTip : IsPreconnected (Metric.ball p r ∩ (filledJulia c₁)ᶜ) := htip p hpLocal r hr
      have hsectorV : Metric.ball p r ∩ (filledJulia c₁)ᶜ ⊆ V := by
        set W : Set ℂ := Metric.ball p r ∩ (filledJulia c₁)ᶜ with hW
        have hWc : IsPreconnected W := by simpa [W] using hpTip
        have hWC : W ⊆ C := by
          intro z hz
          exact ⟨hz.2, hother (Metric.ball_subset_ball hr_le_other hz.1)⟩
        have hpclV : p ∈ closure V := by simpa [V, C] using hpcl
        have hmeet : (Metric.ball p r ∩ V).Nonempty := by
          rw [_root_.mem_closure_iff] at hpclV
          exact hpclV (Metric.ball p r) isOpen_ball (Metric.mem_ball_self hr)
        obtain ⟨y, hyball, hyV⟩ := hmeet
        have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
        have hWsubCompY : W ⊆ connectedComponentIn C y :=
          hWc.subset_connectedComponentIn hyW hWC
        have hcomp : connectedComponentIn C y = V := by
          have h := connectedComponentIn_eq (by simpa [V] using hyV)
          simpa [V] using h.symm
        intro z hz
        exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
          (U := V) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
          hr hrOther hsectorV hother
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        ?_, ?_⟩
      · refine ⟨u, huU, ?_⟩
        intro z₀ hz₀S
        simpa [V, C] using hclosure z₀ hz₀S
      · intro z₀ hz₀S
        obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
        have hzballLocal : z₀ ∈ Metric.ball p rLocal := Metric.ball_subset_ball hr_le_local hzball
        exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
          htip z₀ ⟨⟨hzballLocal, hzfront⟩, hzoff₂⟩⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62 from a local common-component frontier target.**  This is the q62-facing form of
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w p u : ℂ) (rLocal rOther : ℝ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          u ∈ U ∧ p ∈ filledJulia c₁ ∧ p ∈ interior Ω ∧
          p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
          0 < rLocal ∧ 0 < rOther ∧
          Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hinput))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a single off-other filled-Julia witness.**  This removes the per-relation duty to
find the common-component frontier point.  A fixed point of `filledJulia c₁ \ filledJulia c₂` and any
carrier point `u ∈ U` force a frontier point `p ∈ frontier K₁ ∩ K₂ᶜ` in the closure of the common-basin
component containing `u`; each relation provider only has to supply the algebraic seed and the local
analytic/preconnected data around that `p`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hinput : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (N : ℕ) (Ω : Set ℂ) (w : ℂ) (rLocal rOther : ℝ),
            s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
            IsPreconnected Ω ∧
            (∀ i ∈ s, AnalyticOnNhd ℂ
              (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
            w ∈ Ω ∧
            (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
            p ∈ interior Ω ∧
            0 < rLocal ∧ 0 < rOther ∧
            Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨u, huU⟩ := hUne
  have huCommon : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
      escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
  obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component
      (a := c₁) (b := c₂) (u := u) (x := x) huCommon hxK hxoff₂
  have hpK : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfront
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent
    hUo hUc ⟨u, huU⟩ hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpΩ, hrLocal, hrOther, hother, htip⟩ :=
        hinput p u huU hpfront hpoff₂ hpcl Q s hnt hEqOn
      exact ⟨N, Ω, w, p, u, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, huU, hpK, hpΩ, hpcl, hrLocal, hrOther, hother, htip⟩)

/-- **Connected q62 from a single off-other filled-Julia witness.**  This is the q62-facing version of
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hinput : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (N : ℕ) (Ω : Set ℂ) (w : ℂ) (rLocal rOther : ℝ),
            s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
            IsPreconnected Ω ∧
            (∀ i ∈ s, AnalyticOnNhd ℂ
              (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
            w ∈ Ω ∧
            (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
            p ∈ interior Ω ∧
            0 < rLocal ∧ 0 < rOther ∧
            Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hxK hxoff₂ hinput))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from an off-other witness with the analytic region fixed to `K₂ᶜ`.**  This is the
leaner form of `...offOtherPoint`: the common-component frontier point is constructed internally, and
`Ω` is fixed as the full basin complement `(filledJulia c₂)ᶜ`.  Thus the remaining per-relation input is
only the algebraic full-degree/separable seed plus the local punctured-basin connectivity near the fixed
frontier point. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hinput : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (N : ℕ) (w : ℂ) (rLocal : ℝ),
            s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
            w ∈ (filledJulia c₂)ᶜ ∧
            (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
            0 < rLocal ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch hxK hxoff₂ (by
      intro p u huU hpfront hpoff₂ hpcl Q s hnt hEqOn
      obtain ⟨N, w, rLocal, hsupp, hN, hN1, hw, hleadw, hsepw, hrLocal, htip⟩ :=
        hinput p u huU hpfront hpoff₂ hpcl Q s hnt hEqOn
      obtain ⟨rOther, hrOther, hother⟩ :=
        Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff₂
      refine ⟨N, (filledJulia c₂)ᶜ, w, rLocal, rOther, hsupp, hN, hN1,
        isPreconnected_compl_filledJulia c₂, ?_, hw, hleadw, hsepw, ?_, hrLocal, hrOther,
        hother, htip⟩
      · intro i _hi
        exact analyticOnNhd_eval₂_of_analyticOnNhd hγan₂ (Q i)
      · exact mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff₂))

/-- **Connected q62 with the analytic region fixed to `K₂ᶜ`.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hinput : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (N : ℕ) (w : ℂ) (rLocal : ℝ),
            s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
            w ∈ (filledJulia c₂)ᶜ ∧
            (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
            0 < rLocal ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_offOtherPoint_basinOmega
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hxK hxoff₂ hinput))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Single-relation empty-interior contradiction from a separable common-region frontier fibre.**
This is the local form of
`noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable`: it consumes one
already-normalized relation.  The normalization may come from a minimal/squarefree divisor of an original
raw relation, so the final algebraic seed extraction is no longer forced to keep the raw `Q,s`. -/
theorem false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation
    (hUo : IsOpen U) (_hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁)
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {N : ℕ} {z₀ : ℂ} {r : ℝ} {V : Set ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (hlead : (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0)
    (hsep : (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable)
    (hz₀K : z₀ ∈ filledJulia c₁) (hz₀off : z₀ ∈ (filledJulia c₂)ᶜ)
    (hr : 0 < r) (_hVo : IsOpen V) (hVc : IsPreconnected V) (hUV : U ⊆ V)
    (hVbasin : V ⊆ (filledJulia c₁)ᶜ)
    (hsectorV : Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V)
    (hγV : AnalyticOnNhd ℂ γ V)
    (htip : ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    False := by
  let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
  have haV : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V := by
    intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγV (Q i)
  have hγAt : AnalyticAt ℂ γ z₀ := hγan₂ z₀ hz₀off
  have haAt : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀ := by
    intro i _hi
    exact (analyticAt_eval₂_of_analyticAt hγAt (Q i)).contDiffAt
  have hmatch : ∀ i ∈ s, ∀ z ∈ U,
      a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
    intro i _hi z hz
    dsimp [a]
    simpa using congrArg (fun w => (Q i).eval₂ (Polynomial.evalRingHom z) w) (hγmatch z hz)
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc
      ∑ i ∈ s, a i z * (β z) ^ i
          = ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβV : AnalyticOnNhd ℂ β V := hβan.mono hVbasin
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (β z) ^ i) V :=
    analyticOnNhd_relation_analytic haV hβV
  obtain ⟨u, huU⟩ := hUne
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [hUo.mem_nhds huU] with z hz
    exact hrelU z hz
  have hrelV : Set.EqOn (fun z => ∑ i ∈ s, a i z * (β z) ^ i) 0 V :=
    hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc (hUV huU) hev
  have hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ) :=
    hβan.continuousOn.mono inter_subset_right
  have hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0 := fun z hz => hrelV (hsectorV hz)
  have hβmod_local : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ,
      ‖β z‖ = Real.exp (greenFunctionDyn c₁ z) := fun z hz => hβmod z hz.2
  have hempty_local : Metric.ball z₀ r ∩ interior (filledJulia c₁) = ∅ := by
    rw [hempty, inter_empty]
  exact false_of_global_basin_branch_analytic hsupp hN hN1 haAt (by simpa [a] using hlead)
    (by simpa [a] using hsep) hr hz₀K hempty_local htip hβc hβrel hβmod_local

/-- **NoRelation from normalized separable common-region relations.**  This endpoint implements the
minimal-polynomial/squarefree-divisor road: a raw relation only has to produce some normalized relation
`Q',s'` that still vanishes on `U` and has the separable frontier fibre.  The normalized relation may be a
minimal divisor over the relative coefficient field; it need not be the original raw sparse relation. -/
theorem noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_normalized_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnormalize : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ) (z₀ : ℂ) (r : ℝ)
          (V : Set ℂ),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
          (Q' N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧ z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, z₀, r, V, _hnt', hEqOn', hsupp, hN, hN1, hlead, hsep, hz₀K,
    hz₀off, hr, hVo, hVc, hUV, hVbasin, hsectorV, hγV, htip⟩ := hnormalize Q s hnt hEqOn
  exact false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation
    hUo hUc hUne c₁ c₂ hU₁ β γ hβan hβesc hβmod hempty hγan₂ hγmatch Q' s' hEqOn'
    hsupp hN hN1 hlead hsep hz₀K hz₀off hr hVo hVc hUV hVbasin hsectorV hγV htip

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **hRigid from normalized separable common-region relations.** -/
theorem hrig_phiMero_of_emptyInterior_commonRegion_gamma_offOther_normalized_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnormalize : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ) (z₀ : ℂ) (r : ℝ)
          (V : Set ℂ),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
          (Q' N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧ z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_normalized_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      hnormalize)

/-- **Connected q62 from normalized separable common-region relations.**  This is the q62-facing package
for the minimal-polynomial/squarefree-divisor route. -/
theorem q62_independence_connected_of_emptyInterior_commonRegion_gamma_offOther_normalized_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnormalize : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ) (z₀ : ℂ) (r : ℝ)
          (V : Set ℂ),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
          (Q' N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧ z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonRegion_gamma_offOther_normalized_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
      hnormalize)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- If a bivariate polynomial evaluated at the Böttcher coordinate vanishes pointwise on the carrier,
then its analytic-subring evaluation is zero. -/
theorem eval₂_polyToAnalytic_eq_zero_of_eqOn {c : ℂ} {hU : U ⊆ escapeOpen c}
    (q : Polynomial (Polynomial ℂ))
    (hEq : Set.EqOn (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) 0 U) :
    q.eval₂ (polyToAnalytic U) (phiAnalytic c hU) = 0 := by
  apply Subtype.ext
  rw [eval₂_polyToAnalytic_val c hU q, ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
  exact Filter.eventually_principal.mpr hEq

/-- A nontrivial sparse relation supported only at degree zero cannot vanish on the carrier.  This is
the first algebraic normalization gate for the relative minimal-relation route: once a relation is known
nontrivial in the analytic coefficient ring, its normalized top degree is forced to be positive. -/
theorem false_of_singleton_zero_sparse_relation
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ))
    (hQ0 : (Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ ({0} : Finset ℕ),
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    False := by
  have hcoef : Set.EqOn
      (fun z => (Q 0).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) 0 U := by
    intro z hz
    have h := hEqOn hz
    simpa using h
  exact hQ0 (eval₂_polyToAnalytic_eq_zero_of_eqOn (c := c₂) (hU := hU₂) (Q 0) hcoef)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- If a nontrivial sparse relation has support contained in `range 1`, it is the impossible degree-zero
case.  This packages `false_of_singleton_zero_sparse_relation` in the support language used by the sparse
fibre endpoints. -/
theorem false_of_sparse_relation_support_range_one
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hnt : ∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hsupp : s ⊆ Finset.range 1)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    False := by
  obtain ⟨i, hi, hQi⟩ := hnt
  have hi0 : i = 0 := by
    have hi_lt : i < 1 := Finset.mem_range.mp (hsupp hi)
    omega
  have h0s : 0 ∈ s := by
    simpa [hi0] using hi
  have hs : s = ({0} : Finset ℕ) := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      have hj_lt : j < 1 := Finset.mem_range.mp (hsupp hj)
      have hj0 : j = 0 := by omega
      simp [hj0]
    · intro hj
      have hj0 : j = 0 := by simpa using hj
      simpa [hj0] using h0s
  have hQ0 : (Q 0).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0 := by
    simpa [hi0] using hQi
  exact false_of_singleton_zero_sparse_relation c₁ c₂ hU₂ Q hQ0 (by
    intro z hz
    simpa [hs] using hEqOn hz)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Single normalized relation plus one basin seed gives contradiction.**  This is the normalized
local-frontier version of the countable-avoidance route: from one full-degree separable specialization in
`K₂ᶜ`, the existing common-component target machinery selects a frontier point in the component closure
where the fibre is still separable, and the branch obstruction closes the contradiction. -/
theorem false_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent_relation
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {N : ℕ} {w p u : ℂ} {rLocal : ℝ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (hw : w ∈ (filledJulia c₂)ᶜ)
    (hleadw : (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0)
    (hsepw : (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable)
    (huU : u ∈ U)
    (hpfront : p ∈ frontier (filledJulia c₁)) (hpoff₂ : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hrLocal : 0 < rLocal)
    (htip : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    False := by
  let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
  have hpK : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfront
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff₂
  have hpΩ : p ∈ interior ((filledJulia c₂)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff₂)
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let Vc : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVsubC : Vc ⊆ C := by
    simpa [Vc] using connectedComponentIn_subset C u
  have hVbasin₁ : Vc ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  set r : ℝ := min rLocal rOther with hrdef
  have hr : 0 < r := by rw [hrdef]; exact lt_min hrLocal hrOther
  have hr_le_local : r ≤ rLocal := by rw [hrdef]; exact min_le_left _ _
  have hr_le_other : r ≤ rOther := by rw [hrdef]; exact min_le_right _ _
  have hpLocal : p ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ :=
    ⟨⟨Metric.mem_ball_self hrLocal, hpfront⟩, hpoff₂⟩
  have hpTip : IsPreconnected (Metric.ball p r ∩ (filledJulia c₁)ᶜ) := htip p hpLocal r hr
  have hsectorVc : Metric.ball p r ∩ (filledJulia c₁)ᶜ ⊆ Vc := by
    set W : Set ℂ := Metric.ball p r ∩ (filledJulia c₁)ᶜ with hW
    have hWc : IsPreconnected W := by simpa [W] using hpTip
    have hWC : W ⊆ C := by
      intro z hz
      exact ⟨hz.2, hother (Metric.ball_subset_ball hr_le_other hz.1)⟩
    have hpclVc : p ∈ closure Vc := by simpa [Vc, C] using hpcl
    have hmeet : (Metric.ball p r ∩ Vc).Nonempty := by
      rw [_root_.mem_closure_iff] at hpclVc
      exact hpclVc (Metric.ball p r) isOpen_ball (Metric.mem_ball_self hr)
    obtain ⟨y, hyball, hyV⟩ := hmeet
    have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
    have hWsubCompY : W ⊆ connectedComponentIn C y :=
      hWc.subset_connectedComponentIn hyW hWC
    have hcomp : connectedComponentIn C y = Vc := by
      have h := connectedComponentIn_eq (by simpa [Vc] using hyV)
      simpa [Vc] using h.symm
    intro z hz
    exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
  obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
    exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
      (U := Vc) (Ω := (filledJulia c₂)ᶜ) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
      hr hrOther hsectorVc hother
  have hΩc : IsPreconnected ((filledJulia c₂)ᶜ) := isPreconnected_compl_filledJulia c₂
  have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ := by
    intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγan₂ (Q i)
  obtain ⟨N', z₀, r', V, hsupp', hN', hN1', hlead, hsep, hzfront, hzoff₂, hr', hVo,
      hVc, hUV, hVbasin₁', hVbasin₂', hsectorV, htipz⟩ :=
    exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent
      (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) (S := S)
      hempty hUo hUc hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
      (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
      hN1 hsupp hN hΩc ha hw (by simpa [a] using hleadw) (by simpa [a] using hsepw) havoid
      (hcomponent := by
        refine ⟨u, huU, ?_⟩
        intro z₁ hz₁S
        simpa [Vc, C] using hclosure z₁ hz₁S)
      (hgeom := by
        intro z₁ hz₁S
        obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₁ hz₁S
        have hzballLocal : z₁ ∈ Metric.ball p rLocal := Metric.ball_subset_ball hr_le_local hzball
        exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
          htip z₁ ⟨⟨hzballLocal, hzfront⟩, hzoff₂⟩⟩)
  exact false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation
    hUo hUc hUne c₁ c₂ hU₁ β γ hβan hβesc hβmod hempty hγan₂ hγmatch Q s hEqOn
    hsupp' hN' hN1' (by simpa [a] using hlead) (by simpa [a] using hsep)
    (mem_filledJulia_of_frontier hzfront) hzoff₂ hr' hVo hVc hUV hVbasin₁' hsectorV
    (hγan₂.mono hVbasin₂') htipz

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from normalized relations plus one off-other point.**  This is the countable-avoidance
endpoint for the corrected Grok/minimal-polynomial route: each raw relation may first be replaced by a
normalized relation `Q',s'`; the theorem then constructs the common-component frontier target internally
from a single point of `K₁ \ K₂` and uses one separable seed in `K₂ᶜ`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hnormalize : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ) (w : ℂ)
            (rLocal : ℝ),
            (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
            Set.EqOn (fun z => ∑ i ∈ s',
                ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                  * (bottcherCoord c₁ z) ^ i) 0 U ∧
            s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
            w ∈ (filledJulia c₂)ᶜ ∧
            (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable ∧
            0 < rLocal ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨u, huU⟩ := hUne
  have huCommon : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
      escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
  obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component
      (a := c₁) (b := c₂) (u := u) (x := x) huCommon hxK hxoff₂
  obtain ⟨Q', s', N, w, rLocal, _hnt', hEqOn', hsupp, hN, hN1, hw, hleadw, hsepw,
    hrLocal, htip⟩ := hnormalize p u huU hpfront hpoff₂ hpcl Q s hnt hEqOn
  exact false_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierTargetCommonComponent_relation
    hUo hUc ⟨u, huU⟩ c₁ c₂ hU₁ hU₂ β γ hβan hβesc hβmod hKconn hempty hγan₂ hγmatch
    Q' s' hEqOn' hsupp hN hN1 hw hleadw hsepw huU hpfront hpoff₂ hpcl hrLocal htip

/-- **Connected q62 from normalized relations plus one off-other point.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hnormalize : ∀ (p u : ℂ),
        u ∈ U →
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
          (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
          Set.EqOn (fun z => ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U →
          ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ) (w : ℂ)
            (rLocal : ℝ),
            (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
            Set.EqOn (fun z => ∑ i ∈ s',
                ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                  * (bottcherCoord c₁ z) ^ i) 0 U ∧
            s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
            w ∈ (filledJulia c₂)ᶜ ∧
            (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
            (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable ∧
            0 < rLocal ∧
            (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
              ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_offOtherPoint_basinOmega
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hxK hxoff₂ hnormalize))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from the primitive/squarefree bad-locus package.**  This is the Grok route packaged
without asking the algebraic producer to choose the specialization point.  The producer supplies a
normalized relation and a nonzero bivariate bad-locus polynomial `B` (morally: leading coefficient times
squarefree discriminant).  `hG` then chooses `w ∈ U ⊆ K₂ᶜ` with `B(w, γ w) ≠ 0`, and the existing
common-component/countable-avoidance endpoint finishes. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_primitiveSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hprimitiveSqfreeBad : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
          (B : Polynomial (Polynomial ℂ)),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
          (∀ w : ℂ,
            B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
              (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
              (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable))
    (htipLocal : ∀ p : ℂ,
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        ∃ rLocal : ℝ,
          0 < rLocal ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_offOtherPoint_basinOmega
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch hxK hxoff₂ ?_
  intro p u huU hpfront hpoff₂ _hpcl Q s hnt hEqOn
  obtain ⟨Q', s', N, B, hnt', hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    hprimitiveSqfreeBad Q s hnt hEqOn
  obtain ⟨w, _hwU, hwoff₂, hBne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγmatch hB0
  obtain ⟨hleadw, hsepw⟩ := hBgood w hBne
  obtain ⟨rLocal, hrLocal, htip⟩ := htipLocal p hpfront hpoff₂
  exact ⟨Q', s', N, w, rLocal, hnt', hEqOn', hsupp, hN, hN1, hwoff₂, hleadw, hsepw,
    hrLocal, htip⟩

/-- **Connected q62 from the primitive/squarefree bad-locus package.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_primitiveSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hprimitiveSqfreeBad : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
          (B : Polynomial (Polynomial ℂ)),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
          (∀ w : ℂ,
            B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
              (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
              (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable))
    (htipLocal : ∀ p : ℂ,
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        ∃ rLocal : ℝ,
          0 < rLocal ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_primitiveSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hxK hxoff₂ hprimitiveSqfreeBad htipLocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation with the primitive/squarefree bad-locus producer built internally.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (htipLocal : ∀ p : ℂ,
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        ∃ rLocal : ℝ,
          0 < rLocal ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_primitiveSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch hxK hxoff₂
    (by
      intro Q s hnt hEqOn
      exact primitiveSqfreeBad_of_sparse_relation
        hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn)
    htipLocal

/-- **Connected q62 from radical squarefree bad-locus construction.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (htipLocal : ∀ p : ℂ,
        p ∈ frontier (filledJulia c₁) →
        p ∈ (filledJulia c₂)ᶜ →
        ∃ rLocal : ℝ,
          0 < rLocal ∧
          (∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
            ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_primitiveSqfreeBad_countableAvoidance_offOtherPoint_basinOmega
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG β γ hβan hβesc hβmod
    hKconn hempty hγan₂ hγmatch hxK hxoff₂
    (by
      intro Q s hnt hEqOn
      exact primitiveSqfreeBad_of_sparse_relation
        hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn)
    htipLocal

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Single normalized relation, local-tip form.**  This is the local-radius version of
`false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation`: a separable full-degree
fibre in a common region forces a continuation across the selected frontier point, and
`hnb_of_emptyInterior_modulus` supplies the empty-interior contradiction. -/
theorem false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation_localTip
    (hUo : IsOpen U) (_hUc : IsPreconnected U) (hUne : U.Nonempty)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁)
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U)
    {N : ℕ} {z₀ : ℂ} {r rTip : ℝ} {V : Set ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (hlead : (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0)
    (hsep : (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable)
    (hfront : z₀ ∈ frontier (filledJulia c₁)) (hz₀off : z₀ ∈ (filledJulia c₂)ᶜ)
    (hr : 0 < r) (hrTip : 0 < rTip) (_hVo : IsOpen V) (hVc : IsPreconnected V)
    (hUV : U ⊆ V) (hVbasin : V ⊆ (filledJulia c₁)ᶜ)
    (hsectorV : Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V)
    (hγV : AnalyticOnNhd ℂ γ V)
    (htip : ∀ ρ, 0 < ρ → ρ ≤ rTip →
      IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    False := by
  let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
  have haV : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V := by
    intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγV (Q i)
  have hγAt : AnalyticAt ℂ γ z₀ := hγan₂ z₀ hz₀off
  have haAt : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀ := by
    intro i _hi
    exact (analyticAt_eval₂_of_analyticAt hγAt (Q i)).contDiffAt
  have hmatch : ∀ i ∈ s, ∀ z ∈ U,
      a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
    intro i _hi z hz
    dsimp [a]
    simpa using congrArg (fun w => (Q i).eval₂ (Polynomial.evalRingHom z) w) (hγmatch z hz)
  have hrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    calc
      ∑ i ∈ s, a i z * (β z) ^ i
          = ∑ i ∈ s,
              ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z)) *
                (bottcherCoord c₁ z) ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hmatch i hi z hz, hβesc z (hU₁ hz)]
      _ = 0 := hEqOn hz
  have hβV : AnalyticOnNhd ℂ β V := hβan.mono hVbasin
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (β z) ^ i) V :=
    analyticOnNhd_relation_analytic haV hβV
  obtain ⟨u, huU⟩ := hUne
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [hUo.mem_nhds huU] with z hz
    exact hrelU z hz
  have hrelV : Set.EqOn (fun z => ∑ i ∈ s, a i z * (β z) ^ i) 0 V :=
    hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc (hUV huU) hev
  have hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ) :=
    hβan.continuousOn.mono inter_subset_right
  have hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0 := fun z hz => hrelV (hsectorV hz)
  exact (hnb_of_emptyInterior_modulus hempty hβmod z₀ hfront)
    (continuesAcross_of_global_basin_branch_analytic_localTip hsupp hN hN1 haAt
      (by simpa [a] using hlead) (by simpa [a] using hsep) hr hrTip hfront htip hβc hβrel)

/-- **NoRelation from normalized relations plus local-radius carrier-closure targets.**  A raw sparse
relation may be replaced by a normalized relation `Q',s'`; the target package only needs local-tip
preconnectedness below some positive radius at the selected countable-avoidance targets. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_carrierClosureLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnormalize : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
          (Ω : Set ℂ) (w : ℂ) (S : Set ℂ),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s', AnalyticOnNhd ℂ
            (fun z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable ∧
          (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
          (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, Ω, w, S, _hnt', hEqOn', hsupp, hN, hN1, hΩc, haΩ,
    hw, hleadw, hsepw, havoid, hSclosure, hgeom⟩ := hnormalize Q s hnt hEqOn
  let a : ℕ → ℂ → ℂ := fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)
  obtain ⟨N', z₀, r, rTip, V, hsupp', hN', hN1', hlead, hsep, hfront, hz₀off,
    hr, hrTip, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
    exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_carrierClosure_localTip
      (U := U) (a := a) (s := s') (N := N) (c₁ := c₁) (c₂ := c₂)
      hempty hUo hUc hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
      (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
      hN1 hsupp hN hΩc (by simpa [a] using haΩ) hw (by simpa [a] using hleadw)
      (by simpa [a] using hsepw) havoid hSclosure hgeom
  exact false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation_localTip
    hUo hUc hUne c₁ c₂ hU₁ β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    Q' s' hEqOn' hsupp' hN' hN1' (by simpa [a] using hlead) (by simpa [a] using hsep)
    hfront hz₀off hr hrTip hVo hVc hUV hVbasin₁ hsectorV (hγan₂.mono hVbasin₂) htip

/-- **NoRelation from radical squarefree algebra plus rotated local-slit carrier-closure targets.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (S : Set ℂ)
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T)
    (hSclosure : ∀ z₀ ∈ S, z₀ ∈ closure U)
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_carrierClosureLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch ?_
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, B, hnt', hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn
  obtain ⟨w, _hwU, hwoff₂, hBne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγmatch hB0
  obtain ⟨hleadw, hsepw⟩ := hBgood w hBne
  refine ⟨Q', s', N, (filledJulia c₂)ᶜ, w, S, hnt', hEqOn', hsupp, hN, hN1,
    isPreconnected_compl_filledJulia c₂, ?_, hwoff₂, hleadw, hsepw, ?_, hSclosure, ?_⟩
  · intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγan₂ (Q' i)
  · intro T hT
    obtain ⟨z₀, hzS, hzoff, hznot⟩ := havoid T hT
    exact ⟨z₀, hzS, hzoff, hznot⟩
  · intro z₀ hzS
    obtain ⟨hzK, hzoff, u, rTip, hu, hrTip, hslit⟩ := hgeom z₀ hzS
    exact ⟨hzK, hzoff, rTip, hrTip,
      local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
        (K := filledJulia c₁) (u := u) (z₀ := z₀) (R := rTip) hu hslit⟩

/-- **Connected q62 from radical squarefree algebra plus rotated local-slit carrier-closure targets.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (S : Set ℂ)
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T)
    (hSclosure : ∀ z₀ ∈ S, z₀ ∈ closure U)
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
        hγan₂ hγmatch S havoid hSclosure hgeom))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Rotated-slit target-set manufacturer.**  From a connected empty-interior filled Julia set, a local
carrier sector, an off-other ball, and pointwise rotated-slit sectors on the local frontier slice, build
the exact countable-avoidance carrier-closure target package used by the radical-squarefree endpoint. -/
theorem exists_carrierClosure_rotatedSlitSector_target_set_of_preconnected_emptyInterior
    {Ω : Set ℂ} {c₁ c₂ p : ℂ} {rLocal rOther : ℝ}
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
    exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
      (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
      hrLocal hrOther hsector hother
  refine ⟨S, havoid, hclosure, ?_⟩
  intro z₀ hz₀S
  obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
  exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
    hlocal z₀ ⟨⟨hzball, hzfront⟩, hzoff₂⟩⟩

/-- **NoRelation from a local rotated-slit frontier window, with radical squarefree algebra internal.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal rOther : ℝ}
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨S, havoidΩ, hSclosure, hgeom⟩ :=
    exists_carrierClosure_rotatedSlitSector_target_set_of_preconnected_emptyInterior
      (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
      hrLocal hrOther hsector hother hlocal
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₂ hγmatch S ?_ hSclosure hgeom
  intro T hT
  obtain ⟨z₀, hzS, _hzΩ, hznot⟩ := havoidΩ T hT
  exact ⟨z₀, hzS, (hgeom z₀ hzS).2.1, hznot⟩

/-- **Connected q62 from a local rotated-slit frontier window, with radical squarefree algebra internal.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal rOther : ℝ}
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hpK hpΩ hrLocal hrOther hsector hother hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a local rotated-slit frontier window in the full `K₂ᶜ` analytic basin.**  This
specializes the target-window endpoint to `Ω = (filledJulia c₂)ᶜ`, so the caller supplies only
`p ∈ K₂ᶜ`; the off-other ball and interior proof are obtained from closedness of `K₂`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {p : ℂ} {rLocal : ℝ}
    (hpK : p ∈ filledJulia c₁) (hpoff₂ : p ∈ (filledJulia c₂)ᶜ)
    (hrLocal : 0 < rLocal)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff₂
  have hpΩ : p ∈ interior ((filledJulia c₂)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff₂)
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch (Ω := (filledJulia c₂)ᶜ) hpK hpΩ hrLocal hrOther hsector hother hlocal

/-- **Connected q62 from a local rotated-slit frontier window in the full `K₂ᶜ` analytic basin.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow_basinOmega
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {p : ℂ} {rLocal : ℝ}
    (hpK : p ∈ filledJulia c₁) (hpoff₂ : p ∈ (filledJulia c₂)ᶜ)
    (hrLocal : 0 < rLocal)
    (hsector : Metric.ball p rLocal ∩ (filledJulia c₁)ᶜ ⊆ U)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_localFrontierRotatedSlitWindow_basinOmega
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hpK hpoff₂ hrLocal hsector hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Target-set manufacturer from an uncountable closure slice.**  This is the closure-hop form of the
rotated-slit target package: instead of requiring a full local basin sector contained in `U`, it assumes
the local frontier/off-other slice itself is uncountable after intersecting the analytic region and lies in
`closure U`. -/
theorem exists_carrierClosure_rotatedSlitSector_target_set_of_uncountable_closure
    {Ω : Set ℂ} {c₁ c₂ p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hclosure : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      z₀ ∈ closure U)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure U) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  let S : Set ℂ := (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hnone
    push Not at hnone
    have hsub : S ∩ Ω ⊆ T := by
      intro z hz
      exact hnone z hz.1 hz.2
    exact hunc (hT.mono hsub)
  · intro z₀ hzS
    exact hclosure z₀ hzS
  · intro z₀ hzS
    exact ⟨mem_filledJulia_of_frontier hzS.1.2, hzS.2, hlocal z₀ hzS⟩

/-- **NoRelation from an uncountable closure slice with rotated local slits.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_closureSliceRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hclosure : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      z₀ ∈ closure U)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨S, havoidΩ, hSclosure, hgeom⟩ :=
    exists_carrierClosure_rotatedSlitSector_target_set_of_uncountable_closure
      (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal)
      hunc hclosure hlocal
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_carrierClosureRotatedSlitSectorLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₂ hγmatch S ?_ hSclosure hgeom
  intro T hT
  obtain ⟨z₀, hzS, _hzΩ, hznot⟩ := havoidΩ T hT
  exact ⟨z₀, hzS, (hgeom z₀ hzS).2.1, hznot⟩

/-- **Connected q62 from an uncountable closure slice with rotated local slits.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_closureSliceRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hclosure : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      z₀ ∈ closure U)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_closureSliceRotatedSlit
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
        hγan₂ hγmatch hunc hclosure hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Local-tip countable-avoidance crossing from common-component closure.**  This factors the
closure-hop argument: if every target lies in the closure of the common-basin component containing the
carrier, then a local tip model at the selected target pushes a small punctured ball into that component. -/
theorem exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent_localTip
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c₁ c₂ : ℂ}
    (hempty : interior (filledJulia c₁) = ∅)
    (_hUo : IsOpen U) (hUc : IsPreconnected U) (_hUne : U.Nonempty)
    (hUbasin₁ : U ⊆ (filledJulia c₁)ᶜ) (hUbasin₂ : U ⊆ (filledJulia c₂)ᶜ)
    (hN1 : 1 ≤ N) (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a N w ≠ 0) (hsepw : (fibrePoly a s w).Separable)
    {S : Set ℂ}
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ rTip : ℝ, 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    ∃ (N' : ℕ) (z₀ : ℂ) (r rTip : ℝ) (V : Set ℂ),
      s ⊆ Finset.range (N' + 1) ∧ N' ∈ s ∧ 1 ≤ N' ∧
      a N' z₀ ≠ 0 ∧
      (fibrePoly a s z₀).Separable ∧
      z₀ ∈ frontier (filledJulia c₁) ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
      V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
      (∀ ρ, 0 < ρ → ρ ≤ rTip →
        IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) := by
  obtain ⟨u, huU, hcl⟩ := hcomponent
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVo : IsOpen V := by
    simpa [V] using hCo.connectedComponentIn
  have hVc : IsPreconnected V := by
    simpa [V] using (isPreconnected_connectedComponentIn (x := u) (F := C))
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  have hVbasin₂ : V ⊆ (filledJulia c₂)ᶜ := fun z hz => (hVsubC hz).2
  have hUC : U ⊆ C := fun z hz => ⟨hUbasin₁ hz, hUbasin₂ hz⟩
  have hUV : U ⊆ V := by
    simpa [V, C] using hUc.subset_connectedComponentIn huU hUC
  exact exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_localTip
    (U := U) (a := a) (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
    hN1 hsupp hN hΩc ha hw hleadw hsepw havoid (by
      intro z₀ hz₀S
      obtain ⟨hz₀K₁, hz₀off₂, rTip, hrTip, htip⟩ := hgeom z₀ hz₀S
      obtain ⟨rOther, hrOther, hball₂⟩ :=
        Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl z₀ hz₀off₂
      let r : ℝ := min rOther rTip
      have hr : 0 < r := by
        simpa [r] using lt_min hrOther hrTip
      have hr_le_other : r ≤ rOther := by
        simp [r]
      have hr_le_tip : r ≤ rTip := by
        simp [r]
      have hz₀front : z₀ ∈ frontier (filledJulia c₁) := by
        rw [(isClosed_filledJulia c₁).frontier_eq]
        exact ⟨hz₀K₁, by simp [hempty]⟩
      refine ⟨r, rTip, V, hz₀front, hz₀off₂, hr, hrTip, hVo, hVc, hUV, hVbasin₁,
        hVbasin₂, ?_, htip⟩
      set W : Set ℂ := Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ with hW
      have hWc : IsPreconnected W := by
        simpa [W] using htip r hr hr_le_tip
      have hWC : W ⊆ C := by
        intro z hz
        have hzballOther : z ∈ Metric.ball z₀ rOther :=
          Metric.ball_subset_ball hr_le_other hz.1
        exact ⟨hz.2, hball₂ hzballOther⟩
      have hz₀clV : z₀ ∈ closure V := by
        simpa [V, C] using hcl z₀ hz₀S
      have hmeet : (Metric.ball z₀ r ∩ V).Nonempty := by
        rw [_root_.mem_closure_iff] at hz₀clV
        exact hz₀clV (Metric.ball z₀ r) isOpen_ball (Metric.mem_ball_self hr)
      obtain ⟨y, hyball, hyV⟩ := hmeet
      have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
      have hWsubCompY : W ⊆ connectedComponentIn C y :=
        hWc.subset_connectedComponentIn hyW hWC
      have hcomp : connectedComponentIn C y = V := by
        have h := connectedComponentIn_eq (by simpa [V] using hyV)
        simpa [V] using h.symm
      intro z hz
      exact hcomp ▸ hWsubCompY (by simpa [W] using hz))

/-- **NoRelation from normalized relations plus common-component local-tip targets.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_commonComponentLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnormalize : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
          (Ω : Set ℂ) (w : ℂ) (S : Set ℂ),
          (∃ i ∈ s', (Q' i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) ∧
          Set.EqOn (fun z => ∑ i ∈ s',
              ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
                * (bottcherCoord c₁ z) ^ i) 0 U ∧
          s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s', AnalyticOnNhd ℂ
            (fun z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable ∧
          (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ Ω ∧ z₀ ∉ T) ∧
          (∃ u ∈ U,
            ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
          (∀ z₀ ∈ S,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            (∃ rTip : ℝ, 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, Ω, w, S, _hnt', hEqOn', hsupp, hN, hN1, hΩc, haΩ,
    hw, hleadw, hsepw, havoid, hcomponent, hgeom⟩ := hnormalize Q s hnt hEqOn
  let a : ℕ → ℂ → ℂ := fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)
  obtain ⟨N', z₀, r, rTip, V, hsupp', hN', hN1', hlead, hsep, hfront, hz₀off,
    hr, hrTip, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
    exists_commonBasin_frontier_input_of_sparse_fibre_countableAvoidance_emptyInterior_commonComponent_localTip
      (U := U) (a := a) (s := s') (N := N) (c₁ := c₁) (c₂ := c₂)
      hempty hUo hUc hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
      (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
      hN1 hsupp hN hΩc (by simpa [a] using haΩ) hw (by simpa [a] using hleadw)
      (by simpa [a] using hsepw) havoid hcomponent hgeom
  exact false_of_emptyInterior_commonRegion_gamma_offOther_branch_separable_relation_localTip
    hUo hUc hUne c₁ c₂ hU₁ β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    Q' s' hEqOn' hsupp' hN' hN1' (by simpa [a] using hlead) (by simpa [a] using hsep)
    hfront hz₀off hr hrTip hVo hVc hUV hVbasin₁ hsectorV (hγan₂.mono hVbasin₂) htip

/-- **NoRelation from radical squarefree algebra plus common-component rotated-slit targets.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (S : Set ℂ)
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_commonComponentLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch ?_
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, B, hnt', hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn
  obtain ⟨w, _hwU, hwoff₂, hBne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγmatch hB0
  obtain ⟨hleadw, hsepw⟩ := hBgood w hBne
  refine ⟨Q', s', N, (filledJulia c₂)ᶜ, w, S, hnt', hEqOn', hsupp, hN, hN1,
    isPreconnected_compl_filledJulia c₂, ?_, hwoff₂, hleadw, hsepw, ?_, hcomponent, ?_⟩
  · intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγan₂ (Q' i)
  · intro T hT
    obtain ⟨z₀, hzS, hzoff, hznot⟩ := havoid T hT
    exact ⟨z₀, hzS, hzoff, hznot⟩
  · intro z₀ hzS
    obtain ⟨hzK, hzoff, u, rTip, hu, hrTip, hslit⟩ := hgeom z₀ hzS
    exact ⟨hzK, hzoff, rTip, hrTip,
      local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
        (K := filledJulia c₁) (u := u) (z₀ := z₀) (R := rTip) hu hslit⟩

/-- **Connected q62 from radical squarefree algebra plus common-component rotated-slit targets.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (S : Set ℂ)
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
        hγan₂ hγmatch S havoid hcomponent hgeom))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Common-component target-set manufacturer from an uncountable closure slice.**  This is the
component-closure version of `exists_carrierClosure_rotatedSlitSector_target_set_of_uncountable_closure`:
the selected targets are the local frontier/off-other slice, and the caller supplies that the whole
slice lies in the closure of one fixed common-basin component. -/
theorem exists_commonComponent_rotatedSlitSector_target_set_of_uncountable_closure
    {Ω : Set ℂ} {c₁ c₂ p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hcomponentClosure : ∃ u ∈ U,
      ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
        z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
      (∃ u ∈ U,
        ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  let S : Set ℂ := (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    by_contra hnone
    push Not at hnone
    have hsub : S ∩ Ω ⊆ T := by
      intro z hz
      exact hnone z hz.1 hz.1.2
    exact hunc (by simpa [S] using hT.mono hsub)
  · rcases hcomponentClosure with ⟨u, huU, hucl⟩
    exact ⟨u, huU, by intro z₀ hzS; exact hucl z₀ hzS⟩
  · intro z₀ hzS
    exact ⟨mem_filledJulia_of_frontier hzS.1.2, hzS.2, hlocal z₀ hzS⟩

/-- **NoRelation from an uncountable common-component closure slice with rotated local slits.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosureSliceRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hcomponentClosure : ∃ u ∈ U,
      ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
        z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨S, havoid, hcomponent, hgeom⟩ :=
    exists_commonComponent_rotatedSlitSector_target_set_of_uncountable_closure
      (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) (p := p) (rLocal := rLocal)
      hunc hcomponentClosure hlocal
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₂ hγmatch S havoid hcomponent hgeom

/-- **Connected q62 from an uncountable common-component closure slice with rotated local slits.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosureSliceRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p : ℂ} {rLocal : ℝ}
    (hunc : ¬ ((((Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ) ∩ Ω).Countable))
    (hcomponentClosure : ∃ u ∈ U,
      ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
        z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosureSliceRotatedSlit
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
        hγan₂ hγmatch hunc hcomponentClosure hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Common-component rotated-slit targets from one closure point.**  A single point `p` in the closure
of the common-basin component, together with a rotated local slit at `p`, gives a small full punctured
basin ball contained in that component.  The connected empty-interior frontier selector then supplies a
countable-avoidance target set whose every point lies in the closure of the same component. -/
theorem exists_commonComponent_rotatedSlitSector_target_set_of_preconnected_emptyInterior_closurePoint
    {Ω : Set ℂ} {c₁ c₂ p u : ℂ} {rLocal rOther : ℝ}
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (huU : u ∈ U)
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
      (∃ u ∈ U,
        ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  have hpfront : p ∈ frontier (filledJulia c₁) := mem_frontier_of_mem_filledJulia_emptyInterior hempty hpK
  have hpoff₂ : p ∈ (filledJulia c₂)ᶜ := hother (Metric.mem_ball_self hrOther)
  have hpLocal : p ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ :=
    ⟨⟨Metric.mem_ball_self hrLocal, hpfront⟩, hpoff₂⟩
  obtain ⟨ζ, rTip, hζ, hrTip, hslitp⟩ := hlocal p hpLocal
  set r : ℝ := min (min rLocal rOther) rTip with hrdef
  have hr : 0 < r := by rw [hrdef]; exact lt_min (lt_min hrLocal hrOther) hrTip
  have hr_le_local : r ≤ rLocal := by
    rw [hrdef]
    exact (min_le_left (min rLocal rOther) rTip).trans (min_le_left rLocal rOther)
  have hr_le_other : r ≤ rOther := by
    rw [hrdef]
    exact (min_le_left (min rLocal rOther) rTip).trans (min_le_right rLocal rOther)
  have hr_le_tip : r ≤ rTip := by rw [hrdef]; exact min_le_right _ _
  have hpTip : IsPreconnected (Metric.ball p r ∩ (filledJulia c₁)ᶜ) :=
    local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
      (K := filledJulia c₁) (u := ζ) (z₀ := p) (R := rTip) hζ hslitp r hr hr_le_tip
  have hsectorV : Metric.ball p r ∩ (filledJulia c₁)ᶜ ⊆ V := by
    set W : Set ℂ := Metric.ball p r ∩ (filledJulia c₁)ᶜ with hW
    have hWc : IsPreconnected W := by simpa [W] using hpTip
    have hWC : W ⊆ C := by
      intro z hz
      exact ⟨hz.2, hother (Metric.ball_subset_ball hr_le_other hz.1)⟩
    have hpclV : p ∈ closure V := by simpa [V, C] using hpcl
    have hmeet : (Metric.ball p r ∩ V).Nonempty := by
      rw [_root_.mem_closure_iff] at hpclV
      exact hpclV (Metric.ball p r) isOpen_ball (Metric.mem_ball_self hr)
    obtain ⟨y, hyball, hyV⟩ := hmeet
    have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
    have hWsubCompY : W ⊆ connectedComponentIn C y :=
      hWc.subset_connectedComponentIn hyW hWC
    have hcomp : connectedComponentIn C y = V := by
      have h := connectedComponentIn_eq (by simpa [V] using hyV)
      simpa [V] using h.symm
    intro z hz
    exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
  obtain ⟨S, havoidΩ, hclosure, hSlocal⟩ :=
    exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
      (U := V) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
      hr hrOther hsectorV hother
  refine ⟨S, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨z₀, hzS, _hzΩ, hznot⟩ := havoidΩ T hT
    exact ⟨z₀, hzS, (hSlocal z₀ hzS).2.2, hznot⟩
  · refine ⟨u, huU, ?_⟩
    intro z₀ hzS
    simpa [V, C] using hclosure z₀ hzS
  · intro z₀ hzS
    obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hzS
    have hzballLocal : z₀ ∈ Metric.ball p rLocal := Metric.ball_subset_ball hr_le_local hzball
    exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂,
      hlocal z₀ ⟨⟨hzballLocal, hzfront⟩, hzoff₂⟩⟩

/-- **NoRelation from one common-component closure point and rotated local slits.** -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosurePointRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p u : ℂ} {rLocal rOther : ℝ}
    (huU : u ∈ U)
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨S, havoid, hcomponent, hgeom⟩ :=
    exists_commonComponent_rotatedSlitSector_target_set_of_preconnected_emptyInterior_closurePoint
      (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) (p := p) (u := u)
      hKconn hempty huU hpK hpΩ hpcl hrLocal hrOther hother hlocal
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₂ hγmatch S havoid hcomponent hgeom

/-- **Connected q62 from one common-component closure point and rotated local slits.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosurePointRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {Ω : Set ℂ} {p u : ℂ} {rLocal rOther : ℝ}
    (huU : u ∈ U)
    (hpK : p ∈ filledJulia c₁) (hpΩ : p ∈ interior Ω)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hrLocal : 0 < rLocal) (hrOther : 0 < rOther)
    (hother : Metric.ball p rOther ⊆ (filledJulia c₂)ᶜ)
    (hlocal : ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
      ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
            Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosurePointRotatedSlit
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch huU hpK hpΩ hpcl hrLocal hrOther hother hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from one off-other filled-Julia witness and rotated local slits.**  The existing
common-component crossing lemma manufactures the frontier point `p` in the closure of the common-basin
component; the new closure-point rotated-slit wrapper then supplies countable avoidance and the radical
squarefree contradiction. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hlocal : ∀ p, p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨u, huU⟩ := hUne
  have huC : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
      escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
  obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component
      (a := c₁) (b := c₂) (u := u) (x := x) huC hxK hxoff₂
  obtain ⟨rLocal, hrLocal, hlocalp⟩ := hlocal p hpfront hpoff₂
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff₂
  have hpΩ : p ∈ interior ((filledJulia c₂)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff₂)
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentClosurePointRotatedSlit
    hUo hUc ⟨u, huU⟩ hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
    hγan₂ hγmatch (Ω := (filledJulia c₂)ᶜ) (p := p) (u := u) huU
    (mem_filledJulia_of_frontier hpfront) hpΩ hpcl hrLocal hrOther hother hlocalp

/-- **Connected q62 from one off-other filled-Julia witness and rotated local slits.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hlocal : ∀ p, p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlit
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
        hγan₂ hγmatch hxK hxoff₂ hlocal))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from distinct parameters, by symmetric difference and rotated local slits.**  Distinct
parameters give a point in `K₁ \ K₂` or in `K₂ \ K₁`.  The first branch is the off-other-point wrapper;
the second branch applies the same wrapper with the parameters swapped and then uses `noRelation_symm`.
The branch/modulus hypotheses are supplied for both coordinates, because the swapped branch genuinely
needs the first-coordinate branch data for `c₂`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p, p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)
    (hlocal₂ : ∀ p, p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₂)) ∩ (filledJulia c₁)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₂)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hβ₁match : ∀ z ∈ U, β₁ z = bottcherCoord c₁ z := fun z hz => hβ₁esc z (hU₁ hz)
  have hβ₂match : ∀ z ∈ U, β₂ z = bottcherCoord c₂ z := fun z hz => hβ₂esc z (hU₂ hz)
  obtain ⟨x, hx | hx⟩ := exists_point_filledJulia_symmDiff hne
  · exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlit
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod hKconn₁ hempty₁
      hβ₂an hβ₂match hx.1 hx.2 hlocal₁
  · have hswap :
        NoRelation (RatFunc ℂ) (phiMero c₂ hU₂) (phiMero c₁ hU₁) :=
      noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlit
        hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁ hG₁ β₂ β₁ hβ₂an hβ₂esc hβ₂mod hKconn₂ hempty₂
        hβ₁an hβ₁match hx.1 hx.2 hlocal₂
    exact noRelation_symm hswap

/-- **Connected q62-facing symmetric-difference rotated-slit endpoint.**  The exceptional hypotheses are
kept in the interface used by the connected q62 lane; this endpoint proves the stronger direct
`NoRelation` conclusion through the symmetric-difference split. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlit
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p, p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₁)) ∩ (filledJulia c₂)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)
    (hlocal₂ : ∀ p, p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      ∃ rLocal : ℝ, 0 < rLocal ∧
        ∀ z₀ ∈ (Metric.ball p rLocal ∩ frontier (filledJulia c₂)) ∩ (filledJulia c₁)ᶜ,
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₂)ᶜ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlit
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hlocal₁ hlocal₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from one off-other witness plus a slit-good target selector.**  This is the safer
replacement for requiring every nearby frontier point to have a rotated slit.  The selector only has to
produce a countable-avoidance set of slit-good targets in the closure of the common-basin component
manufactured from the witness `x ∈ K₁ \ K₂`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlitSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff₂ : x ∈ (filledJulia c₂)ᶜ)
    (hselector : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ S : Set ℂ,
        (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
        (∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        (∀ z₀ ∈ S,
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨u, huU⟩ := hUne
  have huC : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
      escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
  obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component
      (a := c₁) (b := c₂) (u := u) (x := x) huC hxK hxoff₂
  obtain ⟨S, havoid, hScomp, hgeom⟩ := hselector p u huU hpfront hpoff₂ hpcl
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentRotatedSlitLocalTip
    hUo hUc ⟨u, huU⟩ hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    S havoid ⟨u, huU, hScomp⟩ hgeom

/-- **NoRelation from distinct parameters plus symmetric slit-good target selectors.**  This follows the
same symmetric-difference split as the pointwise-local-slit endpoint, but the geometric input is now the
safer selector form: each branch only needs a countable-avoidance supply of slit-good targets in the
common-component closure. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hselector₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ S : Set ℂ,
        (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
        (∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        (∀ z₀ ∈ S,
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))
    (hselector₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ S : Set ℂ,
        (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₁)ᶜ ∧ z₀ ∉ T) ∧
        (∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        (∀ z₀ ∈ S,
          z₀ ∈ filledJulia c₂ ∧
          z₀ ∈ (filledJulia c₁)ᶜ ∧
          ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                Metric.ball z₀ ρ ∩ (filledJulia c₂)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hβ₁match : ∀ z ∈ U, β₁ z = bottcherCoord c₁ z := fun z hz => hβ₁esc z (hU₁ hz)
  have hβ₂match : ∀ z ∈ U, β₂ z = bottcherCoord c₂ z := fun z hz => hβ₂esc z (hU₂ hz)
  obtain ⟨x, hx | hx⟩ := exists_point_filledJulia_symmDiff hne
  · exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlitSelector
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod hempty₁
      hβ₂an hβ₂match hx.1 hx.2 hselector₁
  · have hswap :
        NoRelation (RatFunc ℂ) (phiMero c₂ hU₂) (phiMero c₁ hU₁) :=
      noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_offOtherPointRotatedSlitSelector
        hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁ hG₁ β₂ β₁ hβ₂an hβ₂esc hβ₂mod hempty₂
        hβ₁an hβ₁match hx.1 hx.2 hselector₂
    exact noRelation_symm hswap

end Bottcher

namespace Bottcher

/-- **Selector package from an uncountable slit-good set.**  This is the Lean bridge for the external-ray
or landing-point route: once a candidate slit-good set `G` is uncountable, lies off the other filled
Julia set, stays in the closure of one fixed common-basin component, and carries the rotated-slit local
geometry, it supplies exactly the selector consumed by the symmetric-difference endpoint. -/
theorem exists_commonComponent_rotatedSlitSelector_of_uncountable_goodSet
    {c₁ c₂ u : ℂ} {G : Set ℂ}
    (hunc : ¬ G.Countable)
    (hoff : ∀ z ∈ G, z ∈ (filledJulia c₂)ᶜ)
    (hcomp : ∀ z ∈ G,
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z ∈ G,
      z ∈ filledJulia c₁ ∧
      z ∈ (filledJulia c₂)ᶜ ∧
      ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
            Metric.ball z ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {w | v * (w - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  refine ⟨G, ?_, hcomp, hgeom⟩
  intro T hT
  by_contra hnone
  push Not at hnone
  have hsub : G ⊆ T := by
    intro z hz
    exact hnone z hz (hoff z hz)
  exact hunc (hT.mono hsub)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from distinct parameters plus symmetric uncountable slit-good sets.**  This is the
selector endpoint with the selector built internally from an uncountable slit-good set in the relevant
common-component closure.  It is the Lean-facing form of the external-ray/landing-point strategy: future
geometry only has to prove the `hgood` providers, not re-enter the algebra or countable-avoidance stack. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodSet
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hgood₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ (filledJulia c₂)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        (∀ z ∈ G,
          z ∈ filledJulia c₁ ∧
          z ∈ (filledJulia c₂)ᶜ ∧
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₁)ᶜ))
    (hgood₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ (filledJulia c₁)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        (∀ z ∈ G,
          z ∈ filledJulia c₂ ∧
          z ∈ (filledJulia c₁)ᶜ ∧
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₂)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitSelector
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨G, hunc, hoff, hcomp, hgeom⟩ := hgood₁ p u huU hpfront hpoff hpcl
    exact exists_commonComponent_rotatedSlitSelector_of_uncountable_goodSet hunc hoff hcomp hgeom
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨G, hunc, hoff, hcomp, hgeom⟩ := hgood₂ p u huU hpfront hpoff hpcl
    exact exists_commonComponent_rotatedSlitSelector_of_uncountable_goodSet hunc hoff hcomp hgeom

/-- **Connected q62-facing endpoint from symmetric uncountable slit-good sets.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodSet
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hgood₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ (filledJulia c₂)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        (∀ z ∈ G,
          z ∈ filledJulia c₁ ∧
          z ∈ (filledJulia c₂)ᶜ ∧
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₁)ᶜ))
    (hgood₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ (filledJulia c₁)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        (∀ z ∈ G,
          z ∈ filledJulia c₂ ∧
          z ∈ (filledJulia c₁)ᶜ ∧
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₂)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodSet
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ hgood₁ hgood₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Selector package from an uncountable frontier slit-good set.**  This is the corrected
harmonic-measure/accessibility shape: targets lie on `frontier K₁` and carry a one-sided rotated slit
sector in `K₁ᶜ`.  Frontier membership supplies `z ∈ K₁`; the slit sector supplies the local geometry. -/
theorem exists_commonComponent_rotatedSlitSelector_of_uncountable_frontier_goodSet
    {c₁ c₂ u : ℂ} {G : Set ℂ}
    (hunc : ¬ G.Countable)
    (hfront : ∀ z ∈ G, z ∈ frontier (filledJulia c₁))
    (hoff : ∀ z ∈ G, z ∈ (filledJulia c₂)ᶜ)
    (hcomp : ∀ z ∈ G,
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hslit : ∀ z ∈ G,
      ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
            Metric.ball z ρ ∩ (filledJulia c₁)ᶜ) :
    ∃ S : Set ℂ,
      (∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T) ∧
      (∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      (∀ z₀ ∈ S,
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            Metric.ball z₀ ρ ∩ {w | v * (w - z₀) ∈ Complex.slitPlane} ⊆
              Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ) := by
  exact exists_commonComponent_rotatedSlitSelector_of_uncountable_goodSet
    hunc hoff hcomp (by
      intro z hz
      exact ⟨mem_filledJulia_of_frontier (hfront z hz), hoff z hz, hslit z hz⟩)

/-- **NoRelation from symmetric uncountable frontier slit-good sets.**  This is the direct endpoint for
Grok's harmonic-measure/accessibility lead: in each possible symmetric-difference branch, supply an
uncountable set of frontier points in the relevant component closure, off the other filled Julia set, with
one-sided rotated slit sectors in the active basin. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitFrontierGoodSet
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hfrontgood₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ frontier (filledJulia c₁)) ∧
        (∀ z ∈ G, z ∈ (filledJulia c₂)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        (∀ z ∈ G,
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₁)ᶜ))
    (hfrontgood₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ G : Set ℂ,
        ¬ G.Countable ∧
        (∀ z ∈ G, z ∈ frontier (filledJulia c₂)) ∧
        (∀ z ∈ G, z ∈ (filledJulia c₁)ᶜ) ∧
        (∀ z ∈ G, z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        (∀ z ∈ G,
          ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
            ∀ ρ, 0 < ρ → ρ ≤ rTip →
              Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
                Metric.ball z ρ ∩ (filledJulia c₂)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodSet
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨G, hunc, hfront, hoff, hcomp, hslit⟩ := hfrontgood₁ p u huU hpfront hpoff hpcl
    refine ⟨G, hunc, hoff, hcomp, ?_⟩
    intro z hz
    exact ⟨mem_filledJulia_of_frontier (hfront z hz), hoff z hz, hslit z hz⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨G, hunc, hfront, hoff, hcomp, hslit⟩ := hfrontgood₂ p u huU hpfront hpoff hpcl
    refine ⟨G, hunc, hoff, hcomp, ?_⟩
    intro z hz
    exact ⟨mem_filledJulia_of_frontier (hfront z hz), hoff z hz, hslit z hz⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A point is rotated-slit-good for `K_c` if some rotated translated slit sector based at that point
lies in the basin `K_cᶜ` below a positive radius. -/
def RotatedSlitGood (c z : ℂ) : Prop :=
  ∃ (v : ℂ) (rTip : ℝ), ‖v‖ = 1 ∧ 0 < rTip ∧
    ∀ ρ, 0 < ρ → ρ ≤ rTip →
      Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
        Metric.ball z ρ ∩ (filledJulia c)ᶜ

/-- **NoRelation from noncountability of the rotated-slit-good frontier locus.**  This is the tightest
current interface for the remaining geometry: for each common-component closure point, the locus of
frontier points that are off the other filled Julia set, remain in the same component closure, and are
rotated-slit-good is noncountable. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodLocus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hgood₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              RotatedSlitGood c₁ z} : Set ℂ).Countable)
    (hgood₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              RotatedSlitGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitFrontierGoodSet
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    let G : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              RotatedSlitGood c₁ z}
    refine ⟨G, hgood₁ p u huU hpfront hpoff hpcl, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2.1
    · intro z hz
      exact hz.2.2.1
    · intro z hz
      exact hz.2.2.2
  · intro p u huU hpfront hpoff hpcl
    let G : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              RotatedSlitGood c₂ z}
    refine ⟨G, hgood₂ p u huU hpfront hpoff hpcl, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact hz.1
    · intro z hz
      exact hz.2.1
    · intro z hz
      exact hz.2.2.1
    · intro z hz
      exact hz.2.2.2

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A fixed-direction version of `RotatedSlitGood`: the slit direction is supplied externally, so a
selector can first pigeonhole or otherwise force one direction and then hand the result to the existing
rotated-slit-good endpoint. -/
def FixedRotatedSlitGood (c v z : ℂ) : Prop :=
  ‖v‖ = 1 ∧ ∃ rTip : ℝ, 0 < rTip ∧
    ∀ ρ, 0 < ρ → ρ ≤ rTip →
      Metric.ball z ρ ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
        Metric.ball z ρ ∩ (filledJulia c)ᶜ

lemma rotatedSlitGood_of_fixedRotatedSlitGood {c v z : ℂ}
    (h : FixedRotatedSlitGood c v z) : RotatedSlitGood c z := by
  rcases h with ⟨hv, rTip, hrTip, hslit⟩
  exact ⟨v, rTip, hv, hrTip, hslit⟩

/-- **NoRelation from a fixed-direction slit-good frontier locus.**  This is the Grok fixed-direction
selector bridge: if every common-component closure point has a noncountable frontier/off-other/closure
locus with one fixed slit direction, then the existing rotated-slit-good locus endpoint applies. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffFixedRotatedSlitGoodLocus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hfixed₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧
        ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              FixedRotatedSlitGood c₁ v z} : Set ℂ).Countable)
    (hfixed₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧
        ¬ ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              FixedRotatedSlitGood c₂ v z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffRotatedSlitGoodLocus
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, _hv, hunc⟩ := hfixed₁ p u huU hpfront hpoff hpcl
    intro hcount
    exact hunc (hcount.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, rotatedSlitGood_of_fixedRotatedSlitGood hz.2.2.2⟩))
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, _hv, hunc⟩ := hfixed₂ p u huU hpfront hpoff hpcl
    intro hcount
    exact hunc (hcount.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1, rotatedSlitGood_of_fixedRotatedSlitGood hz.2.2.2⟩))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Local ray confinement at `z`: below some positive radius, the filled Julia set lies on the
excluded ray for the fixed rotated slit direction `v`.  This is the concrete local form of the
sector/rational-twist lead: once a cone boundary is straightened to the omitted ray, the complement is
a fixed rotated slit plane. -/
def LocalRayConfined (c v z : ℂ) : Prop :=
  ∃ rTip : ℝ, 0 < rTip ∧
    ∀ w, w ∈ Metric.ball z rTip → w ∈ filledJulia c →
      v * (w - z) ∉ Complex.slitPlane

lemma fixedRotatedSlitGood_of_localRayConfined {c v z : ℂ} (hv : ‖v‖ = 1)
    (h : LocalRayConfined c v z) : FixedRotatedSlitGood c v z := by
  rcases h with ⟨rTip, hrTip, hray⟩
  refine ⟨hv, rTip, hrTip, ?_⟩
  intro ρ hρ hρle w hw
  refine ⟨hw.1, ?_⟩
  intro hwK
  exact hray w (Metric.ball_subset_ball hρle hw.1) hwK hw.2

/-- **NoRelation from a fixed-direction local-ray-confined frontier locus.**  This is the local ray
version of the fixed-direction bridge: prove a noncountable common-component closure locus whose filled
Julia set is locally trapped in one omitted ray, and the existing slit-good endpoint fires. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedGoodLocus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hray₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧
        ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              LocalRayConfined c₁ v z} : Set ℂ).Countable)
    (hray₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧
        ¬ ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              LocalRayConfined c₂ v z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffFixedRotatedSlitGoodLocus
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hunc⟩ := hray₁ p u huU hpfront hpoff hpcl
    refine ⟨v, hv, ?_⟩
    intro hcount
    exact hunc (hcount.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1,
        fixedRotatedSlitGood_of_localRayConfined hv hz.2.2.2⟩))
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hunc⟩ := hray₂ p u huU hpfront hpoff hpcl
    refine ⟨v, hv, ?_⟩
    intro hcount
    exact hunc (hcount.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.1,
        fixedRotatedSlitGood_of_localRayConfined hv hz.2.2.2⟩))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a local-ray-confined selector set.**  This is the Cantor/perfect-subset version of
the local-ray bridge: the geometric step may now return any noncountable set `S` in the common-component
closure whose points are locally confined to one omitted ray. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hsel₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ ¬ S.Countable ∧
        S ⊆ frontier (filledJulia c₁) ∧
        S ⊆ (filledJulia c₂)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₁ v z)
    (hsel₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ ¬ S.Countable ∧
        S ⊆ frontier (filledJulia c₂) ∧
        S ⊆ (filledJulia c₁)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₂ v z) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedGoodLocus
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, S, hv, hSunc, hSfront, hSoff, hScl, hSray⟩ := hsel₁ p u huU hpfront hpoff hpcl
    refine ⟨v, hv, ?_⟩
    intro hcount
    exact hSunc (hcount.mono (by
      intro z hzS
      exact ⟨hSfront hzS, hSoff hzS, hScl hzS, hSray z hzS⟩))
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, S, hv, hSunc, hSfront, hSoff, hScl, hSray⟩ := hsel₂ p u huU hpfront hpoff hpcl
    refine ⟨v, hv, ?_⟩
    intro hcount
    exact hSunc (hcount.mono (by
      intro z hzS
      exact ⟨hSfront hzS, hSoff hzS, hScl hzS, hSray z hzS⟩))

/-- Connected-q62-facing form of the local-ray-confined selector endpoint. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hsel₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ ¬ S.Countable ∧
        S ⊆ frontier (filledJulia c₁) ∧
        S ⊆ (filledJulia c₂)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₁ v z)
    (hsel₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ ¬ S.Countable ∧
        S ⊆ frontier (filledJulia c₂) ∧
        S ⊆ (filledJulia c₁)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₂ v z) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedSelector
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ hsel₁ hsel₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma not_countable_of_perfect_nonempty {S : Set ℂ} (hS : Perfect S) (hne : S.Nonempty) :
    ¬ S.Countable := by
  rcases hne with ⟨z, hzS⟩
  have hunc : ¬ (Metric.ball z (1 : ℝ) ∩ S).Countable :=
    not_countable_ball_inter_perfect hS hzS (by norm_num)
  intro hScount
  exact hunc (hScount.mono inter_subset_right)

/-- **NoRelation from a perfect local-ray-confined selector set.**  This is the exact formal shape of a
Cantor/perfect-set geometric supply: each side returns a nonempty perfect set in the common-component
closure, with one fixed omitted-ray direction on that set. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffPerfectLocalRayConfinedSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hsel₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ Perfect S ∧ S.Nonempty ∧
        S ⊆ frontier (filledJulia c₁) ∧
        S ⊆ (filledJulia c₂)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₁ v z)
    (hsel₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (v : ℂ) (S : Set ℂ), ‖v‖ = 1 ∧ Perfect S ∧ S.Nonempty ∧
        S ⊆ frontier (filledJulia c₂) ∧
        S ⊆ (filledJulia c₁)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ∀ z ∈ S, LocalRayConfined c₂ v z) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalRayConfinedSelector
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc hβ₁mod
    hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, S, hv, hSperf, hSne, hSfront, hSoff, hScl, hSray⟩ :=
      hsel₁ p u huU hpfront hpoff hpcl
    exact ⟨v, S, hv, not_countable_of_perfect_nonempty hSperf hSne,
      hSfront, hSoff, hScl, hSray⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, S, hv, hSperf, hSne, hSfront, hSoff, hScl, hSray⟩ :=
      hsel₂ p u huU hpfront hpoff hpcl
    exact ⟨v, S, hv, not_countable_of_perfect_nonempty hSperf hSne,
      hSfront, hSoff, hScl, hSray⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from radical squarefree algebra plus common-component local-tip targets.**  This is the
same endpoint as the rotated-slit local-tip theorem, but with the local preconnectedness supplied
directly instead of being derived from a slit model. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentLocalTipSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (S : Set ℂ)
    (havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T)
    (hcomponent : ∃ u ∈ U,
      ∀ z₀ ∈ S, z₀ ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hgeom : ∀ z₀ ∈ S,
      z₀ ∈ filledJulia c₁ ∧
      z₀ ∈ (filledJulia c₂)ᶜ ∧
      ∃ rTip : ℝ, 0 < rTip ∧
        ∀ ρ, 0 < ρ → ρ ≤ rTip →
          IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_normalized_countableAvoidance_commonComponentLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch ?_
  intro Q s hnt hEqOn
  obtain ⟨Q', s', N, B, hnt', hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn
  obtain ⟨w, _hwU, hwoff₂, hBne⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγmatch hB0
  obtain ⟨hleadw, hsepw⟩ := hBgood w hBne
  refine ⟨Q', s', N, (filledJulia c₂)ᶜ, w, S, hnt', hEqOn', hsupp, hN, hN1,
    isPreconnected_compl_filledJulia c₂, ?_, hwoff₂, hleadw, hsepw, ?_, hcomponent, ?_⟩
  · intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγan₂ (Q' i)
  · intro T hT
    obtain ⟨z₀, hzS, hzoff, hznot⟩ := havoid T hT
    exact ⟨z₀, hzS, hzoff, hznot⟩
  · intro z₀ hzS
    exact hgeom z₀ hzS

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from symmetric perfect local-tip selectors.**  This is the weakest selector endpoint in
this chain: the geometric construction only has to produce a nonempty perfect common-component closure
set of local preconnected basin tips on the relevant side of the symmetric difference. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffPerfectLocalTipSelector
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneSymm : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneSymm hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneSymm hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (htip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ S : Set ℂ, Perfect S ∧ S.Nonempty ∧
        S ⊆ frontier (filledJulia c₁) ∧
        S ⊆ (filledJulia c₂)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ∀ z ∈ S, ∃ rTip : ℝ, 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            IsPreconnected (Metric.ball z ρ ∩ (filledJulia c₁)ᶜ))
    (htip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ S : Set ℂ, Perfect S ∧ S.Nonempty ∧
        S ⊆ frontier (filledJulia c₂) ∧
        S ⊆ (filledJulia c₁)ᶜ ∧
        S ⊆ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ∀ z ∈ S, ∃ rTip : ℝ, 0 < rTip ∧
          ∀ ρ, 0 < ρ → ρ ≤ rTip →
            IsPreconnected (Metric.ball z ρ ∩ (filledJulia c₂)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneSymm
    letI := (ratfuncToMero U hUo hUc hUneSymm hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneSymm
  letI := (ratfuncToMero U hUo hUc hUneSymm hUinf).toAlgebra
  have hβ₁match : ∀ z ∈ U, β₁ z = bottcherCoord c₁ z := fun z hz => hβ₁esc z (hU₁ hz)
  have hβ₂match : ∀ z ∈ U, β₂ z = bottcherCoord c₂ z := fun z hz => hβ₂esc z (hU₂ hz)
  obtain ⟨x, hx | hx⟩ := exists_point_filledJulia_symmDiff hne
  · obtain ⟨u, huU⟩ := hUneSymm
    have huC : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
      ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
        escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
    obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
      exists_frontier_off_other_in_closure_common_component
        (a := c₁) (b := c₂) (u := u) (x := x) huC hx.1 hx.2
    obtain ⟨S, hSperf, hSne, hSfront, hSoff, hScl, hStip⟩ :=
      htip₁ p u huU hpfront hpoff₂ hpcl
    have havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T := by
      intro T hT
      by_contra hnone
      push Not at hnone
      have hSsubT : S ⊆ T := by
        intro z hzS
        exact hnone z hzS (hSoff hzS)
      exact (not_countable_of_perfect_nonempty hSperf hSne) (hT.mono hSsubT)
    exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentLocalTipSelector
      (U := U) hUo hUc ⟨u, huU⟩ hUinf c₁ c₂ hU₁ hU₂ hG₂ β₁ β₂ hβ₁an hβ₁esc
      hβ₁mod hempty₁
      hβ₂an hβ₂match S havoid ⟨u, huU, hScl⟩ (by
        intro z hzS
        exact ⟨mem_filledJulia_of_frontier (hSfront hzS), hSoff hzS, hStip z hzS⟩)
  · obtain ⟨u, huU⟩ := hUneSymm
    have huC : u ∈ (filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ :=
      ⟨escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU),
        escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU)⟩
    obtain ⟨p, hpfront, hpoff₁, hpcl⟩ :=
      exists_frontier_off_other_in_closure_common_component
        (a := c₂) (b := c₁) (u := u) (x := x) huC hx.1 hx.2
    obtain ⟨S, hSperf, hSne, hSfront, hSoff, hScl, hStip⟩ :=
      htip₂ p u huU hpfront hpoff₁ hpcl
    have havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₁)ᶜ ∧ z₀ ∉ T := by
      intro T hT
      by_contra hnone
      push Not at hnone
      have hSsubT : S ⊆ T := by
        intro z hzS
        exact hnone z hzS (hSoff hzS)
      exact (not_countable_of_perfect_nonempty hSperf hSne) (hT.mono hSsubT)
    have hswap : NoRelation (RatFunc ℂ) (phiMero c₂ hU₂) (phiMero c₁ hU₁) :=
      noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentLocalTipSelector
        (U := U) hUo hUc ⟨u, huU⟩ hUinf c₂ c₁ hU₂ hU₁ hG₁ β₂ β₁ hβ₂an hβ₂esc
        hβ₂mod hempty₂
        hβ₁an hβ₁match S havoid ⟨u, huU, hScl⟩ (by
          intro z hzS
          exact ⟨mem_filledJulia_of_frontier (hSfront hzS), hSoff hzS, hStip z hzS⟩)
    exact noRelation_symm hswap

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A point is local-tip-good for `K_c` if the punctured basin is locally preconnected below some
positive radius. -/
def LocalTipGood (c z : ℂ) : Prop :=
  ∃ rTip : ℝ, 0 < rTip ∧
    ∀ ρ, 0 < ρ → ρ ≤ rTip →
      IsPreconnected (Metric.ball z ρ ∩ (filledJulia c)ᶜ)

lemma localTipGood_of_localRayConfined {c v z : ℂ} (hv : ‖v‖ = 1)
    (h : LocalRayConfined c v z) : LocalTipGood c z := by
  rcases fixedRotatedSlitGood_of_localRayConfined hv h with ⟨_hv, rTip, hrTip, hslit⟩
  exact ⟨rTip, hrTip,
    local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
      (K := filledJulia c) (u := v) (z₀ := z) (R := rTip) hv hslit⟩

/-- **NoRelation from noncountability of the local-tip-good frontier locus.**  This is the Baire-style
endpoint: the remaining geometry only has to show that bad non-tip points do not exhaust the
noncountable common-component closure slice. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipGoodLocus
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneLocalTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hgood₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              LocalTipGood c₁ z} : Set ℂ).Countable)
    (hgood₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              LocalTipGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneLocalTip
    letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneLocalTip
  letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
  have hβ₁match : ∀ z ∈ U, β₁ z = bottcherCoord c₁ z := fun z hz => hβ₁esc z (hU₁ hz)
  have hβ₂match : ∀ z ∈ U, β₂ z = bottcherCoord c₂ z := fun z hz => hβ₂esc z (hU₂ hz)
  obtain ⟨x, hx | hx⟩ := exists_point_filledJulia_symmDiff hne
  · obtain ⟨u, huU⟩ := hUneLocalTip
    have huC : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
      ⟨escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU),
        escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU)⟩
    obtain ⟨p, hpfront, hpoff₂, hpcl⟩ :=
      exists_frontier_off_other_in_closure_common_component
        (a := c₁) (b := c₂) (u := u) (x := x) huC hx.1 hx.2
    let S : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              LocalTipGood c₁ z}
    have hSunc : ¬ S.Countable := by
      simpa [S] using hgood₁ p u huU hpfront hpoff₂ hpcl
    have havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₂)ᶜ ∧ z₀ ∉ T := by
      intro T hT
      by_contra hnone
      push Not at hnone
      have hSsubT : S ⊆ T := by
        intro z hzS
        exact hnone z hzS hzS.2.1
      exact hSunc (hT.mono hSsubT)
    exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentLocalTipSelector
      (U := U) hUo hUc ⟨u, huU⟩ hUinf c₁ c₂ hU₁ hU₂ hG₂ β₁ β₂ hβ₁an hβ₁esc
      hβ₁mod hempty₁ hβ₂an hβ₂match S havoid ⟨u, huU, by intro z hzS; exact hzS.2.2.1⟩
      (by
        intro z hzS
        exact ⟨mem_filledJulia_of_frontier hzS.1, hzS.2.1, hzS.2.2.2⟩)
  · obtain ⟨u, huU⟩ := hUneLocalTip
    have huC : u ∈ (filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ :=
      ⟨escapeOpen_subset_compl_filledJulia c₂ (hU₂ huU),
        escapeOpen_subset_compl_filledJulia c₁ (hU₁ huU)⟩
    obtain ⟨p, hpfront, hpoff₁, hpcl⟩ :=
      exists_frontier_off_other_in_closure_common_component
        (a := c₂) (b := c₁) (u := u) (x := x) huC hx.1 hx.2
    let S : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              LocalTipGood c₂ z}
    have hSunc : ¬ S.Countable := by
      simpa [S] using hgood₂ p u huU hpfront hpoff₁ hpcl
    have havoid : ∀ T : Set ℂ, T.Countable → ∃ z₀ ∈ S, z₀ ∈ (filledJulia c₁)ᶜ ∧ z₀ ∉ T := by
      intro T hT
      by_contra hnone
      push Not at hnone
      have hSsubT : S ⊆ T := by
        intro z hzS
        exact hnone z hzS hzS.2.1
      exact hSunc (hT.mono hSsubT)
    have hswap : NoRelation (RatFunc ℂ) (phiMero c₂ hU₂) (phiMero c₁ hU₁) :=
      noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_commonComponentLocalTipSelector
        (U := U) hUo hUc ⟨u, huU⟩ hUinf c₂ c₁ hU₂ hU₁ hG₁ β₂ β₁ hβ₂an hβ₂esc
        hβ₂mod hempty₂ hβ₁an hβ₁match S havoid ⟨u, huU, by intro z hzS; exact hzS.2.2.1⟩
        (by
          intro z hzS
          exact ⟨mem_filledJulia_of_frontier hzS.1, hzS.2.1, hzS.2.2.2⟩)
    exact noRelation_symm hswap

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a noncountable closure slice with countably many non-tip points.**  This is the
Baire/countable-bad form of the local-tip endpoint. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBadCountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneLocalTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hslice₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} : Set ℂ).Countable)
    (hbad₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              ¬ LocalTipGood c₁ z} : Set ℂ).Countable)
    (hslice₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ¬ ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)} : Set ℂ).Countable)
    (hbad₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              ¬ LocalTipGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneLocalTip
    letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneLocalTip
  letI := (ratfuncToMero U hUo hUc hUneLocalTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipGoodLocus
    hUo hUc hUneLocalTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    let Slice : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)}
    let Good : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              LocalTipGood c₁ z}
    let Bad : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              ¬ LocalTipGood c₁ z}
    intro hGood
    have hBad : Bad.Countable := by
      simpa [Bad] using hbad₁ p u huU hpfront hpoff hpcl
    have hSlice : Slice.Countable := by
      have hsub : Slice ⊆ Good ∪ Bad := by
        intro z hz
        by_cases htip : LocalTipGood c₁ z
        · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2, htip⟩
        · exact Or.inr ⟨hz.1, hz.2.1, hz.2.2, htip⟩
      exact (hGood.union hBad).mono hsub
    exact (hslice₁ p u huU hpfront hpoff hpcl) (by simpa [Slice] using hSlice)
  · intro p u huU hpfront hpoff hpcl
    let Slice : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)}
    let Good : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              LocalTipGood c₂ z}
    let Bad : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              ¬ LocalTipGood c₂ z}
    intro hGood
    have hBad : Bad.Countable := by
      simpa [Bad] using hbad₂ p u huU hpfront hpoff hpcl
    have hSlice : Slice.Countable := by
      have hsub : Slice ⊆ Good ∪ Bad := by
        intro z hz
        by_cases htip : LocalTipGood c₂ z
        · exact Or.inl ⟨hz.1, hz.2.1, hz.2.2, htip⟩
        · exact Or.inr ⟨hz.1, hz.2.1, hz.2.2, htip⟩
      exact (hGood.union hBad).mono hsub
    exact (hslice₂ p u huU hpfront hpoff hpcl) (by simpa [Slice] using hSlice)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A local tip at the base common-component closure point forces a noncountable frontier/off-other
slice in the closure of that same common-basin component. -/
theorem not_countable_commonComponent_closure_slice_of_localTip
    {c₁ c₂ p u : ℂ}
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (_huU : u ∈ U)
    (hpfront : p ∈ frontier (filledJulia c₁))
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (htip : LocalTipGood c₁ p) :
    ¬ ({z | z ∈ frontier (filledJulia c₁) ∧
            z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} : Set ℂ).Countable := by
  rcases htip with ⟨rTip, hrTip, htip⟩
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCo : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  set r : ℝ := min rTip rOther with hrdef
  have hr : 0 < r := by rw [hrdef]; exact lt_min hrTip hrOther
  have hr_le_tip : r ≤ rTip := by rw [hrdef]; exact min_le_left _ _
  have hr_le_other : r ≤ rOther := by rw [hrdef]; exact min_le_right _ _
  have hsectorV : Metric.ball p r ∩ (filledJulia c₁)ᶜ ⊆ V := by
    set W : Set ℂ := Metric.ball p r ∩ (filledJulia c₁)ᶜ with hW
    have hWc : IsPreconnected W := by simpa [W] using htip r hr hr_le_tip
    have hWC : W ⊆ C := by
      intro z hz
      exact ⟨hz.2, hother (Metric.ball_subset_ball hr_le_other hz.1)⟩
    have hpclV : p ∈ closure V := by simpa [V, C] using hpcl
    have hmeet : (Metric.ball p r ∩ V).Nonempty := by
      rw [_root_.mem_closure_iff] at hpclV
      exact hpclV (Metric.ball p r) isOpen_ball (Metric.mem_ball_self hr)
    obtain ⟨y, hyball, hyV⟩ := hmeet
    have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
    have hWsubCompY : W ⊆ connectedComponentIn C y :=
      hWc.subset_connectedComponentIn hyW hWC
    have hcomp : connectedComponentIn C y = V := by
      have h := connectedComponentIn_eq (by simpa [V] using hyV)
      simpa [V] using h.symm
    intro z hz
    exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
  have hpΩ : p ∈ interior ((filledJulia c₂)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff)
  obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
    exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
      (U := V) (Ω := (filledJulia c₂)ᶜ) (c₁ := c₁) (c₂ := c₂)
      hKconn hempty (mem_filledJulia_of_frontier hpfront) hpΩ hr hrOther hsectorV hother
  intro hcount
  obtain ⟨z, hzS, _hzΩ, hznot⟩ := havoid
    ({z | z ∈ frontier (filledJulia c₁) ∧
            z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} : Set ℂ) hcount
  obtain ⟨_hzball, hzfront, hzoff⟩ := hSlocal z hzS
  have hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
    simpa [V, C] using hclosure z hzS
  exact hznot ⟨hzfront, hzoff, hzcl⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from base local tips plus countably many non-tip points.**  The previous
`LocalTipBadCountable` endpoint needs noncountability of the whole common-component closure slice.
This wrapper obtains that noncountability from local-tip-goodness of the base closure point itself;
the remaining geometric input is only that the non-tip locus inside each such slice is countable. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipBadCountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (hbad₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ({z | z ∈ frontier (filledJulia c₁) ∧
              z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
              ¬ LocalTipGood c₁ z} : Set ℂ).Countable)
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (hbad₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ({z | z ∈ frontier (filledJulia c₂) ∧
              z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
              ¬ LocalTipGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBadCountable
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ hbad₁ ?_ hbad₂
  · intro p u huU hpfront hpoff hpcl
    exact not_countable_commonComponent_closure_slice_of_localTip
      (U := U) (c₁ := c₁) (c₂ := c₂) (p := p) (u := u)
      hKconn₁ hempty₁ huU hpfront hpoff hpcl (hbaseTip₁ p u huU hpfront hpoff hpcl)
  · intro p u huU hpfront hpoff hpcl
    exact not_countable_commonComponent_closure_slice_of_localTip
      (U := U) (c₁ := c₂) (c₂ := c₁) (p := p) (u := u)
      hKconn₂ hempty₂ huU hpfront hpoff hpcl (hbaseTip₂ p u huU hpfront hpoff hpcl)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from base local tips plus globally countable non-tip loci.**  This is the component-free
version of the countable-bad endpoint: it is enough to count non-local-tip points globally on the
off-other frontier. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipGlobalBadCountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (hglobalBad₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ).Countable)
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (hglobalBad₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipBadCountable
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseTip₁ ?_
    hbaseTip₂ ?_
  · intro p u huU hpfront hpoff hpcl
    exact hglobalBad₁.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.2⟩)
  · intro p u huU hpfront hpoff hpcl
    exact hglobalBad₂.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, hz.2.2.2⟩)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma countable_of_subset_iUnion_finite {ι : Type*} [Countable ι] {S : Set ℂ} {F : ι → Set ℂ}
    (hcover : S ⊆ ⋃ i, F i) (hfinite : ∀ i, (F i).Finite) : S.Countable := by
  exact (Set.countable_iUnion (fun i => (hfinite i).countable)).mono hcover

/-- **NoRelation from base local tips plus componentwise finite bad-tip covers.**  This is the
component-index form of the Grok crossing lead: if the global non-tip loci are covered by a countable
family of finite component-bad sets, then they are countable, and the global-bad endpoint applies. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipFiniteBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hfinite₁ : ∀ i, (F₁ i).Finite)
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hfinite₂ : ∀ i, (F₂ i).Finite) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipGlobalBadCountable
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseTip₁ ?_
    hbaseTip₂ ?_
  · exact countable_of_subset_iUnion_finite hcover₁ hfinite₁
  · exact countable_of_subset_iUnion_finite hcover₂ hfinite₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma localTipGood_of_rotatedSlitGood {c z : ℂ}
    (h : RotatedSlitGood c z) : LocalTipGood c z := by
  rcases h with ⟨v, rTip, hv, hrTip, hslit⟩
  exact ⟨rTip, hrTip,
    local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
      (K := filledJulia c) (u := v) (z₀ := z) (R := rTip) hv hslit⟩

lemma localTipGood_of_fixedRotatedSlitGood {c v z : ℂ}
    (h : FixedRotatedSlitGood c v z) : LocalTipGood c z := by
  exact localTipGood_of_rotatedSlitGood (rotatedSlitGood_of_fixedRotatedSlitGood h)

/-- **NoRelation from base rotated slits plus componentwise finite bad-tip covers.**
This is the same finite-bad-cover endpoint as the local-tip version, with the base-goodness input
pushed down to the concrete rotated-slit witness supplied at the base closure point. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseRotatedSlitFiniteBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseSlit₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      RotatedSlitGood c₁ p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hfinite₁ : ∀ i, (F₁ i).Finite)
    (hbaseSlit₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      RotatedSlitGood c₂ p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hfinite₂ : ∀ i, (F₂ i).Finite) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipFiniteBadCover
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ F₁ hcover₁
    hfinite₁ ?_ F₂ hcover₂ hfinite₂
  · intro p u huU hpfront hpoff hpcl
    exact localTipGood_of_rotatedSlitGood (hbaseSlit₁ p u huU hpfront hpoff hpcl)
  · intro p u huU hpfront hpoff hpcl
    exact localTipGood_of_rotatedSlitGood (hbaseSlit₂ p u huU hpfront hpoff hpcl)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A one-radius rotated slit sector in the basin.  This is the Lean-facing shape of the
prime-end/crosscut stabilization lead: once a single sufficiently small half-plane sector is known to
avoid `K_c`, the all-smaller-radius `RotatedSlitGood` interface follows by monotonicity of balls. -/
def RotatedSlitRadiusGood (c z : ℂ) : Prop :=
  ∃ (v : ℂ) (r : ℝ), ‖v‖ = 1 ∧ 0 < r ∧
    Metric.ball z r ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆ (filledJulia c)ᶜ

lemma rotatedSlitGood_of_rotatedSlitRadiusGood {c z : ℂ}
    (h : RotatedSlitRadiusGood c z) : RotatedSlitGood c z := by
  rcases h with ⟨v, r, hv, hr, hsector⟩
  refine ⟨v, r, hv, hr, ?_⟩
  intro ρ hρ hρle w hw
  exact ⟨hw.1, hsector ⟨Metric.ball_subset_ball hρle hw.1, hw.2⟩⟩

/-- **NoRelation from one-radius base rotated slits plus componentwise finite bad-tip covers.**
This packages the crosscut/equipotential-sector lead: the base geometry only has to produce one
stable slit sector at each relevant closure point, not the quantified all-radius form. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseRotatedSlitRadiusFiniteBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseSector : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseSector₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      RotatedSlitRadiusGood c₁ p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hfinite₁ : ∀ i, (F₁ i).Finite)
    (hbaseSector₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      RotatedSlitRadiusGood c₂ p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hfinite₂ : ∀ i, (F₂ i).Finite) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseSector
    letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseSector
  letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseRotatedSlitFiniteBadCover
    hUo hUc hUneBaseSector hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ F₁ hcover₁
    hfinite₁ ?_ F₂ hcover₂ hfinite₂
  · intro p u huU hpfront hpoff hpcl
    exact rotatedSlitGood_of_rotatedSlitRadiusGood (hbaseSector₁ p u huU hpfront hpoff hpcl)
  · intro p u huU hpfront hpoff hpcl
    exact rotatedSlitGood_of_rotatedSlitRadiusGood (hbaseSector₂ p u huU hpfront hpoff hpcl)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma countable_of_subset_iUnion_countable {ι : Type*} [Countable ι] {S : Set ℂ} {F : ι → Set ℂ}
    (hcover : S ⊆ ⋃ i, F i) (hcount : ∀ i, (F i).Countable) : S.Countable := by
  exact (Set.countable_iUnion hcount).mono hcover

/-- **NoRelation from one-radius base sectors plus countable bad-tip portrait covers.**
This is the countable-prime-end/portrait version of the finite-bad-cover endpoint: each portrait class
may itself be countable, as long as there are only countably many classes. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseRotatedSlitRadiusCountableBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseSector : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseSector₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      RotatedSlitRadiusGood c₁ p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hbaseSector₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      RotatedSlitRadiusGood c₂ p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseSector
    letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseSector
  letI := (ratfuncToMero U hUo hUc hUneBaseSector hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipGlobalBadCountable
    hUo hUc hUneBaseSector hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ ?_ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    exact localTipGood_of_rotatedSlitGood
      (rotatedSlitGood_of_rotatedSlitRadiusGood (hbaseSector₁ p u huU hpfront hpoff hpcl))
  · exact countable_of_subset_iUnion_countable hcover₁ hcount₁
  · intro p u huU hpfront hpoff hpcl
    exact localTipGood_of_rotatedSlitGood
      (rotatedSlitGood_of_rotatedSlitRadiusGood (hbaseSector₂ p u huU hpfront hpoff hpcl))
  · exact countable_of_subset_iUnion_countable hcover₂ hcount₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma rotatedSlitRadiusGood_of_localRayConfined {c v z : ℂ} (hv : ‖v‖ = 1)
    (h : LocalRayConfined c v z) : RotatedSlitRadiusGood c z := by
  rcases h with ⟨rTip, hrTip, hray⟩
  refine ⟨v, rTip, hv, hrTip, ?_⟩
  intro w hw hwK
  exact hray w hw.1 hwK hw.2

/-- **NoRelation from base local-ray confinement plus countable bad-tip portrait covers.**
This is the Moore/simple-dendrite-tip version of the current endpoint: at each base closure point,
it is enough to trap the local filled Julia set in one omitted ray, while the non-tip locus is handled
by countably many countable portrait classes. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalRayConfinedCountableBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseRay : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseRay₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalRayConfined c₁ v p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hbaseRay₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalRayConfined c₂ v p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
    letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
  letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseRotatedSlitRadiusCountableBadCover
    hUo hUc hUneBaseRay hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ F₁ hcover₁
    hcount₁ ?_ F₂ hcover₂ hcount₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hray⟩ := hbaseRay₁ p u huU hpfront hpoff hpcl
    exact rotatedSlitRadiusGood_of_localRayConfined hv hray
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hray⟩ := hbaseRay₂ p u huU hpfront hpoff hpcl
    exact rotatedSlitRadiusGood_of_localRayConfined hv hray

end Bottcher

namespace Bottcher

lemma rotatedSlitRadiusGood_iff_exists_localRayConfined {c z : ℂ} :
    RotatedSlitRadiusGood c z ↔ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalRayConfined c v z := by
  constructor
  · intro h
    rcases h with ⟨v, r, hv, hr, hsector⟩
    refine ⟨v, hv, r, hr, ?_⟩
    intro w hwball hwK hwslit
    exact hsector ⟨hwball, hwslit⟩ hwK
  · intro h
    rcases h with ⟨v, hv, hray⟩
    exact rotatedSlitRadiusGood_of_localRayConfined hv hray

end Bottcher

namespace Bottcher

/-- Local confinement to the explicit rotated nonpositive real ray based at `z`. -/
def LocalNonpositiveRayConfined (c v z : ℂ) : Prop :=
  ∃ rTip : ℝ, 0 < rTip ∧
    ∀ w, w ∈ Metric.ball z rTip → w ∈ filledJulia c →
      ∃ t : ℝ, t ≤ 0 ∧ v * (w - z) = (t : ℂ)

lemma exists_nonpos_real_of_not_mem_slitPlane {z : ℂ} (hz : z ∉ Complex.slitPlane) :
    ∃ t : ℝ, t ≤ 0 ∧ z = (t : ℂ) := by
  rw [Complex.mem_slitPlane_iff] at hz
  push Not at hz
  refine ⟨z.re, hz.1, ?_⟩
  apply Complex.ext <;> simp [hz.2]

lemma localRayConfined_of_localNonpositiveRayConfined {c v z : ℂ}
    (h : LocalNonpositiveRayConfined c v z) : LocalRayConfined c v z := by
  rcases h with ⟨rTip, hrTip, hray⟩
  refine ⟨rTip, hrTip, ?_⟩
  intro w hwball hwK hwslit
  obtain ⟨t, ht, hwt⟩ := hray w hwball hwK
  have hnot : ((t : ℂ) ∉ Complex.slitPlane) := by
    rw [Complex.mem_slitPlane_iff]
    push Not
    exact ⟨ht, by simp⟩
  exact hnot (by simpa [hwt] using hwslit)

lemma localNonpositiveRayConfined_of_localRayConfined {c v z : ℂ}
    (h : LocalRayConfined c v z) : LocalNonpositiveRayConfined c v z := by
  rcases h with ⟨rTip, hrTip, hray⟩
  refine ⟨rTip, hrTip, ?_⟩
  intro w hwball hwK
  obtain ⟨t, ht, hwt⟩ := exists_nonpos_real_of_not_mem_slitPlane (hray w hwball hwK)
  exact ⟨t, ht, hwt⟩

lemma localRayConfined_iff_localNonpositiveRayConfined {c v z : ℂ} :
    LocalRayConfined c v z ↔ LocalNonpositiveRayConfined c v z := by
  constructor
  · exact localNonpositiveRayConfined_of_localRayConfined
  · exact localRayConfined_of_localNonpositiveRayConfined

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from base explicit nonpositive-ray confinement plus countable bad-tip portrait covers.**
This is the most literal Lean surface for the Moore-singleton / external-ray-collapse / one-arm-tip
lead: each base closure point supplies a rotated nonpositive real ray containing the local filled Julia
set, and the remaining non-tip failures are countably portrait-covered. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseNonpositiveRayConfinedCountableBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseRay : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseRay₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    (F₁ : ι₁ → Set ℂ)
    (hcover₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ LocalTipGood c₁ z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hbaseRay₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p)
    (F₂ : ι₂ → Set ℂ)
    (hcover₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ LocalTipGood c₂ z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
    letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
  letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalRayConfinedCountableBadCover
    hUo hUc hUneBaseRay hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ F₁ hcover₁
    hcount₁ ?_ F₂ hcover₂ hcount₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hray⟩ := hbaseRay₁ p u huU hpfront hpoff hpcl
    exact ⟨v, hv, localRayConfined_of_localNonpositiveRayConfined hray⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨v, hv, hray⟩ := hbaseRay₂ p u huU hpfront hpoff hpcl
    exact ⟨v, hv, localRayConfined_of_localNonpositiveRayConfined hray⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma localTipGood_of_localNonpositiveRayConfined {c v z : ℂ} (hv : ‖v‖ = 1)
    (h : LocalNonpositiveRayConfined c v z) : LocalTipGood c z := by
  exact localTipGood_of_localRayConfined hv (localRayConfined_of_localNonpositiveRayConfined h)

lemma not_exists_localNonpositiveRayConfined_of_not_localTipGood {c z : ℂ}
    (hbad : ¬ LocalTipGood c z) : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c v z := by
  intro h
  rcases h with ⟨v, hv, hray⟩
  exact hbad (localTipGood_of_localNonpositiveRayConfined hv hray)

/-- **NoRelation from base explicit rays plus countable non-ray-confined portrait covers.**
This aligns the bad-set input with the Moore-singleton lead: it is enough to count frontier points that
fail to be locally confined to any rotated nonpositive ray. Lean turns that into the required non-tip
cover because local ray confinement implies `LocalTipGood`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseNonpositiveRayConfinedMooreBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseRay : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseRay₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    (F₁ : ι₁ → Set ℂ)
    (hcoverRayBad₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hbaseRay₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p)
    (F₂ : ι₂ → Set ℂ)
    (hcoverRayBad₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
    letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseRay
  letI := (ratfuncToMero U hUo hUc hUneBaseRay hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseNonpositiveRayConfinedCountableBadCover
    hUo hUc hUneBaseRay hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseRay₁ F₁ ?_
    hcount₁ hbaseRay₂ F₂ ?_ hcount₂
  · intro z hz
    exact hcoverRayBad₁ ⟨hz.1, hz.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hz.2.2⟩
  · intro z hz
    exact hcoverRayBad₂ ⟨hz.1, hz.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hz.2.2⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a Moore-style singleton/non-singleton dichotomy plus countable non-ray portraits.**
For each base common-component closure point, the geometric input may choose either branch:
* singleton/one-arm branch: the base point is locally confined to a rotated nonpositive ray;
* non-singleton branch: the frontier/off-other slice in that same component closure is already
  noncountable.
The bad-set input counts only failures of local nonpositive-ray confinement; Lean converts that to the
`¬ LocalTipGood` count needed by the countable-avoidance algebra. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreDichotomyBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ¬ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} : Set ℂ).Countable)
    (F₁ : ι₁ → Set ℂ)
    (hcoverRayBad₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ¬ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
              z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)} : Set ℂ).Countable)
    (F₂ : ι₂ → Set ℂ)
    (hcoverRayBad₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  have hglobalBad₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ).Countable :=
    countable_of_subset_iUnion_countable hcoverRayBad₁ hcount₁
  have hglobalBad₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ).Countable :=
    countable_of_subset_iUnion_countable hcoverRayBad₂ hcount₂
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBadCountable
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hbaseRay | hunc
    · rcases hbaseRay with ⟨v, hv, hray⟩
      exact not_countable_commonComponent_closure_slice_of_localTip
        (U := U) (c₁ := c₁) (c₂ := c₂) (p := p) (u := u)
        hKconn₁ hempty₁ huU hpfront hpoff hpcl
        (localTipGood_of_localNonpositiveRayConfined hv hray)
    · exact hunc
  · intro p u huU hpfront hpoff hpcl
    exact hglobalBad₁.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hz.2.2.2⟩)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hbaseRay | hunc
    · rcases hbaseRay with ⟨v, hv, hray⟩
      exact not_countable_commonComponent_closure_slice_of_localTip
        (U := U) (c₁ := c₂) (c₂ := c₁) (p := p) (u := u)
        hKconn₂ hempty₂ huU hpfront hpoff hpcl
        (localTipGood_of_localNonpositiveRayConfined hv hray)
    · exact hunc
  · intro p u huU hpfront hpoff hpcl
    exact hglobalBad₂.mono (by
      intro z hz
      exact ⟨hz.1, hz.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hz.2.2.2⟩)

end Bottcher

namespace Bottcher

open MeasureTheory
open scoped ENNReal

lemma not_countable_Icc_real_of_lt {a b : ℝ} (hab : a < b) : ¬ (Set.Icc a b).Countable := by
  intro hcnt
  have hzero : volume (Set.Icc a b) = 0 := hcnt.measure_zero volume
  rw [Real.volume_Icc] at hzero
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (b - a) := by
    rw [ENNReal.ofReal_pos]
    linarith
  exact (ne_of_gt hpos) hzero

/-- A nondegenerate preconnected subset of the complex plane is noncountable.  This is the reusable
continuum atom for the Moore-fiber branch: once a non-singleton impression/fiber sits inside the
frontier slice, that slice is automatically noncountable. -/
lemma not_countable_of_isPreconnected_nontrivial_complex {S : Set ℂ}
    (hS : IsPreconnected S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) (hne : a ≠ b) :
    ¬ S.Countable := by
  intro hcnt
  by_cases hre : a.re = b.re
  · have him_ne : a.im ≠ b.im := by
      intro him
      exact hne (Complex.ext hre him)
    rcases lt_or_gt_of_ne him_ne with him_lt | him_gt
    · have hI : Set.Icc a.im b.im ⊆ Complex.im '' S := by
        simpa using hS.intermediate_value ha hb (Complex.continuous_im.continuousOn)
      exact not_countable_Icc_real_of_lt him_lt ((hcnt.image Complex.im).mono hI)
    · have hI : Set.Icc b.im a.im ⊆ Complex.im '' S := by
        have hIV := hS.intermediate_value hb ha (Complex.continuous_im.continuousOn)
        simpa using hIV
      exact not_countable_Icc_real_of_lt him_gt ((hcnt.image Complex.im).mono hI)
  · rcases lt_or_gt_of_ne hre with hre_lt | hre_gt
    · have hI : Set.Icc a.re b.re ⊆ Complex.re '' S := by
        simpa using hS.intermediate_value ha hb (Complex.continuous_re.continuousOn)
      exact not_countable_Icc_real_of_lt hre_lt ((hcnt.image Complex.re).mono hI)
    · have hI : Set.Icc b.re a.re ⊆ Complex.re '' S := by
        have hIV := hS.intermediate_value hb ha (Complex.continuous_re.continuousOn)
        simpa using hIV
      exact not_countable_Icc_real_of_lt hre_gt ((hcnt.image Complex.re).mono hI)

lemma not_countable_of_preconnected_nontrivial_subset {S F : Set ℂ}
    (hsub : F ⊆ S) (hF : IsPreconnected F) {a b : ℂ}
    (ha : a ∈ F) (hb : b ∈ F) (hne : a ≠ b) : ¬ S.Countable := by
  intro hS
  exact not_countable_of_isPreconnected_nontrivial_complex hF ha hb hne (hS.mono hsub)

lemma not_countable_commonComponent_slice_of_preconnected_nontrivial_subset
    {c₁ c₂ u : ℂ} {F : Set ℂ}
    (hsub : F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (hF : IsPreconnected F) {a b : ℂ} (ha : a ∈ F) (hb : b ∈ F) (hne : a ≠ b) :
    ¬ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} : Set ℂ).Countable := by
  exact not_countable_of_preconnected_nontrivial_subset hsub hF ha hb hne

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a Moore-fiber witness dichotomy plus countable non-ray portraits.**
This is the Lean-facing version of Grok's nondegenerate-impression route: in the non-singleton branch,
the caller only has to provide a nontrivial preconnected fiber/continuum contained in the relevant
frontier/off-other/component-closure slice. Lean proves that this branch is noncountable. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (F₁ : ι₁ → Set ℂ)
    (hcoverRayBad₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ) ⊆ ⋃ i, F₁ i)
    (hcount₁ : ∀ i, (F₁ i).Countable)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)})
    (F₂ : ι₂ → Set ℂ)
    (hcoverRayBad₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ) ⊆ ⋃ i, F₂ i)
    (hcount₂ : ∀ i, (F₂ i).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreDichotomyBadCover
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ F₁ hcoverRayBad₁
    hcount₁ ?_ F₂ hcoverRayBad₂ hcount₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hbase | hfiber
    · exact Or.inl hbase
    · rcases hfiber with ⟨F, hFconn, hFnontriv, hFsub⟩
      rcases hFnontriv with ⟨a, ha, b, hb, hneab⟩
      exact Or.inr (not_countable_commonComponent_slice_of_preconnected_nontrivial_subset
        (c₁ := c₁) (c₂ := c₂) (u := u) hFsub hFconn ha hb hneab)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hbase | hfiber
    · exact Or.inl hbase
    · rcases hfiber with ⟨F, hFconn, hFnontriv, hFsub⟩
      rcases hFnontriv with ⟨a, ha, b, hb, hneab⟩
      exact Or.inr (not_countable_commonComponent_slice_of_preconnected_nontrivial_subset
        (c₁ := c₂) (c₂ := c₁) (u := u) hFsub hFconn ha hb hneab)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma countable_of_subset_iUnion_subsingleton {ι : Type*} [Countable ι] {S : Set ℂ} {F : ι → Set ℂ}
    (hcover : S ⊆ ⋃ i, F i) (hsubsingle : ∀ i, (F i).Subsingleton) : S.Countable := by
  exact countable_of_subset_iUnion_countable hcover (fun i => (hsubsingle i).countable)

/-- **NoRelation from Moore-fiber dichotomy plus singleton-coded bad portraits.**
This is the dyadic/rational-code form suggested by the portrait leads: the bad non-ray-confined locus
is covered by countably many code classes, and each code class selects at most one frontier point. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomySingletonCodeBadCover
    {ι₁ ι₂ : Type*} [Countable ι₁] [Countable ι₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (CodeClass₁ : ι₁ → Set ℂ)
    (hcoverCode₁ : ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ) ⊆ ⋃ i, CodeClass₁ i)
    (hcodeSubsingle₁ : ∀ i, (CodeClass₁ i).Subsingleton)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)})
    (CodeClass₂ : ι₂ → Set ℂ)
    (hcoverCode₂ : ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ) ⊆ ⋃ i, CodeClass₂ i)
    (hcodeSubsingle₂ : ∀ i, (CodeClass₂ i).Subsingleton) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyBadCover
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hdich₁ CodeClass₁
    hcoverCode₁ (fun i => (hcodeSubsingle₁ i).countable) hdich₂ CodeClass₂ hcoverCode₂
    (fun i => (hcodeSubsingle₂ i).countable)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- If a subset of the complex plane admits an injective code into a countable type, then it is
countable.  This is the abstract form of the loop/order-type portrait lead: the hard combinatorics
can now target one injective countable invariant on the bad locus. -/
lemma countable_of_injOn_countable_code {κ : Type*} [Countable κ] {S : Set ℂ}
    (code : ℂ → κ) (hinj : InjOn code S) : S.Countable := by
  let codeS : S → κ := fun z => code z
  have hcodeS : Function.Injective codeS := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.property y.property hxy
  haveI : Countable S := hcodeS.countable
  exact Set.to_countable S

/-- **NoRelation from Moore-fiber dichotomy plus an injective loop/order code on bad portraits.**
This is the Grok loop-order lead in Lean form.  For each side, instead of supplying a countable
family of singleton portrait cells, it is enough to supply one code into a countable type that is
injective on the non-ray-confined bad frontier locus. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCodeBadCover
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)})
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  let Bad₁ : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
    ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z}
  let Bad₂ : Set ℂ := {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
    ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z}
  have hbad₁ : Bad₁.Countable :=
    countable_of_injOn_countable_code loopOrderCode₁ (by simpa [Bad₁] using hloopOrderInj₁)
  have hbad₂ : Bad₂.Countable :=
    countable_of_injOn_countable_code loopOrderCode₂ (by simpa [Bad₂] using hloopOrderInj₂)
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyBadCover
    (ι₁ := Unit) (ι₂ := Unit)
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hdich₁
    (fun _ : Unit => Bad₁) ?_ (fun _ => hbad₁) hdich₂ (fun _ : Unit => Bad₂) ?_
    (fun _ => hbad₂)
  · intro z hz
    simpa [Bad₁] using hz
  · intro z hz
    simpa [Bad₂] using hz

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62-facing endpoint from Moore-fiber dichotomy plus injective loop/order codes.**
This exposes the Grok loop-order primitive at the same level as the other connected q62 reductions. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)})
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCodeBadCover
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hdich₁ loopOrderCode₁
    hloopOrderInj₁ hdich₂ loopOrderCode₂ hloopOrderInj₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A total scanner order with a strictly increasing countable code makes that code injective on the
scanned set.  This is the formal core of the first-bifurcation-scale lead: totality comes from the
scanner finding the first separating bifurcation, and strictness comes from the return-loop/kneading
trace increasing at that bifurcation. -/
lemma injOn_of_total_strict_code {κ : Type*} [Preorder κ] {S : Set ℂ}
    (code : ℂ → κ) (scannerBefore : ℂ → ℂ → Prop)
    (htotal : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → scannerBefore x y ∨ scannerBefore y x)
    (hstrict : ∀ x ∈ S, ∀ y ∈ S, scannerBefore x y → code x < code y) :
    InjOn code S := by
  intro x hx y hy hxy
  by_contra hne
  rcases htotal x hx y hy hne with hltxy | hltyx
  · have hlt : code x < code y := hstrict x hx y hy hltxy
    rw [hxy] at hlt
    exact (lt_irrefl (code y)) hlt
  · have hlt : code y < code x := hstrict y hy x hx hltyx
    rw [hxy] at hlt
    exact (lt_irrefl (code y)) hlt

/-- **Connected q62-facing endpoint from a first-bifurcation scanner order.**
This is the next concrete Grok primitive after the loop/order-code endpoint.  The caller proves, on
each non-ray-confined bad locus, that the rational first-bifurcation scanner is total and that the
loop/order code strictly increases along it; Lean turns those two facts into injectivity and applies
the Moore-fiber loop-code endpoint. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)})
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ F : Set ℂ, IsPreconnected F ∧
          (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
          F ⊆ {z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)})
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hdich₁ loopOrderCode₁ ?_
    hdich₂ loopOrderCode₂ ?_
  · exact injOn_of_total_strict_code loopOrderCode₁ scannerBefore₁ hscannerTotal₁ hscannerStrict₁
  · exact injOn_of_total_strict_code loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- The exact frontier/off-other/common-component-closure slice used by the Moore-fiber branch. -/
def CommonComponentFrontierSlice (c₁ c₂ u : ℂ) : Set ℂ :=
  {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
    z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)}

/-- A nontrivial connected component of the exact slice is already a Moore-fiber witness.
This is the Lean core of Grok's two-arm-germ lead: the paper proof may now prove that the slice
component of `p` contains a second point, rather than constructing an arbitrary continuum `F`. -/
lemma mooreFiberWitness_of_nontrivial_commonComponentFrontierSlice_component
    {c₁ c₂ u p q : ℂ}
    (hp : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hq : q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p)
    (hne : q ≠ p) :
    ∃ F : Set ℂ, IsPreconnected F ∧
      (∃ a ∈ F, ∃ b ∈ F, a ≠ b) ∧
      F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} := by
  let F : Set ℂ := connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p
  have hpF : p ∈ F := by
    simpa [F] using mem_connectedComponentIn hp
  have hFpre : IsPreconnected F := by
    simpa [F] using (isPreconnected_connectedComponentIn (x := p)
      (F := CommonComponentFrontierSlice c₁ c₂ u))
  have hFsub : F ⊆ {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)} := by
    intro z hz
    have hzslice : z ∈ CommonComponentFrontierSlice c₁ c₂ u :=
      connectedComponentIn_subset (CommonComponentFrontierSlice c₁ c₂ u) p (by simpa [F] using hz)
    simpa [CommonComponentFrontierSlice] using hzslice
  exact ⟨F, hFpre, ⟨p, hpF, q, by simpa [F] using hq, Ne.symm hne⟩, hFsub⟩

/-- **Connected q62-facing endpoint from two-arm slice components plus injective loop/order codes.**
This is the first-separating-annulus/two-arm-germ interface: for each relevant base point, the
geometric proof only has to choose either a local nonpositive ray, or a second point in the same
connected component of the exact frontier/off-other/common-component-closure slice. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberSliceComponentLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₂ c₁ u) p ∧ q ≠ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | htwoArm
    · exact Or.inl hray
    · rcases htwoArm with ⟨q, hq, hnepq⟩
      exact Or.inr (mooreFiberWitness_of_nontrivial_commonComponentFrontierSlice_component
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (q := q)
        (by exact ⟨hpfront, hpoff, hpcl⟩) hq hnepq)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | htwoArm
    · exact Or.inl hray
    · rcases htwoArm with ⟨q, hq, hnepq⟩
      exact Or.inr (mooreFiberWitness_of_nontrivial_commonComponentFrontierSlice_component
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (q := q)
        (by exact ⟨hpfront, hpoff, hpcl⟩) hq hnepq)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62-facing endpoint from two-arm slice components and first-bifurcation scanners.**
This is the combined Grok route now exposed as one Lean target: prove the two-arm component alternative
for the Moore branch, and prove scanner totality plus strict code growth on the non-ray bad locus. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmSliceComponentFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₂ c₁ u) p ∧ q ≠ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberSliceComponentLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hdich₁ loopOrderCode₁ ?_
    hdich₂ loopOrderCode₂ ?_
  · exact injOn_of_total_strict_code loopOrderCode₁ scannerBefore₁ hscannerTotal₁ hscannerStrict₁
  · exact injOn_of_total_strict_code loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma exists_second_point_of_not_subsingleton {S : Set ℂ} {p : ℂ}
    (hnot : ¬ S.Subsingleton) :
    ∃ q, q ∈ S ∧ q ≠ p := by
  by_contra hnone
  push Not at hnone
  have hsub : S.Subsingleton := by
    intro x hx y hy
    have hxp : x = p := by
      exact hnone x hx
    have hyp : y = p := by
      exact hnone y hy
    exact hxp.trans hyp.symm
  exact hnot hsub

lemma exists_second_point_in_commonComponentFrontierSlice_component_of_not_subsingleton
    {c₁ c₂ u p : ℂ}
    (hnot : ¬ (connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p).Subsingleton) :
    ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p := by
  exact exists_second_point_of_not_subsingleton hnot

/-- **Connected q62-facing endpoint from non-singleton Moore atoms and first-bifurcation scanners.**
This is the Moore-atom version of the two-arm route: the geometric branch may now prove directly that
the connected component of the exact slice at `p` is not a singleton. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreAtomFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ¬ (connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p).Subsingleton)
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ¬ (connectedComponentIn (CommonComponentFrontierSlice c₂ c₁ u) p).Subsingleton)
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmSliceComponentFirstBifurcationScanner
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    scannerBefore₁ hscannerTotal₁ hscannerStrict₁ ?_ loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hnot
    · exact Or.inl hray
    · exact Or.inr (exists_second_point_in_commonComponentFrontierSlice_component_of_not_subsingleton
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) hnot)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hnot
    · exact Or.inl hray
    · exact Or.inr (exists_second_point_in_commonComponentFrontierSlice_component_of_not_subsingleton
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) hnot)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A preconnected nontrivial two-arm germ inside the exact slice forces the Moore atom/component at
`p` to be non-singleton.  This is the current Lean-facing form of Grok's two-arm-nonsubsingleton
slice primitive. -/
lemma commonComponentFrontierSlice_component_not_subsingleton_of_preconnected_nontrivial_subset
    {c₁ c₂ u p : ℂ} {A : Set ℂ}
    (hApre : IsPreconnected A) (hpA : p ∈ A) (hAnon : A.Nontrivial)
    (hAsub : A ⊆ CommonComponentFrontierSlice c₁ c₂ u) :
    ¬ (connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p).Subsingleton := by
  obtain ⟨q, hqA, hqne⟩ := hAnon.exists_ne p
  have hAcomp : A ⊆ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p :=
    hApre.subset_connectedComponentIn hpA hAsub
  intro hsub
  exact hqne (hsub (hAcomp hqA) (hAcomp hpA))

/-- **Connected q62-facing endpoint from two-arm preconnected germs and first-bifurcation scanners.**
The Moore branch no longer has to prove a component statement directly: it may provide a nontrivial
preconnected germ `A` through `p` contained in the exact frontier/off-other/common-component slice. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmPreconnectedGermFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
          A ⊆ CommonComponentFrontierSlice c₁ c₂ u)
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
          A ⊆ CommonComponentFrontierSlice c₂ c₁ u)
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreAtomFirstBifurcationScanner
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    scannerBefore₁ hscannerTotal₁ hscannerStrict₁ ?_ loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | htwoArm
    · exact Or.inl hray
    · rcases htwoArm with ⟨A, hApre, hpA, hAnon, hAsub⟩
      exact Or.inr (commonComponentFrontierSlice_component_not_subsingleton_of_preconnected_nontrivial_subset
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (A := A) hApre hpA hAnon hAsub)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | htwoArm
    · exact Or.inl hray
    · rcases htwoArm with ⟨A, hApre, hpA, hAnon, hAsub⟩
      exact Or.inr (commonComponentFrontierSlice_component_not_subsingleton_of_preconnected_nontrivial_subset
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (A := A) hApre hpA hAnon hAsub)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A nonconstant continuous interval arc in a target set supplies the preconnected nontrivial germ
needed by the two-arm slice route.  This is the Lean-facing bridge for Grok's local-wedge/crosscut
lead: once a geometric construction produces such a clipped arc in the exact slice, the Moore atom is
non-singleton. -/
lemma preconnected_nontrivial_germ_of_interval_arc
    {S : Set ℂ} {p : ℂ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ S)
    (hγ0 : γ 0 = p)
    (hγ1ne : γ 1 ≠ p) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧ A ⊆ S := by
  let A : Set ℂ := γ '' Set.Icc (0 : ℝ) 1
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · have hIpre : IsPreconnected (Set.Icc (0 : ℝ) 1) := isPreconnected_Icc
    simpa [A] using hIpre.image γ hγcont
  · have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    exact ⟨0, h0I, hγ0⟩
  · have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have h1I : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have hpA : p ∈ A := ⟨0, h0I, hγ0⟩
    have h1A : γ 1 ∈ A := ⟨1, h1I, rfl⟩
    exact Set.nontrivial_of_mem_mem_ne hpA h1A (Ne.symm (by simpa [hγ0] using hγ1ne))
  · exact hγsub

/-- Specialisation of the interval-arc bridge to the exact common-component frontier slice. -/
lemma commonComponentFrontierSlice_preconnected_germ_of_interval_arc
    {c₁ c₂ u p : ℂ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₁ c₂ u)
    (hγ0 : γ 0 = p)
    (hγ1ne : γ 1 ≠ p) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ CommonComponentFrontierSlice c₁ c₂ u := by
  exact preconnected_nontrivial_germ_of_interval_arc
    (S := CommonComponentFrontierSlice c₁ c₂ u) hγcont hγsub hγ0 hγ1ne

/-- **Connected q62-facing endpoint from interval two-arm germs and first-bifurcation scanners.**
This is the current implementation of Grok's local-wedge idea: the geometric side can now provide a
nonconstant continuous arc in the exact slice, instead of packaging the image as an abstract
preconnected set. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmIntervalGermFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
          γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₁ c₂ u ∧
          γ 0 = p ∧ γ 1 ≠ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
          γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₂ c₁ u ∧
          γ 0 = p ∧ γ 1 ≠ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmPreconnectedGermFirstBifurcationScanner
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    scannerBefore₁ hscannerTotal₁ hscannerStrict₁ ?_ loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | harc
    · exact Or.inl hray
    · rcases harc with ⟨γ, hγcont, hγsub, hγ0, hγ1ne⟩
      exact Or.inr (commonComponentFrontierSlice_preconnected_germ_of_interval_arc
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (γ := γ) hγcont hγsub hγ0 hγ1ne)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | harc
    · exact Or.inl hray
    · rcases harc with ⟨γ, hγcont, hγsub, hγ0, hγ1ne⟩
      exact Or.inr (commonComponentFrontierSlice_preconnected_germ_of_interval_arc
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (γ := γ) hγcont hγsub hγ0 hγ1ne)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A straight segment contained in a target set is a nonconstant interval arc in that set. -/
lemma interval_arc_of_segment_subset
    {S : Set ℂ} {p q : ℂ}
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t • (q - p) ∈ S)
    (hqne : q ≠ p) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ '' Set.Icc (0 : ℝ) 1 ⊆ S ∧ γ 0 = p ∧ γ 1 ≠ p := by
  let γ : ℝ → ℂ := fun t => p + t • (q - p)
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · have hγcont : Continuous γ := by
      fun_prop
    exact hγcont.continuousOn
  · intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact hseg t ht
  · simp [γ]
  · have hγ1 : γ 1 = q := by simp [γ]
    exact fun h => hqne (hγ1.symm.trans h)

/-- Specialisation of the straight-segment bridge to the exact common-component frontier slice. -/
lemma commonComponentFrontierSlice_interval_arc_of_segment_subset
    {c₁ c₂ u p q : ℂ}
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      p + t • (q - p) ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hqne : q ≠ p) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
      γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₁ c₂ u ∧
      γ 0 = p ∧ γ 1 ≠ p := by
  exact interval_arc_of_segment_subset
    (S := CommonComponentFrontierSlice c₁ c₂ u) hseg hqne

/-- **Connected q62-facing endpoint from straight two-arm segment germs and first-bifurcation
scanners.**  This is the straight-line version of Grok's local-wedge primitive: the geometric branch
may now aim for a distinct point `q` such that the full segment from `p` to `q` stays inside the exact
slice. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmSegmentFirstBifurcationScanner
    {κ₁ κ₂ : Type*} [Countable κ₁] [Preorder κ₁] [Countable κ₂] [Preorder κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ q : ℂ, q ≠ p ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            p + t • (q - p) ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (loopOrderCode₁ : ℂ → κ₁)
    (scannerBefore₁ : ℂ → ℂ → Prop)
    (hscannerTotal₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      x ≠ y → scannerBefore₁ x y ∨ scannerBefore₁ y x)
    (hscannerStrict₁ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ),
      scannerBefore₁ x y → loopOrderCode₁ x < loopOrderCode₁ y)
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ q : ℂ, q ≠ p ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            p + t • (q - p) ∈ CommonComponentFrontierSlice c₂ c₁ u)
    (loopOrderCode₂ : ℂ → κ₂)
    (scannerBefore₂ : ℂ → ℂ → Prop)
    (hscannerTotal₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      x ≠ y → scannerBefore₂ x y ∨ scannerBefore₂ y x)
    (hscannerStrict₂ : ∀ x ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      ∀ y ∈ ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ),
      scannerBefore₂ x y → loopOrderCode₂ x < loopOrderCode₂ y) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmIntervalGermFirstBifurcationScanner
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    scannerBefore₁ hscannerTotal₁ hscannerStrict₁ ?_ loopOrderCode₂ scannerBefore₂ hscannerTotal₂ hscannerStrict₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hseg
    · exact Or.inl hray
    · rcases hseg with ⟨q, hqne, hseg⟩
      exact Or.inr (commonComponentFrontierSlice_interval_arc_of_segment_subset
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (q := q) hseg hqne)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hseg
    · exact Or.inl hray
    · rcases hseg with ⟨q, hqne, hseg⟩
      exact Or.inr (commonComponentFrontierSlice_interval_arc_of_segment_subset
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (q := q) hseg hqne)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62-facing endpoint from interval two-arm germs and injective loop/order codes.**
This removes the scanner-totality and scanner-strictness obligations from the interval-arc route: the
bad non-ray locus only has to carry an injective countable code. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmIntervalGermLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
          γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₁ c₂ u ∧
          γ 0 = p ∧ γ 1 ≠ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 1) ∧
          γ '' Set.Icc (0 : ℝ) 1 ⊆ CommonComponentFrontierSlice c₂ c₁ u ∧
          γ 0 = p ∧ γ 1 ≠ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | harc
    · exact Or.inl hray
    · rcases harc with ⟨γ, hγcont, hγsub, hγ0, hγ1ne⟩
      rcases commonComponentFrontierSlice_preconnected_germ_of_interval_arc
          (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (γ := γ)
          hγcont hγsub hγ0 hγ1ne with ⟨A, hApre, hpA, hAnon, hAsub⟩
      obtain ⟨q, hqA, hqne⟩ := hAnon.exists_ne p
      refine Or.inr ⟨A, hApre, ?_, ?_⟩
      · exact ⟨q, hqA, p, hpA, hqne⟩
      · intro z hzA
        simpa [CommonComponentFrontierSlice] using hAsub hzA
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | harc
    · exact Or.inl hray
    · rcases harc with ⟨γ, hγcont, hγsub, hγ0, hγ1ne⟩
      rcases commonComponentFrontierSlice_preconnected_germ_of_interval_arc
          (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (γ := γ)
          hγcont hγsub hγ0 hγ1ne with ⟨A, hApre, hpA, hAnon, hAsub⟩
      obtain ⟨q, hqA, hqne⟩ := hAnon.exists_ne p
      refine Or.inr ⟨A, hApre, ?_, ?_⟩
      · exact ⟨q, hqA, p, hpA, hqne⟩
      · intro z hzA
        simpa [CommonComponentFrontierSlice] using hAsub hzA

/-- **Connected q62-facing endpoint from straight two-arm segment germs and injective loop/order
codes.**  This combines Grok's straight-segment local-wedge lead with the existing loop-code bad-locus
countability route, so no scanner relation has to be supplied. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmSegmentLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ q : ℂ, q ≠ p ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            p + t • (q - p) ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ q : ℂ, q ≠ p ∧
          ∀ t ∈ Set.Icc (0 : ℝ) 1,
            p + t • (q - p) ∈ CommonComponentFrontierSlice c₂ c₁ u)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffTwoArmIntervalGermLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hseg
    · exact Or.inl hray
    · rcases hseg with ⟨q, hqne, hseg⟩
      exact Or.inr (commonComponentFrontierSlice_interval_arc_of_segment_subset
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (q := q) hseg hqne)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hseg
    · exact Or.inl hray
    · rcases hseg with ⟨q, hqne, hseg⟩
      exact Or.inr (commonComponentFrontierSlice_interval_arc_of_segment_subset
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (q := q) hseg hqne)

end Bottcher

namespace Bottcher

/-- Failure of all local nonpositive-ray confinements gives, for any chosen unit direction and any
scale, a filled-Julia point in that scale that is not on the corresponding nonpositive ray. -/
lemma exists_off_nonpositive_ray_witness_of_not_exists_localNonpositiveRayConfined
    {c v p : ℂ} (hv : ‖v‖ = 1)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c v p)
    {r : ℝ} (hr : 0 < r) :
    ∃ w, w ∈ Metric.ball p r ∧ w ∈ filledJulia c ∧
      ∀ t : ℝ, t ≤ 0 → v * (w - p) ≠ (t : ℂ) := by
  by_contra hnone
  push Not at hnone
  have hconf : LocalNonpositiveRayConfined c v p := by
    refine ⟨r, hr, ?_⟩
    intro w hw hK
    exact hnone w hw hK
  exact hbad ⟨v, hv, hconf⟩

lemma mem_frontier_filledJulia_of_mem_emptyInterior {c w : ℂ}
    (hempty : interior (filledJulia c) = ∅) (hw : w ∈ filledJulia c) :
    w ∈ frontier (filledJulia c) := by
  rw [(isClosed_filledJulia c).frontier_eq]
  exact ⟨hw, by simp [hempty]⟩

/-- With empty interior and an off-other neighbourhood, a non-ray point yields a nearby frontier point
that remains off the other filled Julia set and avoids any prescribed nonpositive ray direction. -/
lemma exists_frontier_offOther_off_nonpositive_ray_witness_of_not_exists_localNonpositiveRayConfined
    {c₁ c₂ v p : ℂ} (hempty : interior (filledJulia c₁) = ∅)
    (hpoff : p ∈ (filledJulia c₂)ᶜ) (hv : ‖v‖ = 1)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) :
    ∃ w, w ∈ frontier (filledJulia c₁) ∧ w ∈ (filledJulia c₂)ᶜ ∧
      ∀ t : ℝ, t ≤ 0 → v * (w - p) ≠ (t : ℂ) := by
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  obtain ⟨w, hwball, hwK, hnotray⟩ :=
    exists_off_nonpositive_ray_witness_of_not_exists_localNonpositiveRayConfined
      (c := c₁) (v := v) (p := p) hv hbad hr
  exact ⟨w, mem_frontier_filledJulia_of_mem_emptyInterior hempty hwK, hball hwball, hnotray⟩

end Bottcher

namespace Bottcher

/-- Scale-controlled version of the non-ray witness: under empty interior and off-other openness, every
prescribed neighbourhood of a non-ray point contains a frontier/off-other point avoiding any chosen
nonpositive ray direction. -/
lemma exists_frontier_offOther_off_nonpositive_ray_witness_in_ball_of_not_exists_localNonpositiveRayConfined
    {c₁ c₂ v p : ℂ} (hempty : interior (filledJulia c₁) = ∅)
    (hpoff : p ∈ (filledJulia c₂)ᶜ) (hv : ‖v‖ = 1)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    {R : ℝ} (hR : 0 < R) :
    ∃ w, w ∈ Metric.ball p R ∧ w ∈ frontier (filledJulia c₁) ∧ w ∈ (filledJulia c₂)ᶜ ∧
      ∀ t : ℝ, t ≤ 0 → v * (w - p) ≠ (t : ℂ) := by
  obtain ⟨rOff, hrOff, hballOff⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let ρ : ℝ := min R rOff
  have hρ : 0 < ρ := lt_min hR hrOff
  obtain ⟨w, hwρ, hwK, hnotray⟩ :=
    exists_off_nonpositive_ray_witness_of_not_exists_localNonpositiveRayConfined
      (c := c₁) (v := v) (p := p) hv hbad hρ
  have hwR : w ∈ Metric.ball p R := Metric.ball_subset_ball (min_le_left R rOff) hwρ
  have hwoff : w ∈ (filledJulia c₂)ᶜ :=
    hballOff (Metric.ball_subset_ball (min_le_right R rOff) hwρ)
  exact ⟨w, hwR, mem_frontier_filledJulia_of_mem_emptyInterior hempty hwK, hwoff, hnotray⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- If a locally preconnected slice contains `p` and a distinct nearby point, its local piece is the
nontrivial preconnected germ needed by the Moore/two-arm route. -/
lemma preconnected_nontrivial_germ_of_local_preconnected_second_point
    {S : Set ℂ} {p q : ℂ} {R : ℝ} (hR : 0 < R)
    (hpS : p ∈ S) (hqS : q ∈ S) (hqball : q ∈ Metric.ball p R) (hqne : q ≠ p)
    (hpre : IsPreconnected (S ∩ Metric.ball p R)) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧ A ⊆ S := by
  let A : Set ℂ := S ∩ Metric.ball p R
  refine ⟨A, hpre, ?_, ?_, ?_⟩
  · exact ⟨hpS, Metric.mem_ball_self hR⟩
  · have hpA : p ∈ A := ⟨hpS, Metric.mem_ball_self hR⟩
    have hqA : q ∈ A := ⟨hqS, hqball⟩
    exact Set.nontrivial_of_mem_mem_ne hqA hpA hqne
  · exact fun z hz => hz.1

/-- A local exact-slice preconnectedness/crosscut condition turns failure of local ray confinement into
a nontrivial preconnected germ inside `CommonComponentFrontierSlice`.  The off-ray witness supplies the
distinct nearby frontier/off-other point; the local closure-saturation hypothesis puts that point back
in the exact common-component slice. -/
lemma commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    (hR : 0 < R)
    (hlocalClosure : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hpre : IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R)) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ CommonComponentFrontierSlice c₁ c₂ u := by
  have hv : ‖(1 : ℂ)‖ = 1 := by norm_num
  obtain ⟨q, hqball, hqfront, hqoff, hqnotray⟩ :=
    exists_frontier_offOther_off_nonpositive_ray_witness_in_ball_of_not_exists_localNonpositiveRayConfined
      (c₁ := c₁) (c₂ := c₂) (v := (1 : ℂ)) (p := p) hempty hpS.2.1 hv hbad hR
  have hqS : q ∈ CommonComponentFrontierSlice c₁ c₂ u :=
    ⟨hqfront, hqoff, hlocalClosure q hqball hqfront hqoff⟩
  have hqne : q ≠ p := by
    intro hqp
    have hzero : (1 : ℂ) * (q - p) = (0 : ℂ) := by simp [hqp]
    exact (hqnotray 0 (by norm_num)) hzero
  exact preconnected_nontrivial_germ_of_local_preconnected_second_point
    (S := CommonComponentFrontierSlice c₁ c₂ u) hR hpS hqS hqball hqne hpre

/-- **Connected q62-facing endpoint from local exact-slice preconnectedness and injective loop/order
codes.**  This is the Lean form of Grok's nondegenerate-component/crosscut lead: once local topology
shows that the exact frontier/off-other/common-component slice is preconnected near every relevant
point and locally saturated by the common-basin component closure, the no-ray case automatically
produces the two-arm germ. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  classical
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberDichotomyLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    by_cases hray : ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p
    · exact Or.inl hray
    · obtain ⟨R, hR, hlocalClosure, hpre⟩ := hlocal₁ p u huU hpfront hpoff hpcl
      have hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u := ⟨hpfront, hpoff, hpcl⟩
      obtain ⟨A, hApre, hpA, hAnon, hAsub⟩ :=
        commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray
          (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (R := R)
          hempty₁ hpS hray hR hlocalClosure hpre
      obtain ⟨q, hqA, hqne⟩ := hAnon.exists_ne p
      refine Or.inr ⟨A, hApre, ?_, ?_⟩
      · exact ⟨q, hqA, p, hpA, hqne⟩
      · intro z hzA
        simpa [CommonComponentFrontierSlice] using hAsub hzA
  · intro p u huU hpfront hpoff hpcl
    by_cases hray : ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p
    · exact Or.inl hray
    · obtain ⟨R, hR, hlocalClosure, hpre⟩ := hlocal₂ p u huU hpfront hpoff hpcl
      have hpS : p ∈ CommonComponentFrontierSlice c₂ c₁ u := ⟨hpfront, hpoff, hpcl⟩
      obtain ⟨A, hApre, hpA, hAnon, hAsub⟩ :=
        commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray
          (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (R := R)
          hempty₂ hpS hray hR hlocalClosure hpre
      obtain ⟨q, hqA, hqne⟩ := hAnon.exists_ne p
      refine Or.inr ⟨A, hApre, ?_, ?_⟩
      · exact ⟨q, hqA, p, hpA, hqne⟩
      · intro z hzA
        simpa [CommonComponentFrontierSlice] using hAsub hzA

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma mem_closure_of_tendsto_sequence {S : Set ℂ} {z : ℂ} {γ : ℕ → ℂ}
    (hγS : ∀ n, γ n ∈ S) (hγlim : Tendsto γ atTop (𝓝 z)) :
    z ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro V hV
  have hEventually : ∀ᶠ n in atTop, γ n ∈ V := hγlim hV
  rcases hEventually.exists with ⟨n, hnV⟩
  exact ⟨γ n, hnV, hγS n⟩

/-- Local common-basin approach sequences give the closure-saturation input needed by the local
exact-slice route.  This is the formal core of the crosscut/Green lead: construct points in the same
common-basin component converging to every local frontier/off-other point. -/
lemma localClosureSaturation_of_commonComponent_tendsto_sequences
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ γ : ℕ → ℂ,
        (∀ n, γ n ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        Tendsto γ atTop (𝓝 z)) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  intro z hzball hzfront hzoff
  obtain ⟨γ, hγS, hγlim⟩ := happroach z hzball hzfront hzoff
  exact mem_closure_of_tendsto_sequence hγS hγlim

/-- Non-ray plus local exact-slice preconnectedness follows from common-basin approach sequences,
rather than an already-packaged closure-saturation hypothesis. -/
lemma commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray_of_commonComponent_approaches
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    (hR : 0 < R)
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ γ : ℕ → ℂ,
        (∀ n, γ n ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        Tendsto γ atTop (𝓝 z))
    (hpre : IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R)) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ CommonComponentFrontierSlice c₁ c₂ u := by
  exact commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray
    (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (R := R)
    hempty hpS hbad hR
    (localClosureSaturation_of_commonComponent_tendsto_sequences happroach) hpre

/-- **Connected q62-facing endpoint from common-component approach sequences, local exact-slice
preconnectedness, and injective loop/order codes.**  This is the crosscut/Green approach form of the
local exact-slice route: the geometric side can provide explicit sequences in the common exterior
component converging to each local frontier/off-other point. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceApproachPreconnectedLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ γ : ℕ → ℂ,
            (∀ n, γ n ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
            Tendsto γ atTop (𝓝 z)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ γ : ℕ → ℂ,
            (∀ n, γ n ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
            Tendsto γ atTop (𝓝 z)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, hR, happroach, hpre⟩ := hlocal₁ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, localClosureSaturation_of_commonComponent_tendsto_sequences happroach, hpre⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, hR, happroach, hpre⟩ := hlocal₂ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, localClosureSaturation_of_commonComponent_tendsto_sequences happroach, hpre⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A one-sided approach curve contained in a set proves the endpoint lies in the set closure. -/
lemma mem_closure_of_tendsto_right_curve {S : Set ℂ} {z : ℂ} {γ : ℝ → ℂ}
    (hγS : ∀ t : ℝ, 0 < t → γ t ∈ S)
    (hγlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    z ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro V hV
  have hVev : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ V := hγlim hV
  have hposev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := by
    exact eventually_mem_nhdsWithin
  rcases (hVev.and hposev).exists with ⟨t, htV, htpos⟩
  exact ⟨γ t, htV, hγS t htpos⟩

/-- Local common-basin approach curves give the closure-saturation input needed by the local exact-slice
route.  This is closer to the crosscut/equipotential geometry than explicit sequences: a curve in the
common exterior component tends to each local frontier/off-other point from positive time. -/
lemma localClosureSaturation_of_commonComponent_right_tendsto_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ γ : ℝ → ℂ,
        (∀ t : ℝ, 0 < t →
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  intro z hzball hzfront hzoff
  obtain ⟨γ, hγS, hγlim⟩ := happroach z hzball hzfront hzoff
  exact mem_closure_of_tendsto_right_curve hγS hγlim

/-- Non-ray plus local exact-slice preconnectedness follows from common-basin approach curves. -/
lemma commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray_of_commonComponent_right_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hbad : ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p)
    (hR : 0 < R)
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ γ : ℝ → ℂ,
        (∀ t : ℝ, 0 < t →
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z))
    (hpre : IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R)) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ CommonComponentFrontierSlice c₁ c₂ u := by
  exact commonComponentFrontierSlice_preconnected_germ_of_local_preconnected_nonray
    (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (R := R)
    hempty hpS hbad hR
    (localClosureSaturation_of_commonComponent_right_tendsto_curves happroach) hpre

/-- **Connected q62-facing endpoint from common-component approach curves, local exact-slice
preconnectedness, and injective loop/order codes.**  This is the direct crosscut/equipotential-curve
version of the local route: the geometric side supplies curves in the common exterior component tending
to each local frontier/off-other point. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceApproachCurvePreconnectedLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ γ : ℝ → ℂ,
            (∀ t : ℝ, 0 < t →
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ R : ℝ, 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ γ : ℝ → ℂ,
            (∀ t : ℝ, 0 < t →
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) ∧
        IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, hR, happroach, hpre⟩ := hlocal₁ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, localClosureSaturation_of_commonComponent_right_tendsto_curves happroach, hpre⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, hR, happroach, hpre⟩ := hlocal₂ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, localClosureSaturation_of_commonComponent_right_tendsto_curves happroach, hpre⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma isPreconnected_of_interval_param_eq
    {S : Set ℂ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγimage : γ '' Set.Icc (0 : ℝ) 1 = S) :
    IsPreconnected S := by
  have hIpre : IsPreconnected (Set.Icc (0 : ℝ) 1) := isPreconnected_Icc
  simpa [hγimage] using hIpre.image γ hγcont

lemma commonComponentFrontierSlice_local_preconnected_of_interval_param
    {c₁ c₂ u p : ℂ} {R : ℝ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγimage : γ '' Set.Icc (0 : ℝ) 1 =
      CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) :
    IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) := by
  exact isPreconnected_of_interval_param_eq hγcont hγimage

/-- **Connected q62-facing endpoint from common-component approach curves, interval-parametrized local
exact slices, and injective loop/order codes.**  This is the most direct current crosscut/prime-end
surface: local Green/crosscut geometry may provide one interval parametrization of the exact slice in a
small ball, plus one-sided approach curves from the common exterior component. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceApproachCurveParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ γ : ℝ → ℂ,
            (∀ t : ℝ, 0 < t →
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        γslice '' Set.Icc (0 : ℝ) 1 =
          CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ γ : ℝ → ℂ,
            (∀ t : ℝ, 0 < t →
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        γslice '' Set.Icc (0 : ℝ) 1 =
          CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceApproachCurvePreconnectedLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγimage⟩ := hlocal₁ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, happroach,
      commonComponentFrontierSlice_local_preconnected_of_interval_param hγcont hγimage⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγimage⟩ := hlocal₂ p u huU hpfront hpoff hpcl
    exact ⟨R, hR, happroach,
      commonComponentFrontierSlice_local_preconnected_of_interval_param hγcont hγimage⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma mem_closure_of_eventually_right_curve {S : Set ℂ} {z : ℂ} {γ : ℝ → ℂ}
    (hγS : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ S)
    (hγlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z)) :
    z ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro V hV
  have hVev : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ V := hγlim hV
  rcases (hVev.and hγS).exists with ⟨t, htV, htS⟩
  exact ⟨γ t, htV, htS⟩

lemma tendsto_right_of_continuousAt {z : ℂ} {γ : ℝ → ℂ}
    (hγcont : ContinuousAt γ 0) (hγ0 : γ 0 = z) :
    Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have hlim : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 (γ 0)) :=
    hγcont.mono_left nhdsWithin_le_nhds
  simpa [hγ0] using hlim

/-- Eventual common-component membership near the boundary endpoint is enough for closure.  This is the
right interface for crosscuts whose parametrization is only known to lie in the common exterior for all
sufficiently small positive times. -/
lemma localClosureSaturation_of_commonComponent_eventual_right_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ γ : ℝ → ℂ,
        ContinuousAt γ 0 ∧ γ 0 = z ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  intro z hzball hzfront hzoff
  obtain ⟨γ, hγcont, hγ0, hγS⟩ := happroach z hzball hzfront hzoff
  exact mem_closure_of_eventually_right_curve hγS (tendsto_right_of_continuousAt hγcont hγ0)

lemma isPreconnected_of_interval_param_surj
    {S : Set ℂ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγmaps : MapsTo γ (Set.Icc (0 : ℝ) 1) S)
    (hγsurj : ∀ z ∈ S, ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = z) :
    IsPreconnected S := by
  have hIpre : IsPreconnected (Set.Icc (0 : ℝ) 1) := isPreconnected_Icc
  have himage : γ '' Set.Icc (0 : ℝ) 1 = S := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨t, ht, rfl⟩
      exact hγmaps ht
    · intro hz
      obtain ⟨t, ht, htz⟩ := hγsurj z hz
      exact ⟨t, ht, htz⟩
  simpa [himage] using hIpre.image γ hγcont

lemma commonComponentFrontierSlice_local_preconnected_of_interval_param_surj
    {c₁ c₂ u p : ℂ} {R : ℝ} {γ : ℝ → ℂ}
    (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1))
    (hγmaps : MapsTo γ (Set.Icc (0 : ℝ) 1)
      (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (hγsurj : ∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
      ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = z) :
    IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) := by
  exact isPreconnected_of_interval_param_surj hγcont hγmaps hγsurj

/-- **Connected q62-facing endpoint from endpoint-continuous crosscut access curves, surjective local
slice parametrizations, and injective loop/order codes.**  This weakens the previous parametrized route:
approach curves need only be continuous at `0` and eventually lie in the common component, and the local
slice parametrization is supplied by `MapsTo` plus pointwise surjectivity. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ γ : ℝ → ℂ,
            ContinuousAt γ 0 ∧ γ 0 = z ∧
            ∀ᶠ t in 𝓝[>] (0 : ℝ),
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ γ : ℝ → ℂ,
            ContinuousAt γ 0 ∧ γ 0 = z ∧
            ∀ᶠ t in 𝓝[>] (0 : ℝ),
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, hR, ?_, ?_⟩
    · exact localClosureSaturation_of_commonComponent_eventual_right_curves happroach
    · exact commonComponentFrontierSlice_local_preconnected_of_interval_param_surj
        hγcont hγmaps hγsurj
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, hR, ?_, ?_⟩
    · exact localClosureSaturation_of_commonComponent_eventual_right_curves happroach
    · exact commonComponentFrontierSlice_local_preconnected_of_interval_param_surj
        hγcont hγmaps hγsurj

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma eventually_right_mem_of_Ioc_subset {S : Set ℂ} {γ : ℝ → ℂ} {ε : ℝ}
    (hε : 0 < ε) (hmem : ∀ t ∈ Set.Ioc (0 : ℝ) ε, γ t ∈ S) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ S := by
  filter_upwards [Ioc_mem_nhdsGT hε] with t ht
  exact hmem t ht

lemma continuousAccess_of_Ioc_component_crosscut {S : Set ℂ} {z : ℂ} {γ : ℝ → ℂ} {ε : ℝ}
    (hγcont : ContinuousAt γ 0) (hγ0 : γ 0 = z) (hε : 0 < ε)
    (hmem : ∀ t ∈ Set.Ioc (0 : ℝ) ε, γ t ∈ S) :
    ContinuousAt γ 0 ∧ γ 0 = z ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ S :=
  ⟨hγcont, hγ0, eventually_right_mem_of_Ioc_subset hε hmem⟩

/-- A crosscut parametrized on `(0, ε]` inside the common component gives the local closure
saturation needed by the q62 exact-slice endpoint. -/
lemma localClosureSaturation_of_commonComponent_Ioc_access_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (γ : ℝ → ℂ) (ε : ℝ),
        ContinuousAt γ 0 ∧ γ 0 = z ∧ 0 < ε ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) ε,
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  apply localClosureSaturation_of_commonComponent_eventual_right_curves
  intro z hzball hzfront hzoff
  obtain ⟨γ, ε, hγcont, hγ0, hε, hγS⟩ := happroach z hzball hzfront hzoff
  exact ⟨γ, continuousAccess_of_Ioc_component_crosscut hγcont hγ0 hε hγS⟩

/-- **Connected q62-facing endpoint from closed-tail crosscut access curves.**  This is the
`(0, ε]` crosscut version of the eventual-access endpoint: the local geometric input may state that
each endpoint is approached by a curve whose positive tail lies in the common exterior component. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousIocAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            ContinuousAt γ 0 ∧ γ 0 = z ∧ 0 < ε ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            ContinuousAt γ 0 ∧ γ 0 = z ∧ 0 < ε ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousAccessParamLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨γ, ε, hγcont, hγ0, hε, hγS⟩ := happroach z hzball hzfront hzoff
    exact ⟨γ, continuousAccess_of_Ioc_component_crosscut hγcont hγ0 hε hγS⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨γ, ε, hγcont, hγ0, hε, hγS⟩ := happroach z hzball hzfront hzoff
    exact ⟨γ, continuousAccess_of_Ioc_component_crosscut hγcont hγ0 hε hγS⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- One-sided convergence plus a positive crosscut tail inside the common component gives the local
closure saturation needed by the exact-slice endpoint.  This avoids asking the crosscut extension to
be ambient-continuous at the endpoint. -/
lemma localClosureSaturation_of_commonComponent_rightTendsto_Ioc_access_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (γ : ℝ → ℂ) (ε : ℝ),
        Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) ∧ 0 < ε ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) ε,
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  intro z hzball hzfront hzoff
  obtain ⟨γ, ε, hγlim, hε, hγS⟩ := happroach z hzball hzfront hzoff
  exact mem_closure_of_eventually_right_curve
    (eventually_right_mem_of_Ioc_subset hε hγS) hγlim

/-- **Connected q62-facing endpoint from one-sided crosscut access and local exact-slice
parametrization.**  The access input is now just `Tendsto` along `𝓝[>] 0` plus membership on a
positive interval tail, matching the data produced by a parametrized crosscut without requiring an
ambient continuous extension through the endpoint. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRightTendstoIocAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) ∧ 0 < ε ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) ∧ 0 < ε ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, hR, ?_, ?_⟩
    · exact localClosureSaturation_of_commonComponent_rightTendsto_Ioc_access_curves happroach
    · exact commonComponentFrontierSlice_local_preconnected_of_interval_param_surj
        hγcont hγmaps hγsurj
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, hR, ?_, ?_⟩
    · exact localClosureSaturation_of_commonComponent_rightTendsto_Ioc_access_curves happroach
    · exact commonComponentFrontierSlice_local_preconnected_of_interval_param_surj
        hγcont hγmaps hγsurj

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma tendsto_right_of_continuousOn_Icc {γ : ℝ → ℂ} {z : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) ε)) (hγ0 : γ 0 = z) :
    Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 z) := by
  have hwithin : Tendsto γ (𝓝[Set.Ioc (0 : ℝ) ε] (0 : ℝ)) (𝓝 (γ 0)) := by
    exact ((hγcont.continuousWithinAt ⟨le_rfl, le_of_lt hε⟩).mono Set.Ioc_subset_Icc_self)
  rw [nhdsWithin_Ioc_eq_nhdsGT hε] at hwithin
  simpa [hγ0] using hwithin

/-- A closed-interval crosscut with endpoint value `z` and open tail in the common component gives
one-sided access to the component closure. -/
lemma localClosureSaturation_of_commonComponent_Icc_access_curves
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (γ : ℝ → ℂ) (ε : ℝ),
        0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) ε,
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  apply localClosureSaturation_of_commonComponent_rightTendsto_Ioc_access_curves
  intro z hzball hzfront hzoff
  obtain ⟨γ, ε, hε, hγcont, hγ0, hγS⟩ := happroach z hzball hzfront hzoff
  exact ⟨γ, ε, tendsto_right_of_continuousOn_Icc hε hγcont hγ0, hε, hγS⟩

/-- **Connected q62-facing endpoint from closed-interval crosscuts and local exact-slice
parametrization.**  This is the shape a literal crosscut proof should provide: each local boundary
point is the endpoint of a continuous interval curve whose positive tail stays in the common exterior
component. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousIccAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ (γ : ℝ → ℂ) (ε : ℝ),
            0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
            ∀ t ∈ Set.Ioc (0 : ℝ) ε,
              γ t ∈ connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRightTendstoIocAccessParamLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨γ, ε, hε, hγcont, hγ0, hγS⟩ := happroach z hzball hzfront hzoff
    exact ⟨γ, ε, tendsto_right_of_continuousOn_Icc hε hγcont hγ0, hε, hγS⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨γ, ε, hε, hγcont, hγ0, hγS⟩ := happroach z hzball hzfront hzoff
    exact ⟨γ, ε, tendsto_right_of_continuousOn_Icc hε hγcont hγ0, hε, hγS⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A local rotated slit sector inside `S` supplies a concrete closed-interval crosscut: the straight
ray `t ↦ z + v⁻¹ t`, shortened to half the supplied radius. -/
lemma exists_Icc_crosscut_of_rotated_slit_subset {S : Set ℂ} {v z : ℂ} {η : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 < η)
    (hslit : Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆ S) :
    ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) ε, γ t ∈ S := by
  let γ : ℝ → ℂ := fun t => z + v⁻¹ * (t : ℂ)
  let ε : ℝ := η / 2
  have hε : 0 < ε := by dsimp [ε]; exact half_pos hη
  refine ⟨γ, ε, hε, ?_, ?_, ?_⟩
  · exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  · simp [γ]
  · intro t ht
    have hne : v ≠ 0 := by
      intro hv0
      rw [hv0, norm_zero] at hv
      norm_num at hv
    have hsub : γ t - z = v⁻¹ * (t : ℂ) := by
      simp [γ]
    apply hslit
    constructor
    · rw [Metric.mem_ball, dist_eq_norm, hsub, norm_mul, norm_inv, hv]
      rw [Complex.norm_of_nonneg (le_of_lt ht.1)]
      norm_num
      exact lt_of_le_of_lt ht.2 (by dsimp [ε]; exact half_lt_self hη)
    · change v * (γ t - z) ∈ Complex.slitPlane
      rw [hsub, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      exact Complex.ofReal_mem_slitPlane.2 ht.1

lemma localClosureSaturation_of_commonComponent_rotatedSlit_access
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
        Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
          connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  apply localClosureSaturation_of_commonComponent_Icc_access_curves
  intro z hzball hzfront hzoff
  obtain ⟨v, η, hv, hη, hslit⟩ := happroach z hzball hzfront hzoff
  exact exists_Icc_crosscut_of_rotated_slit_subset hv hη hslit

/-- **Connected q62-facing endpoint from local rotated slit-sector access and local exact-slice
parametrization.**  This turns a concrete slit-sector inclusion in the common component into the
closed-interval crosscuts consumed by the q62 route. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRotatedSlitAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
            Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
              connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
            Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
              connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousIccAccessParamLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨v, η, hv, hη, hslit⟩ := happroach z hzball hzfront hzoff
    exact exists_Icc_crosscut_of_rotated_slit_subset hv hη hslit
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨v, η, hv, hη, hslit⟩ := happroach z hzball hzfront hzoff
    exact exists_Icc_crosscut_of_rotated_slit_subset hv hη hslit

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_nonempty_inter
    {c₁ c₂ u v z : ℂ} {η : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 < η)
    (hsubC : Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
      ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ))
    (hinter : (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ∩
      connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u).Nonempty) :
    Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
      connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  let S : Set ℂ := Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane}
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  have hpre : IsPreconnected S :=
    isPreconnected_ball_inter_rotated_translated_slitPlane v z hv hη
  obtain ⟨y, hyS, hyComp⟩ := hinter
  have hSsubY : S ⊆ connectedComponentIn C y := hpre.subset_connectedComponentIn hyS hsubC
  have hcomp : connectedComponentIn C u = connectedComponentIn C y := connectedComponentIn_eq hyComp
  intro x hx
  rw [hcomp]
  exact hSsubY hx

lemma localClosureSaturation_of_commonComponent_rotatedSlit_commonExterior_inter_access
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (happroach : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
        Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
          ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) ∧
        (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ∩
          connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u).Nonempty) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  apply localClosureSaturation_of_commonComponent_rotatedSlit_access
  intro z hzball hzfront hzoff
  obtain ⟨v, η, hv, hη, hsubC, hinter⟩ := happroach z hzball hzfront hzoff
  exact ⟨v, η, hv, hη,
    rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_nonempty_inter hv hη hsubC hinter⟩

/-- **Connected q62-facing endpoint from common-exterior slit sectors that touch the selected common
component.**  This separates the geometric work into two native checks: the local slit sector lies in
the common exterior, and it intersects the chosen component. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRotatedSlitCommonExteriorInterAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
            Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
              ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) ∧
            (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ∩
              connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u).Nonempty) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
            Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
              ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) ∧
            (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ∩
              connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u).Nonempty) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRotatedSlitAccessParamLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨v, η, hv, hη, hsubC, hinter⟩ := happroach z hzball hzfront hzoff
    exact ⟨v, η, hv, hη,
      rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_nonempty_inter hv hη hsubC hinter⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, happroach, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    intro z hzball hzfront hzoff
    obtain ⟨v, η, hv, hη, hsubC, hinter⟩ := happroach z hzball hzfront hzoff
    exact ⟨v, η, hv, hη,
      rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_nonempty_inter hv hη hsubC hinter⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A locally preconnected, nontrivial exact slice already gives the Moore two-arm alternative:
the local slice through `p` lies in the connected component of the global exact slice at `p`, and
nontriviality supplies the second point. -/
lemma exists_second_point_in_commonComponentFrontierSlice_component_of_local_preconnected_nontrivial
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hR : 0 < R) (hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hpre : IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (hnon : (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Nontrivial) :
    ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p := by
  let A : Set ℂ := CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R
  have hpA : p ∈ A := ⟨hpS, Metric.mem_ball_self hR⟩
  have hAsub : A ⊆ CommonComponentFrontierSlice c₁ c₂ u := fun z hz => hz.1
  have hAcomp : A ⊆ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p :=
    hpre.subset_connectedComponentIn hpA hAsub
  obtain ⟨q, hqA, hqne⟩ := hnon.exists_ne p
  exact ⟨q, hAcomp hqA, hqne⟩

/-- **Connected q62-facing endpoint from a local nontrivial Moore atom.**  This is the Grok-style
bypass of interval parametrization: instead of parametrizing the exact slice, the geometric branch may
prove directly that a small exact slice around each non-ray point is preconnected and nontrivial. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedNontrivialLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ R : ℝ, 0 < R ∧
          IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Nontrivial)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ R : ℝ, 0 < R ∧
          IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R).Nontrivial)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberSliceComponentLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · obtain ⟨R, hR, hpre, hnon⟩ := hlocal
      exact Or.inr
        (exists_second_point_in_commonComponentFrontierSlice_component_of_local_preconnected_nontrivial
          (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) hR ⟨hpfront, hpoff, hpcl⟩ hpre hnon)
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · obtain ⟨R, hR, hpre, hnon⟩ := hlocal
      exact Or.inr
        (exists_second_point_in_commonComponentFrontierSlice_component_of_local_preconnected_nontrivial
          (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) hR ⟨hpfront, hpoff, hpcl⟩ hpre hnon)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma rotatedSlit_inter_connectedComponentIn_of_mem_closure
    {c₁ c₂ u v z : ℂ} {η : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 < η)
    (hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) :
    (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ∩
      connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u).Nonempty := by
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hVopen : IsOpen V := by
    have hCopen : IsOpen C :=
      (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
    exact hCopen.connectedComponentIn
  have hball_nhds : Metric.ball z η ∈ 𝓝 z := Metric.ball_mem_nhds z hη
  obtain ⟨y, hyball, hyV⟩ :=
    (mem_closure_iff_nhds.mp (by simpa [V] using hzcl)) (Metric.ball z η) hball_nhds
  have hyclS : y ∈ closure (Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane}) :=
    ball_subset_closure_ball_inter_rotated_translated_slitPlane v z hv hyball
  have hV_nhds : V ∈ 𝓝 y := hVopen.mem_nhds (by simpa [V] using hyV)
  obtain ⟨x, hxV, hxS⟩ := (mem_closure_iff_nhds.mp hyclS) V hV_nhds
  exact ⟨x, hxS, by simpa [V] using hxV⟩

lemma rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_mem_closure
    {c₁ c₂ u v z : ℂ} {η : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 < η)
    (hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hsubC : Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
      ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ)) :
    Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
      connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  exact rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_nonempty_inter
    hv hη hsubC (rotatedSlit_inter_connectedComponentIn_of_mem_closure hv hη hzcl)

lemma exists_Icc_crosscut_to_commonComponent_of_rotatedSlit_subset_commonExterior_of_mem_closure
    {c₁ c₂ u v z : ℂ} {η : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 < η)
    (hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hsubC : Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
      ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ)) :
    ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) ε,
        γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  exact exists_Icc_crosscut_of_rotated_slit_subset hv hη
    (rotatedSlit_subset_connectedComponentIn_of_subset_commonExterior_of_mem_closure
      hv hη hzcl hsubC)

end Bottcher

namespace Bottcher

/-- `RotatedSlitGood` for the active filled Julia set plus openness of the other basin gives a rotated
slit sector in the common exterior. -/
lemma exists_rotatedSlit_subset_commonExterior_of_rotatedSlitGood_offOther
    {c₁ c₂ z : ℂ} (hgood : RotatedSlitGood c₁ z) (hzoff : z ∈ (filledJulia c₂)ᶜ) :
    ∃ (v : ℂ) (η : ℝ), ‖v‖ = 1 ∧ 0 < η ∧
      Metric.ball z η ∩ {w | v * (w - z) ∈ Complex.slitPlane} ⊆
        ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) := by
  rcases hgood with ⟨v, rTip, hv, hrTip, hslit⟩
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl z hzoff
  let η : ℝ := min rTip rOther
  have hη : 0 < η := lt_min hrTip hrOther
  have hη_tip : η ≤ rTip := min_le_left rTip rOther
  have hη_other : η ≤ rOther := min_le_right rTip rOther
  refine ⟨v, η, hv, hη, ?_⟩
  intro w hw
  have hw₁ : w ∈ Metric.ball z η ∩ (filledJulia c₁)ᶜ := hslit η hη hη_tip hw
  exact ⟨hw₁.2, hother (Metric.ball_subset_ball hη_other hw₁.1)⟩

lemma exists_Icc_crosscut_to_commonComponent_of_rotatedSlitGood_offOther_mem_closure
    {c₁ c₂ u z : ℂ}
    (hgood : RotatedSlitGood c₁ z) (hzoff : z ∈ (filledJulia c₂)ᶜ)
    (hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) :
    ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧ γ 0 = z ∧
      ∀ t ∈ Set.Ioc (0 : ℝ) ε,
        γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  obtain ⟨v, η, hv, hη, hsubC⟩ :=
    exists_rotatedSlit_subset_commonExterior_of_rotatedSlitGood_offOther hgood hzoff
  exact exists_Icc_crosscut_to_commonComponent_of_rotatedSlit_subset_commonExterior_of_mem_closure
    hv hη hzcl hsubC

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

lemma localIccAccess_of_rotatedSlitGood_offOther_closure
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (haccess : ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      RotatedSlitGood c₁ z ∧
        z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) :
    ∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
      z ∈ (filledJulia c₂)ᶜ →
      ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ ContinuousOn γ (Set.Icc (0 : ℝ) ε) ∧
        γ 0 = z ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) ε,
          γ t ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  intro z hzball hzfront hzoff
  obtain ⟨hgood, hzcl⟩ := haccess z hzball hzfront hzoff
  exact exists_Icc_crosscut_to_commonComponent_of_rotatedSlitGood_offOther_mem_closure
    hgood hzoff hzcl

/-- **Connected q62-facing endpoint from local `RotatedSlitGood` access and exact-slice
parametrization.**  This removes explicit slit-sector/crosscut construction from the q62 input: every
local frontier/off-other point only has to be `RotatedSlitGood` and in the selected common-component
closure. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceRotatedSlitGoodAccessParamLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hlocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₁) →
          z ∈ (filledJulia c₂)ᶜ →
          RotatedSlitGood c₁ z ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hlocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∃ (R : ℝ) (γslice : ℝ → ℂ), 0 < R ∧
        (∀ z, z ∈ Metric.ball p R → z ∈ frontier (filledJulia c₂) →
          z ∈ (filledJulia c₁)ᶜ →
          RotatedSlitGood c₂ z ∧
            z ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
        ContinuousOn γslice (Set.Icc (0 : ℝ) 1) ∧
        MapsTo γslice (Set.Icc (0 : ℝ) 1)
          (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
        (∀ z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R,
          ∃ t ∈ Set.Icc (0 : ℝ) 1, γslice t = z))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSliceContinuousIccAccessParamLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, haccess, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₁ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    exact localIccAccess_of_rotatedSlitGood_offOther_closure haccess
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨R, γslice, hR, haccess, hγcont, hγmaps, hγsurj⟩ :=
      hlocal₂ p u huU hpfront hpoff hpcl
    refine ⟨R, γslice, hR, ?_, hγcont, hγmaps, hγsurj⟩
    exact localIccAccess_of_rotatedSlitGood_offOther_closure haccess

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A noncountable set is automatically nontrivial.  This is the small cardinal bridge needed by the
local exact-slice route: once the geometric side proves a local slice is not countable, the Moore
component endpoint only needs local preconnectedness. -/
lemma Set.Nontrivial.of_not_countable {S : Set ℂ} (h : ¬ S.Countable) : S.Nontrivial := by
  by_contra hnon
  exact h ((Set.not_nontrivial_iff.mp hnon).countable)

lemma exists_second_point_in_commonComponentFrontierSlice_component_of_local_preconnected_not_countable
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hR : 0 < R) (hpS : p ∈ CommonComponentFrontierSlice c₁ c₂ u)
    (hpre : IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (hnotCount : ¬ (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Countable) :
    ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p := by
  exact exists_second_point_in_commonComponentFrontierSlice_component_of_local_preconnected_nontrivial
    hR hpS hpre (Set.Nontrivial.of_not_countable hnotCount)

/-- **Connected q62-facing endpoint from locally noncountable exact slices.**  This is the Lean-facing
piece of Grok's noncountability route: after local preconnectedness is known, the geometric side can
prove local noncountability instead of explicitly choosing a second point or parametrizing the slice. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedNotCountableLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        ∃ R : ℝ, 0 < R ∧
          IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) ∧
          ¬ (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Countable)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        ∃ R : ℝ, 0 < R ∧
          IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R) ∧
          ¬ (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R).Countable)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedNontrivialLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · obtain ⟨R, hR, hpre, hnotCount⟩ := hlocal
      exact Or.inr ⟨R, hR, hpre, Set.Nontrivial.of_not_countable hnotCount⟩
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · obtain ⟨R, hR, hpre, hnotCount⟩ := hlocal
      exact Or.inr ⟨R, hR, hpre, Set.Nontrivial.of_not_countable hnotCount⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Localized form of `not_countable_commonComponent_closure_slice_of_localTip`: the same selector
argument actually produces noncountability inside a definite ball around the base closure point. -/
theorem exists_not_countable_local_commonComponentFrontierSlice_of_localTip
    {c₁ c₂ p u : ℂ}
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (_huU : u ∈ U)
    (hpfront : p ∈ frontier (filledJulia c₁))
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (htip : LocalTipGood c₁ p) :
    ∃ R : ℝ, 0 < R ∧
      ¬ (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Countable := by
  rcases htip with ⟨rTip, hrTip, htip⟩
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  set R : ℝ := min rTip rOther with hRdef
  have hR : 0 < R := by rw [hRdef]; exact lt_min hrTip hrOther
  have hR_le_tip : R ≤ rTip := by rw [hRdef]; exact min_le_left _ _
  have hR_le_other : R ≤ rOther := by rw [hRdef]; exact min_le_right _ _
  have hsectorV : Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆ V := by
    set W : Set ℂ := Metric.ball p R ∩ (filledJulia c₁)ᶜ with hW
    have hWc : IsPreconnected W := by simpa [W] using htip R hR hR_le_tip
    have hWC : W ⊆ C := by
      intro z hz
      exact ⟨hz.2, hother (Metric.ball_subset_ball hR_le_other hz.1)⟩
    have hpclV : p ∈ closure V := by simpa [V, C] using hpcl
    have hmeet : (Metric.ball p R ∩ V).Nonempty := by
      rw [_root_.mem_closure_iff] at hpclV
      exact hpclV (Metric.ball p R) isOpen_ball (Metric.mem_ball_self hR)
    obtain ⟨y, hyball, hyV⟩ := hmeet
    have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
    have hWsubCompY : W ⊆ connectedComponentIn C y :=
      hWc.subset_connectedComponentIn hyW hWC
    have hcomp : connectedComponentIn C y = V := by
      have h := connectedComponentIn_eq (by simpa [V] using hyV)
      simpa [V] using h.symm
    intro z hz
    exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
  have hpΩ : p ∈ interior ((filledJulia c₂)ᶜ) :=
    mem_interior_iff_mem_nhds.mpr ((isClosed_filledJulia c₂).isOpen_compl.mem_nhds hpoff)
  obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
    exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
      (U := V) (Ω := (filledJulia c₂)ᶜ) (c₁ := c₁) (c₂ := c₂)
      hKconn hempty (mem_filledJulia_of_frontier hpfront) hpΩ hR hrOther hsectorV hother
  refine ⟨R, hR, ?_⟩
  intro hcount
  obtain ⟨z, hzS, _hzΩ, hznot⟩ := havoid
    (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R) hcount
  obtain ⟨hzball, hzfront, hzoff⟩ := hSlocal z hzS
  have hzcl : z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
    simpa [V, C] using hclosure z hzS
  exact hznot ⟨⟨hzfront, hzoff, hzcl⟩, hzball⟩

/-- **Connected q62-facing endpoint from base local tips plus all-radius local exact-slice
preconnectedness.**  The local-tip selector supplies a radius where the exact slice is noncountable;
all-radius preconnectedness supplies the matching preconnectedness at that same radius. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipEveryRadiusPreconnectedLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        LocalTipGood c₁ p ∧
          ∀ R : ℝ, 0 < R →
            IsPreconnected (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R))
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        LocalTipGood c₂ p ∧
          ∀ R : ℝ, 0 < R →
            IsPreconnected (CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R))
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalExactSlicePreconnectedNotCountableLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · rcases hlocal with ⟨htip, hpreAll⟩
      obtain ⟨R, hR, hnotCount⟩ :=
        exists_not_countable_local_commonComponentFrontierSlice_of_localTip
          (U := U) hKconn₁ hempty₁ huU hpfront hpoff hpcl htip
      exact Or.inr ⟨R, hR, hpreAll R hR, hnotCount⟩
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · rcases hlocal with ⟨htip, hpreAll⟩
      obtain ⟨R, hR, hnotCount⟩ :=
        exists_not_countable_local_commonComponentFrontierSlice_of_localTip
          (U := U) hKconn₂ hempty₂ huU hpfront hpoff hpcl htip
      exact Or.inr ⟨R, hR, hpreAll R hR, hnotCount⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A noncountable local exact slice contained in the global exact-slice component of `p` gives the
Moore second point directly, bypassing local preconnectedness. -/
lemma exists_second_point_in_commonComponentFrontierSlice_component_of_local_not_countable_subset_component
    {c₁ c₂ u p : ℂ} {R : ℝ}
    (hnotCount : ¬ (CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R).Countable)
    (hsubComp : CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ⊆
      connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p) :
    ∃ q, q ∈ connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p ∧ q ≠ p := by
  obtain ⟨q, hq, hqne⟩ := (Set.Nontrivial.of_not_countable hnotCount).exists_ne p
  exact ⟨q, hsubComp hq, hqne⟩

/-- **Connected q62-facing endpoint from base local tips plus local component saturation.**  This is
Grok's component-saturation bypass in Lean form: `LocalTipGood` supplies a noncountable local exact
slice, and saturation of that local slice into the component of `p` supplies the Moore two-arm witness
directly, without proving preconnectedness of the exact slice. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipEveryRadiusComponentSaturationLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hdich₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v p) ∨
        LocalTipGood c₁ p ∧
          ∀ R : ℝ, 0 < R →
            CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ⊆
              connectedComponentIn (CommonComponentFrontierSlice c₁ c₂ u) p)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hdich₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      (∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v p) ∨
        LocalTipGood c₂ p ∧
          ∀ R : ℝ, 0 < R →
            CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R ⊆
              connectedComponentIn (CommonComponentFrontierSlice c₂ c₁ u) p)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberSliceComponentLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₁ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · rcases hlocal with ⟨htip, hsat⟩
      obtain ⟨R, hR, hnotCount⟩ :=
        exists_not_countable_local_commonComponentFrontierSlice_of_localTip
          (U := U) hKconn₁ hempty₁ huU hpfront hpoff hpcl htip
      exact Or.inr
        (exists_second_point_in_commonComponentFrontierSlice_component_of_local_not_countable_subset_component
          hnotCount (hsat R hR))
  · intro p u huU hpfront hpoff hpcl
    rcases hdich₂ p u huU hpfront hpoff hpcl with hray | hlocal
    · exact Or.inl hray
    · rcases hlocal with ⟨htip, hsat⟩
      obtain ⟨R, hR, hnotCount⟩ :=
        exists_not_countable_local_commonComponentFrontierSlice_of_localTip
          (U := U) hKconn₂ hempty₂ huU hpfront hpoff hpcl htip
      exact Or.inr
        (exists_second_point_in_commonComponentFrontierSlice_component_of_local_not_countable_subset_component
          hnotCount (hsat R hR))

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A base local tip plus locally countably many non-tip points forces the global local-tip-good locus
inside the common-component frontier slice to be noncountable.  This is the localized version of the
older `LocalTipBadCountable` bridge: only the bad locus in the small ball selected by the base local tip
is needed. -/
lemma not_countable_commonComponentFrontierSlice_localTipGood_locus_of_baseLocalTip_localBadCountable
    {c₁ c₂ p u : ℂ}
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (huU : u ∈ U)
    (hpfront : p ∈ frontier (filledJulia c₁))
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (htip : LocalTipGood c₁ p)
    (hbadLocal : ∀ R : ℝ, 0 < R →
      ({z | z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ∧
          ¬ LocalTipGood c₁ z} : Set ℂ).Countable) :
    ¬ ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
          z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
          LocalTipGood c₁ z} : Set ℂ).Countable := by
  obtain ⟨R, hR, hnotCount⟩ :=
    exists_not_countable_local_commonComponentFrontierSlice_of_localTip
      (U := U) hKconn hempty huU hpfront hpoff hpcl htip
  intro hGoodCount
  apply hnotCount
  let Good : Set ℂ := {z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
          z ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
          LocalTipGood c₁ z}
  let BadLocal : Set ℂ := {z | z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ∧
          ¬ LocalTipGood c₁ z}
  have hGood : Good.Countable := by simpa [Good] using hGoodCount
  have hBad : BadLocal.Countable := by simpa [BadLocal] using hbadLocal R hR
  have hsub : CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ⊆ Good ∪ BadLocal := by
    intro z hz
    by_cases htipz : LocalTipGood c₁ z
    · left
      exact ⟨hz.1.1, hz.1.2.1, hz.1.2.2, htipz⟩
    · right
      exact ⟨hz, htipz⟩
  exact (hGood.union hBad).mono hsub

/-- **NoRelation from base local tips plus locally countably many non-tip points.**  This replaces the
older global bad-countability requirement by a local one: at every relevant base point, every small
exact slice ball has only countably many non-`LocalTipGood` points. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipLocalBadCountable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (hbadLocal₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      ∀ R : ℝ, 0 < R →
        ({z | z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ∧
            ¬ LocalTipGood c₁ z} : Set ℂ).Countable)
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (hbadLocal₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      ∀ R : ℝ, 0 < R →
        ({z | z ∈ CommonComponentFrontierSlice c₂ c₁ u ∩ Metric.ball p R ∧
            ¬ LocalTipGood c₂ z} : Set ℂ).Countable) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipGoodLocus
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hempty₁ hempty₂ ?_ ?_
  · intro p u huU hpfront hpoff hpcl
    exact not_countable_commonComponentFrontierSlice_localTipGood_locus_of_baseLocalTip_localBadCountable
      (U := U) hKconn₁ hempty₁ huU hpfront hpoff hpcl
      (hbaseTip₁ p u huU hpfront hpoff hpcl)
      (hbadLocal₁ p u huU hpfront hpoff hpcl)
  · intro p u huU hpfront hpoff hpcl
    exact not_countable_commonComponentFrontierSlice_localTipGood_locus_of_baseLocalTip_localBadCountable
      (U := U) hKconn₂ hempty₂ huU hpfront hpoff hpcl
      (hbaseTip₂ p u huU hpfront hpoff hpcl)
      (hbadLocal₂ p u huU hpfront hpoff hpcl)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- A countable injective code on the non-ray bad locus counts the local non-`LocalTipGood` points in
any exact-slice ball.  The only implication used is `¬ LocalTipGood -> ¬ local nonpositive ray`. -/
lemma countable_local_nonLocalTip_of_injOn_nonpositiveRayCode
    {κ : Type*} [Countable κ] {c₁ c₂ u p : ℂ} {R : ℝ}
    (loopOrderCode : ℂ → κ)
    (hloopOrderInj : InjOn loopOrderCode
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ)) :
    ({z | z ∈ CommonComponentFrontierSlice c₁ c₂ u ∩ Metric.ball p R ∧
        ¬ LocalTipGood c₁ z} : Set ℂ).Countable := by
  refine countable_of_injOn_countable_code loopOrderCode ?_
  intro x hx y hy hxy
  exact hloopOrderInj
    ⟨hx.1.1.1, hx.1.1.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hx.2⟩
    ⟨hy.1.1.1, hy.1.1.2.1, not_exists_localNonpositiveRayConfined_of_not_localTipGood hy.2⟩
    hxy

/-- **NoRelation from base local tips plus injective local loop/order codes.**  This combines the
localized local-tip noncountability bridge with the existing loop-order countability primitive: the
remaining geometric input is that each base point is `LocalTipGood`, while the combinatorial input is a
countable injective code on the non-ray frontier/off-other locus. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipLocalLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneBaseTip : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
    letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneBaseTip
  letI := (ratfuncToMero U hUo hUc hUneBaseTip hUinf).toAlgebra
  refine noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBaseLocalTipLocalBadCountable
    hUo hUc hUneBaseTip hUinf c₁ c₂ hU₁ hU₂ hne hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseTip₁ ?_
    hbaseTip₂ ?_
  · intro p u huU hpfront hpoff hpcl R hR
    exact countable_local_nonLocalTip_of_injOn_nonpositiveRayCode
      (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (R := R) loopOrderCode₁ hloopOrderInj₁
  · intro p u huU hpfront hpoff hpcl R hR
    exact countable_local_nonLocalTip_of_injOn_nonpositiveRayCode
      (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (R := R) loopOrderCode₂ hloopOrderInj₂

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Compact quasicomponent separation.  In a compact Hausdorff space, if a compact set misses the
connected component of `x`, then some clopen neighbourhood of `x` already misses that compact set. -/
lemma exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
    {α : Type*} [TopologicalSpace α] [T2Space α] [CompactSpace α]
    {F : Set α} {x : α}
    (hF : IsCompact F) (hdisj : Disjoint F (connectedComponent x)) :
    ∃ E : Set α, IsClopen E ∧ x ∈ E ∧ Disjoint F E := by
  have hCeq := connectedComponent_eq_iInter_isClopen (X := α) x
  have hEmpty : F ∩ (⋂ s : {s : Set α // IsClopen s ∧ x ∈ s}, (s : Set α)) = ∅ := by
    rw [← hCeq]
    exact disjoint_iff_inter_eq_empty.mp hdisj
  obtain ⟨u, hu⟩ := hF.elim_finite_subfamily_closed
    (fun s : {s : Set α // IsClopen s ∧ x ∈ s} => (s : Set α))
    (fun s => s.2.1.1) hEmpty
  let E : Set α := ⋂ s ∈ u, (s : Set α)
  refine ⟨E, ?_, ?_, ?_⟩
  · exact isClopen_biInter_finset (s := u) (fun s _ => s.2.1)
  · simp [E, fun s : {s : Set α // IsClopen s ∧ x ∈ s} => s.2.2]
  · rw [Set.disjoint_iff_inter_eq_empty]
    simpa [E] using hu

/-- A clopen subset of a closed ball that avoids the boundary sphere is clopen after embedding back
into the ambient metric space.  This is the clopen-lifting step in boundary bumping. -/
lemma isClopen_image_closedBall_subtype_of_isClopen_disjoint_sphere
    {α : Type*} [MetricSpace α] {p : α} {r : ℝ}
    {E : Set (Metric.closedBall p r)}
    (hE : IsClopen E)
    (hdisj : Disjoint E
      ({x : Metric.closedBall p r | (x : α) ∈ Metric.sphere p r} :
        Set (Metric.closedBall p r))) :
    IsClopen (((↑) : Metric.closedBall p r → α) '' E : Set α) := by
  constructor
  · exact Metric.isClosed_closedBall.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hE.1
  · rcases isOpen_induced_iff.mp hE.2 with ⟨O, hOopen, hOeq⟩
    have himg_eq : ((↑) : Metric.closedBall p r → α) '' E = O ∩ Metric.ball p r := by
      ext z
      constructor
      · rintro ⟨zQ, hzQE, rfl⟩
        have hzO : (zQ : α) ∈ O := by
          change zQ ∈ ((↑) : Metric.closedBall p r → α) ⁻¹' O
          rw [hOeq]
          exact hzQE
        have hznotSphere : ¬ (zQ : α) ∈ Metric.sphere p r := by
          intro hzSphere
          exact Set.disjoint_left.mp hdisj hzQE hzSphere
        have hzball : (zQ : α) ∈ Metric.ball p r := by
          rw [Metric.mem_ball]
          have hzclosed : dist (zQ : α) p ≤ r := zQ.2
          have hzne : dist (zQ : α) p ≠ r := by
            intro hdist
            exact hznotSphere (by simpa [Metric.mem_sphere] using hdist)
          exact lt_of_le_of_ne hzclosed hzne
        exact ⟨hzO, hzball⟩
      · intro hz
        have hzclosed : z ∈ Metric.closedBall p r := Metric.ball_subset_closedBall hz.2
        refine ⟨⟨z, hzclosed⟩, ?_, rfl⟩
        change (⟨z, hzclosed⟩ : Metric.closedBall p r) ∈ E
        rw [← hOeq]
        exact hz.1
    rw [himg_eq]
    exact hOopen.inter isOpen_ball

/-- Boundary bumping for compact preconnected metric spaces.  Every positive closed ball around a
point contains a nontrivial preconnected subset through that point.  If the whole space is already in
the closed ball, take the whole space; otherwise the component in the closed ball bumps into the
sphere, proved via compact quasicomponents. -/
lemma exists_preconnected_nontrivial_subset_closedBall_of_compact_preconnected
    {α : Type*} [MetricSpace α] [CompactSpace α] [Nontrivial α]
    (hpre : IsPreconnected (Set.univ : Set α)) (p : α) {r : ℝ} (hr : 0 < r) :
    ∃ A : Set α, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧ A ⊆ Metric.closedBall p r := by
  by_cases hsub : (Set.univ : Set α) ⊆ Metric.closedBall p r
  · exact ⟨Set.univ, hpre, Set.mem_univ p, Set.nontrivial_univ, hsub⟩
  · have hnotforall : ¬ ∀ y : α, y ∈ Metric.closedBall p r := by
      intro hall
      exact hsub (fun y _ => hall y)
    push Not at hnotforall
    obtain ⟨y, hyout⟩ := hnotforall
    let Q : Set α := Metric.closedBall p r
    have hpQ : p ∈ Q := by simpa [Q, Metric.mem_closedBall] using le_of_lt hr
    let C : Set α := connectedComponentIn Q p
    have hCpre : IsPreconnected C := by
      simpa [C] using (isPreconnected_connectedComponentIn (x := p) (F := Q))
    have hpC : p ∈ C := by simpa [C] using mem_connectedComponentIn hpQ
    have hCsubQ : C ⊆ Q := by simpa [C] using connectedComponentIn_subset Q p
    have hCnot : ¬ C.Subsingleton := by
      intro hCsub
      have hQcompact : IsCompact Q := by simpa [Q] using (isCompact_closedBall p r)
      haveI : CompactSpace Q := isCompact_iff_compactSpace.mp hQcompact
      let pQ : Q := ⟨p, hpQ⟩
      let FQ : Set Q := {x : Q | (x : α) ∈ Metric.sphere p r}
      have hFQclosed : IsClosed FQ := by
        exact Metric.isClosed_sphere.preimage continuous_subtype_val
      have hFQcompact : IsCompact FQ := hFQclosed.isCompact
      have hdisjFcomp : Disjoint FQ (connectedComponent pQ) := by
        rw [Set.disjoint_left]
        intro z hzF hzC
        have hzCimg : (z : α) ∈ C := by
          have : (z : α) ∈ connectedComponentIn Q p := by
            rw [connectedComponentIn_eq_image hpQ]
            exact ⟨z, hzC, rfl⟩
          simpa [C] using this
        have hzp : (z : α) = p := hCsub hzCimg hpC
        have hdist : dist (z : α) p = r := by simpa [Metric.mem_sphere] using hzF
        rw [hzp, dist_self] at hdist
        linarith
      obtain ⟨E, hEclopen, hpE, hdisjFE⟩ :=
        exists_isClopen_neighborhood_disjoint_compact_of_disjoint_connectedComponent
          (F := FQ) (x := pQ) hFQcompact hdisjFcomp
      have hEclopenα : IsClopen (((↑) : Q → α) '' E : Set α) := by
        exact isClopen_image_closedBall_subtype_of_isClopen_disjoint_sphere
          (p := p) (r := r) hEclopen hdisjFE.symm
      have hpEα : p ∈ (((↑) : Q → α) '' E : Set α) := ⟨pQ, hpE, rfl⟩
      have hAllE : (Set.univ : Set α) ⊆ ((↑) : Q → α) '' E :=
        hpre.subset_isClopen hEclopenα ⟨p, Set.mem_univ p, hpEα⟩
      have hyE : y ∈ ((↑) : Q → α) '' E := hAllE (Set.mem_univ y)
      obtain ⟨yQ, _hyQE, hyval⟩ := hyE
      have hyclosed : y ∈ Metric.closedBall p r := by simpa [Q, hyval] using yQ.2
      exact hyout hyclosed
    exact ⟨C, hCpre, hpC, Set.not_subsingleton_iff.mp hCnot, hCsubQ⟩

/-- Filled-Julia boundary-bumping core.  For a connected filled Julia set, every positive closed ball
around a frontier point contains a nontrivial preconnected continuum through that point inside the
filled Julia set. -/
lemma filledJulia_boundaryBumpingCore_of_preconnected
    {c p : ℂ}
    (hKconn : IsPreconnected (filledJulia c))
    (hpfront : p ∈ frontier (filledJulia c)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ filledJulia c ∧ A ⊆ Metric.closedBall p ρ := by
  let K : Set ℂ := filledJulia c
  have hpK : p ∈ K := by simpa [K] using mem_filledJulia_of_frontier hpfront
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (by simpa [K] using isCompact_filledJulia c)
  haveI : Nontrivial K := by
    exact Set.Nontrivial.coe_sort (by simpa [K] using filledJulia_nontrivial c)
  have hpreK : IsPreconnected (Set.univ : Set K) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    simpa [K, Set.image_univ, Subtype.range_coe] using hKconn
  obtain ⟨A₀, hA₀pre, hpA₀, hA₀non, hA₀ρ⟩ :=
    exists_preconnected_nontrivial_subset_closedBall_of_compact_preconnected
      (α := K) hpreK ⟨p, hpK⟩ hρ
  let A : Set ℂ := ((↑) : K → ℂ) '' A₀
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [A] using (IsInducing.subtypeVal.isPreconnected_image.mpr hA₀pre)
  · exact ⟨⟨p, hpK⟩, hpA₀, rfl⟩
  · rcases hA₀non with ⟨x, hx, y, hy, hxy⟩
    refine ⟨(x : ℂ), ⟨x, hx, rfl⟩, (y : ℂ), ⟨y, hy, rfl⟩, ?_⟩
    intro hxyval
    exact hxy (Subtype.ext hxyval)
  · rintro z ⟨x, _hx, rfl⟩
    exact x.2
  · rintro z ⟨x, hx, rfl⟩
    have hxρ := hA₀ρ hx
    change dist (x : ℂ) p ≤ ρ
    simpa [Metric.mem_closedBall] using hxρ

/-- Local-tip absorption of the punctured exterior ball into the selected common exterior component.
This is the Lean form of the first half of the boundary-slice reduction: once `p` lies in the
closure of a common exterior component and the active exterior is locally preconnected at `p`, a
small punctured active-basin ball cannot split across different common exterior components. -/
lemma localTipGood_commonExterior_ball_subset_component
    {c₁ c₂ p u : ℂ}
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (htip : LocalTipGood c₁ p) :
    ∃ R : ℝ, 0 < R ∧
      Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆
        connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u ∧
      Metric.ball p R ⊆ (filledJulia c₂)ᶜ := by
  rcases htip with ⟨rTip, hrTip, htip⟩
  obtain ⟨rOther, hrOther, hother⟩ :=
    Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hVsubC : V ⊆ C := by
    simpa [V] using connectedComponentIn_subset C u
  have hVbasin₁ : V ⊆ (filledJulia c₁)ᶜ := fun z hz => (hVsubC hz).1
  set R : ℝ := min rTip rOther with hRdef
  have hR : 0 < R := by rw [hRdef]; exact lt_min hrTip hrOther
  have hR_le_tip : R ≤ rTip := by rw [hRdef]; exact min_le_left _ _
  have hR_le_other : R ≤ rOther := by rw [hRdef]; exact min_le_right _ _
  have hlocalV : Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆ V := by
    set W : Set ℂ := Metric.ball p R ∩ (filledJulia c₁)ᶜ with hW
    have hWc : IsPreconnected W := by simpa [W] using htip R hR hR_le_tip
    have hWC : W ⊆ C := by
      intro z hz
      exact ⟨hz.2, hother (Metric.ball_subset_ball hR_le_other hz.1)⟩
    have hpclV : p ∈ closure V := by simpa [V, C] using hpcl
    have hmeet : (Metric.ball p R ∩ V).Nonempty := by
      rw [_root_.mem_closure_iff] at hpclV
      exact hpclV (Metric.ball p R) isOpen_ball (Metric.mem_ball_self hR)
    obtain ⟨y, hyball, hyV⟩ := hmeet
    have hyW : y ∈ W := ⟨hyball, hVbasin₁ hyV⟩
    have hWsubCompY : W ⊆ connectedComponentIn C y :=
      hWc.subset_connectedComponentIn hyW hWC
    have hcomp : connectedComponentIn C y = V := by
      have h := connectedComponentIn_eq (by simpa [V] using hyV)
      simpa [V] using h.symm
    intro z hz
    exact hcomp ▸ hWsubCompY (by simpa [W] using hz)
  refine ⟨R, hR, by simpa [V, C] using hlocalV, ?_⟩
  intro z hz
  exact hother (Metric.ball_subset_ball hR_le_other hz)

/-- Closed-ball shrink of `localTipGood_commonExterior_ball_subset_component`.  This packages the
radius choice used by the boundary-bumping route: choose a smaller closed ball for the continuum while
keeping a larger open ball whose punctured active exterior is in the selected common component. -/
lemma localTipGood_commonExterior_closedBall_shrink
    {c₁ c₂ p u : ℂ}
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (htip : LocalTipGood c₁ p) :
    ∃ (ρ R : ℝ), 0 < ρ ∧ ρ < R ∧
      Metric.closedBall p ρ ⊆ (filledJulia c₂)ᶜ ∧
      Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆
        connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u := by
  obtain ⟨R, hR, hlocalV, hoffBall⟩ :=
    localTipGood_commonExterior_ball_subset_component
      (c₁ := c₁) (c₂ := c₂) (p := p) (u := u) hpoff hpcl htip
  refine ⟨R / 2, R, half_pos hR, half_lt_self hR, ?_, hlocalV⟩
  intro z hz
  exact hoffBall (Metric.closedBall_subset_ball (half_lt_self hR) hz)

/-- Boundary-bumping reduction, local carrier form.  Once a paper/topology argument supplies a
nontrivial preconnected continuum `A` inside a small closed ball of `K_c1`, this lemma proves that the
continuum is already a two-arm germ in the exact common-component frontier slice.  The only dynamical
input is that the surrounding punctured basin ball lies in the selected common exterior component. -/
lemma commonComponentFrontierSlice_preconnected_germ_of_filledJulia_closedBall_germ
    {c₁ c₂ u p : ℂ} {A : Set ℂ} {ρ R : ℝ}
    (hempty : interior (filledJulia c₁) = ∅)
    (hApre : IsPreconnected A) (hpA : p ∈ A) (hAnon : A.Nontrivial)
    (hAK : A ⊆ filledJulia c₁)
    (hAρ : A ⊆ Metric.closedBall p ρ)
    (hρR : ρ < R)
    (hoff : Metric.closedBall p ρ ⊆ (filledJulia c₂)ᶜ)
    (hlocalV : Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆
      connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) :
    ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
      A ⊆ CommonComponentFrontierSlice c₁ c₂ u := by
  refine ⟨A, hApre, hpA, hAnon, ?_⟩
  intro x hxA
  have hxK : x ∈ filledJulia c₁ := hAK hxA
  have hxfront : x ∈ frontier (filledJulia c₁) :=
    mem_frontier_of_mem_filledJulia_emptyInterior hempty hxK
  have hxoff : x ∈ (filledJulia c₂)ᶜ := hoff (hAρ hxA)
  have hxballR : x ∈ Metric.ball p R := by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hAρ hxA) hρR
  have hxnotint : x ∉ interior (filledJulia c₁) := by
    rw [hempty]
    simp
  have hxclKc : x ∈ closure (filledJulia c₁)ᶜ := by
    rwa [closure_compl]
  have hxclV : x ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
    rw [mem_closure_iff_nhds] at hxclKc ⊢
    intro N hN
    have hballN : Metric.ball p R ∩ N ∈ 𝓝 x :=
      inter_mem (isOpen_ball.mem_nhds hxballR) hN
    obtain ⟨y, hyBN, hyKc⟩ := hxclKc (Metric.ball p R ∩ N) hballN
    exact ⟨y, hyBN.2, hlocalV ⟨hyBN.1, hyKc⟩⟩
  exact ⟨hxfront, hxoff, hxclV⟩

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Connected q62-facing endpoint from boundary-bumping continua.**  This is the Lean interface for
the boundary-bumping route: for each exact common-component frontier point, the geometric side supplies
a nontrivial preconnected continuum inside a small closed ball of the active filled Julia set; the
surrounding punctured basin ball is contained in the selected common exterior component.  The helper
`commonComponentFrontierSlice_preconnected_germ_of_filledJulia_closedBall_germ` turns that continuum
into a two-arm germ in the exact slice, and the existing loop/order code handles the non-ray bad locus. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBoundaryBumpingContinuumLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbump₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
        ∃ (A : Set ℂ) (ρ R : ℝ),
          IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
          A ⊆ filledJulia c₁ ∧ A ⊆ Metric.closedBall p ρ ∧ ρ < R ∧
          Metric.closedBall p ρ ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball p R ∩ (filledJulia c₁)ᶜ ⊆
            connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hbump₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
        ∃ (A : Set ℂ) (ρ R : ℝ),
          IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
          A ⊆ filledJulia c₂ ∧ A ⊆ Metric.closedBall p ρ ∧ ρ < R ∧
          Metric.closedBall p ρ ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball p R ∩ (filledJulia c₂)ᶜ ⊆
            connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffMooreFiberSliceComponentLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    right
    obtain ⟨A, ρ, R, hApre, hpA, hAnon, hAK, hAρ, hρR, hoff, hlocalV⟩ :=
      hbump₁ p u huU hpfront hpoff hpcl
    obtain ⟨B, hBpre, hpB, hBnon, hBsub⟩ :=
      commonComponentFrontierSlice_preconnected_germ_of_filledJulia_closedBall_germ
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (A := A) (ρ := ρ) (R := R)
        hempty₁ hApre hpA hAnon hAK hAρ hρR hoff hlocalV
    exact exists_second_point_in_commonComponentFrontierSlice_component_of_not_subsingleton
      (c₁ := c₁) (c₂ := c₂) (u := u) (p := p)
      (commonComponentFrontierSlice_component_not_subsingleton_of_preconnected_nontrivial_subset
        (c₁ := c₁) (c₂ := c₂) (u := u) (p := p) (A := B) hBpre hpB hBnon hBsub)
  · intro p u huU hpfront hpoff hpcl
    right
    obtain ⟨A, ρ, R, hApre, hpA, hAnon, hAK, hAρ, hρR, hoff, hlocalV⟩ :=
      hbump₂ p u huU hpfront hpoff hpcl
    obtain ⟨B, hBpre, hpB, hBnon, hBsub⟩ :=
      commonComponentFrontierSlice_preconnected_germ_of_filledJulia_closedBall_germ
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (A := A) (ρ := ρ) (R := R)
        hempty₂ hApre hpA hAnon hAK hAρ hρR hoff hlocalV
    exact exists_second_point_in_commonComponentFrontierSlice_component_of_not_subsingleton
      (c₁ := c₂) (c₂ := c₁) (u := u) (p := p)
      (commonComponentFrontierSlice_component_not_subsingleton_of_preconnected_nontrivial_subset
        (c₁ := c₂) (c₂ := c₁) (u := u) (p := p) (A := B) hBpre hpB hBnon hBsub)

/-- **Connected q62-facing endpoint from local-tip absorption plus a pure boundary-bumping core.**
This is the sharper boundary-slice route: `LocalTipGood` supplies the common-component exterior
absorption and the geometric/topological side only has to produce, for every small radius, a
nontrivial preconnected continuum through the base point inside the active filled Julia set. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingCoreLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (hbumpCore₁ : ∀ p ρ, 0 < ρ → p ∈ frontier (filledJulia c₁) →
      ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
        A ⊆ filledJulia c₁ ∧ A ⊆ Metric.closedBall p ρ)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (hbumpCore₂ : ∀ p ρ, 0 < ρ → p ∈ frontier (filledJulia c₂) →
      ∃ A : Set ℂ, IsPreconnected A ∧ p ∈ A ∧ A.Nontrivial ∧
        A ⊆ filledJulia c₂ ∧ A ⊆ Metric.closedBall p ρ)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffBoundaryBumpingContinuumLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ ?_ loopOrderCode₁
    hloopOrderInj₁ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨ρ, R, hρ, hρR, hoff, hlocalV⟩ :=
      localTipGood_commonExterior_closedBall_shrink
        (c₁ := c₁) (c₂ := c₂) (p := p) (u := u) hpoff hpcl
        (hbaseTip₁ p u huU hpfront hpoff hpcl)
    obtain ⟨A, hApre, hpA, hAnon, hAK, hAρ⟩ := hbumpCore₁ p ρ hρ hpfront
    exact ⟨A, ρ, R, hApre, hpA, hAnon, hAK, hAρ, hρR, hoff, hlocalV⟩
  · intro p u huU hpfront hpoff hpcl
    obtain ⟨ρ, R, hρ, hρR, hoff, hlocalV⟩ :=
      localTipGood_commonExterior_closedBall_shrink
        (c₁ := c₂) (c₂ := c₁) (p := p) (u := u) hpoff hpcl
        (hbaseTip₂ p u huU hpfront hpoff hpcl)
    obtain ⟨A, hApre, hpA, hAnon, hAK, hAρ⟩ := hbumpCore₂ p ρ hρ hpfront
    exact ⟨A, ρ, R, hApre, hpA, hAnon, hAK, hAρ, hρR, hoff, hlocalV⟩

/-- **Connected q62-facing endpoint from local-tip absorption and proved boundary bumping.**  This
removes the `hbumpCore` assumption from
`q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingCoreLoopOrderCode`:
the required local continua are supplied by compact boundary bumping for the connected filled Julia
sets themselves. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingLoopOrderCode
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hbaseTip₁ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
      LocalTipGood c₁ p)
    (loopOrderCode₁ : ℂ → κ₁)
    (hloopOrderInj₁ : InjOn loopOrderCode₁
      ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ))
    (hbaseTip₂ : ∀ p u, u ∈ U →
      p ∈ frontier (filledJulia c₂) → p ∈ (filledJulia c₁)ᶜ →
      p ∈ closure (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u) →
      LocalTipGood c₂ p)
    (loopOrderCode₂ : ℂ → κ₂)
    (hloopOrderInj₂ : InjOn loopOrderCode₂
      ({z | z ∈ frontier (filledJulia c₂) ∧ z ∈ (filledJulia c₁)ᶜ ∧
        ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₂ v z} : Set ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUneMoore
  letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
  refine q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingCoreLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseTip₁ ?_
    loopOrderCode₁ hloopOrderInj₁ hbaseTip₂ ?_ loopOrderCode₂ hloopOrderInj₂
  · intro p ρ hρ hpfront
    exact filledJulia_boundaryBumpingCore_of_preconnected hKconn₁ hpfront hρ
  · intro p ρ hρ hpfront
    exact filledJulia_boundaryBumpingCore_of_preconnected hKconn₂ hpfront hρ

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- Remaining local-tip hypothesis for the boundary-bumping q62 route.  At every relevant common
frontier point, the active exterior is locally preconnected at the base point. -/
def CommonComponentBaseLocalTipHypothesis (U : Set ℂ) (c₁ c₂ : ℂ) : Prop :=
  ∀ p u, u ∈ U →
    p ∈ frontier (filledJulia c₁) → p ∈ (filledJulia c₂)ᶜ →
    p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) →
    LocalTipGood c₁ p

/-- Remaining loop/order coding hypothesis for the boundary-bumping q62 route.  The non-ray bad
frontier/off-other locus must inject into a countable code type. -/
def BoundaryBadNonRayLoopOrderCodeHypothesis {κ : Type*} [Countable κ]
    (c₁ c₂ : ℂ) (loopOrderCode : ℂ → κ) : Prop :=
  InjOn loopOrderCode
    ({z | z ∈ frontier (filledJulia c₁) ∧ z ∈ (filledJulia c₂)ᶜ ∧
      ¬ ∃ v : ℂ, ‖v‖ = 1 ∧ LocalNonpositiveRayConfined c₁ v z} : Set ℂ)

/-- The exact remaining symmetric hypotheses after compact boundary bumping has been proved. -/
def LocalTipBoundaryBumpingRemainingHypotheses (U : Set ℂ) (c₁ c₂ : ℂ)
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (loopOrderCode₁ : ℂ → κ₁) (loopOrderCode₂ : ℂ → κ₂) : Prop :=
  CommonComponentBaseLocalTipHypothesis U c₁ c₂ ∧
  BoundaryBadNonRayLoopOrderCodeHypothesis c₁ c₂ loopOrderCode₁ ∧
  CommonComponentBaseLocalTipHypothesis U c₂ c₁ ∧
  BoundaryBadNonRayLoopOrderCodeHypothesis c₂ c₁ loopOrderCode₂

/-- **Connected q62-facing endpoint stopped exactly at the remaining hypotheses.**  Compact boundary
bumping and local common-component absorption are internal; the only unresolved local inputs are the
base `LocalTipGood` condition and a countable injective code for the non-ray bad locus, symmetrically
for `c₁,c₂`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingRemainingHypotheses
    {κ₁ κ₂ : Type*} [Countable κ₁] [Countable κ₂]
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUneMoore : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (_hx₁ : c₁ ∉ Exceptional) (_hx₂ : c₂ ∉ Exceptional)
    (hG₁ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₁ hU₁))
    (hG₂ : letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β₁ β₂ : ℂ → ℂ)
    (hβ₁an : AnalyticOnNhd ℂ β₁ (filledJulia c₁)ᶜ)
    (hβ₁esc : ∀ z ∈ escapeOpen c₁, β₁ z = bottcherCoord c₁ z)
    (hβ₁mod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β₁ z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hβ₂an : AnalyticOnNhd ℂ β₂ (filledJulia c₂)ᶜ)
    (hβ₂esc : ∀ z ∈ escapeOpen c₂, β₂ z = bottcherCoord c₂ z)
    (hβ₂mod : ∀ z ∈ (filledJulia c₂)ᶜ, ‖β₂ z‖ = Real.exp (greenFunctionDyn c₂ z))
    (hKconn₁ : IsPreconnected (filledJulia c₁))
    (hKconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (loopOrderCode₁ : ℂ → κ₁) (loopOrderCode₂ : ℂ → κ₂)
    (hremaining : LocalTipBoundaryBumpingRemainingHypotheses U c₁ c₂ loopOrderCode₁ loopOrderCode₂) :
    haveI := isDomain_analyticSubring U hUo hUc hUneMoore
    letI := (ratfuncToMero U hUo hUc hUneMoore hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  rcases hremaining with ⟨hbaseTip₁, hloopOrderInj₁, hbaseTip₂, hloopOrderInj₂⟩
  exact q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_radicalSqfreeBad_countableAvoidance_symmDiffLocalTipBoundaryBumpingLoopOrderCode
    hUo hUc hUneMoore hUinf c₁ c₂ hU₁ hU₂ hne _hx₁ _hx₂ hG₁ hG₂ β₁ β₂ hβ₁an hβ₁esc
    hβ₁mod hβ₂an hβ₂esc hβ₂mod hKconn₁ hKconn₂ hempty₁ hempty₂ hbaseTip₁ loopOrderCode₁
    hloopOrderInj₁ hbaseTip₂ loopOrderCode₂ hloopOrderInj₂

end Bottcher

namespace Bottcher

noncomputable section

/-- A boundary point is straight-segment accessible from `V` if some interior point sees it by an
open segment contained in `V`. -/
def StraightSegmentAccessibleFrom (V : Set ℂ) (q : ℂ) : Prop :=
  ∃ x : ℂ, x ∈ V ∧ q ∈ frontier V ∧
    ∀ t : ℝ, 0 ≤ t → t < 1 → AffineMap.lineMap x q t ∈ V

/-- Accessible boundary points are dense in the boundary of any open subset of the plane. -/
lemma exists_straightSegmentAccessible_frontier_point_near
    {V : Set ℂ} (hVopen : IsOpen V) {p : ℂ} (hp : p ∈ frontier V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℂ, q ∈ frontier V ∧ dist q p < ε ∧ StraightSegmentAccessibleFrom V q := by
  have hpcl : p ∈ closure V := frontier_subset_closure hp
  have hpnot : p ∉ V := by
    intro hpV
    have hpint : p ∈ interior V := by simp [hVopen.interior_eq, hpV]
    exact hp.2 hpint
  let η : ℝ := ε / 3
  have hη : 0 < η := by positivity
  obtain ⟨x, hxV, hxp⟩ := Metric.mem_closure_iff.mp hpcl η hη
  have hVne : V ≠ univ := by
    intro h
    exact hpnot (by simpa [h] using mem_univ p)
  have hcomplne : Vᶜ.Nonempty := ⟨p, by simpa using hpnot⟩
  have hdistpos : 0 < Metric.infDist x Vᶜ :=
    ((isClosed_compl_iff.mpr hVopen).notMem_iff_infDist_pos hcomplne).mp (by simpa using hxV)
  obtain ⟨q, hqfront, hdistq⟩ := exists_mem_frontier_infDist_compl_eq_dist (E := ℂ) hxV hVne
  have hqdistxp : dist x q = Metric.infDist x Vᶜ := by
    simpa [dist_comm] using hdistq.symm
  have hseg : ∀ t : ℝ, 0 ≤ t → t < 1 → AffineMap.lineMap x q t ∈ V := by
    intro t ht0 ht1
    have htdist : dist (AffineMap.lineMap x q t) x < Metric.infDist x Vᶜ := by
      rw [dist_lineMap_left, hqdistxp]
      have hnorm : ‖t‖ < (1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht0]
        exact ht1
      simpa using mul_lt_of_lt_one_left hdistpos hnorm
    exact Metric.ball_infDist_compl_subset (x := x) (s := V) htdist
  refine ⟨q, hqfront, ?_, ⟨x, hxV, hqfront, hseg⟩⟩
  have hxpd : dist x p < η := by simpa [dist_comm] using hxp
  have hqx : dist q x = Metric.infDist x Vᶜ := by
    simpa [dist_comm] using hdistq.symm
  have hle : Metric.infDist x Vᶜ ≤ dist x p := Metric.infDist_le_dist_of_mem (by simpa using hpnot)
  calc
    dist q p ≤ dist q x + dist x p := dist_triangle q x p
    _ = Metric.infDist x Vᶜ + dist x p := by rw [hqx]
    _ ≤ dist x p + dist x p := by linarith
    _ < η + η := add_lt_add hxpd hxpd
    _ < ε := by
      dsimp [η]
      linarith

/-- Component-relative access near a common-frontier point, localized away from the other filled Julia
set.  This is the formal core of the prime-end/accessibility replacement for the false local-ray
condition. -/
theorem exists_commonExterior_straightSegmentAccessible_offOther_frontier_near
    {c₁ c₂ u p : ℂ} {ε : ℝ}
    (hpfront : p ∈ frontier (filledJulia c₁))
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hε : 0 < ε) :
    ∃ q : ℂ,
      q ∈ (filledJulia c₂)ᶜ ∧
      q ∈ frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
      dist q p < ε ∧
      StraightSegmentAccessibleFrom
        (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) q := by
  let G : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn G u
  have hGopen : IsOpen G :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVopen : IsOpen V := by
    simpa [V] using hGopen.connectedComponentIn (x := u)
  have hpK : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfront
  have hpnotV : p ∉ V := by
    intro hpV
    have hpG : p ∈ G := connectedComponentIn_subset G u (by simpa [V] using hpV)
    exact hpG.1 hpK
  have hpVfront : p ∈ frontier V := by
    simpa [hVopen.frontier_eq, V] using And.intro hpcl hpnotV
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let δ : ℝ := min ε R
  have hδpos : 0 < δ := lt_min hε hRpos
  obtain ⟨q, hqfront, hqdistδ, hqacc⟩ :=
    exists_straightSegmentAccessible_frontier_point_near (V := V) hVopen hpVfront hδpos
  have hqoff : q ∈ (filledJulia c₂)ᶜ := by
    apply hRsub
    exact lt_of_lt_of_le hqdistδ (min_le_right ε R)
  refine ⟨q, hqoff, ?_, ?_, ?_⟩
  · simpa [V] using hqfront
  · exact lt_of_lt_of_le hqdistδ (min_le_left ε R)
  · simpa [V] using hqacc

end

end Bottcher

namespace Bottcher

noncomputable section

/-- A connected component of a subset is closed relative to the ambient subset. -/
lemma connectedComponentIn_relatively_closed
    {G : Set ℂ} {v : ℂ} (hvG : v ∈ G) :
    closure (connectedComponentIn G v) ∩ G ⊆ connectedComponentIn G v := by
  let W : Set ℂ := connectedComponentIn G v
  have hWpre : IsPreconnected W := isPreconnected_connectedComponentIn
  have hWsubT : W ⊆ closure W ∩ G := by
    intro z hz
    exact ⟨subset_closure hz, connectedComponentIn_subset G v (by simpa [W] using hz)⟩
  have hTsubcl : closure W ∩ G ⊆ closure W := inter_subset_left
  have hTpre : IsPreconnected (closure W ∩ G) := hWpre.subset_closure hWsubT hTsubcl
  have hvW : v ∈ W := by simpa [W] using mem_connectedComponentIn hvG
  have hvT : v ∈ closure W ∩ G := ⟨subset_closure hvW, hvG⟩
  have hTsubG : closure W ∩ G ⊆ G := inter_subset_right
  simpa [W] using hTpre.subset_connectedComponentIn hvT hTsubG

/-- Nearest-complement radial access from an interior point of an open proper planar set. -/
lemma exists_straightSegmentAccessible_frontier_point_near_complement_point
    {W : Set ℂ} (hWopen : IsOpen W) {v y : ℂ}
    (hvW : v ∈ W) (hyWc : y ∈ Wᶜ) {ε : ℝ}
    (hvy : 2 * dist v y < ε) :
    ∃ q : ℂ, q ∈ frontier W ∧ dist q y < ε ∧ StraightSegmentAccessibleFrom W q := by
  have hWne : W ≠ univ := by
    intro h
    exact hyWc (by simpa [h] using mem_univ y)
  have hcomplne : Wᶜ.Nonempty := ⟨y, hyWc⟩
  have hdistpos : 0 < Metric.infDist v Wᶜ :=
    ((isClosed_compl_iff.mpr hWopen).notMem_iff_infDist_pos hcomplne).mp (by simpa using hvW)
  obtain ⟨q, hqfront, hdistq⟩ := exists_mem_frontier_infDist_compl_eq_dist (E := ℂ) hvW hWne
  have hvq : dist v q = Metric.infDist v Wᶜ := by
    simpa [dist_comm] using hdistq.symm
  have hseg : ∀ t : ℝ, 0 ≤ t → t < 1 → AffineMap.lineMap v q t ∈ W := by
    intro t ht0 ht1
    have htdist : dist (AffineMap.lineMap v q t) v < Metric.infDist v Wᶜ := by
      rw [dist_lineMap_left, hvq]
      have hnorm : ‖t‖ < (1 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg ht0]
        exact ht1
      simpa using mul_lt_of_lt_one_left hdistpos hnorm
    exact Metric.ball_infDist_compl_subset (x := v) (s := W) htdist
  refine ⟨q, hqfront, ?_, ⟨v, hvW, hqfront, hseg⟩⟩
  have hqv : dist q v = Metric.infDist v Wᶜ := by
    simpa [dist_comm] using hdistq.symm
  have hle : Metric.infDist v Wᶜ ≤ dist v y := Metric.infDist_le_dist_of_mem hyWc
  calc
    dist q y ≤ dist q v + dist v y := dist_triangle q v y
    _ = Metric.infDist v Wᶜ + dist v y := by rw [hqv]
    _ ≤ dist v y + dist v y := by linarith
    _ = 2 * dist v y := by ring
    _ < ε := hvy

/-- Strong component-relative boundary access: near every eligible common-frontier point there is a
straight-segment-accessible point on the active Julia frontier, still outside the other filled Julia
set, and on the boundary of the chosen common-exterior component. -/
theorem exists_commonExterior_julia_straightSegmentAccessible_offOther_frontier_near
    {c₁ c₂ u p : ℂ} {ε : ℝ}
    (hpfront : p ∈ frontier (filledJulia c₁))
    (hpoff : p ∈ (filledJulia c₂)ᶜ)
    (hpcl : p ∈ closure (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u))
    (hε : 0 < ε) :
    ∃ q : ℂ,
      q ∈ frontier (filledJulia c₁) ∧
      q ∈ (filledJulia c₂)ᶜ ∧
      q ∈ frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) ∧
      dist q p < ε ∧
      StraightSegmentAccessibleFrom
        (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) q := by
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCopen : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVopen : IsOpen V := by
    simpa [V] using hCopen.connectedComponentIn (x := u)
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  let δ : ℝ := min ε R
  have hδpos : 0 < δ := lt_min hε hRpos
  let η : ℝ := δ / 3
  have hηpos : 0 < η := by positivity
  obtain ⟨v, hvV, hpvlt⟩ := Metric.mem_closure_iff.mp hpcl η hηpos
  have hvpdist : dist v p < η := by simpa [dist_comm] using hpvlt
  have hδleR : δ ≤ R := min_le_right ε R
  have hδleε : δ ≤ ε := min_le_left ε R
  have hηltR : η < R := by
    dsimp [η]
    nlinarith [hδpos, hδleR]
  have hvC : v ∈ C := connectedComponentIn_subset C u (by simpa [V] using hvV)
  let G : Set ℂ := Metric.ball p R ∩ (filledJulia c₁)ᶜ
  have hvG : v ∈ G := by
    refine ⟨?_, hvC.1⟩
    exact lt_trans hvpdist hηltR
  let W : Set ℂ := connectedComponentIn G v
  have hGopen : IsOpen G := Metric.isOpen_ball.inter (isClosed_filledJulia c₁).isOpen_compl
  have hWopen : IsOpen W := by
    simpa [W] using hGopen.connectedComponentIn (x := v)
  have hvW : v ∈ W := by simpa [W] using mem_connectedComponentIn hvG
  have hWsubG : W ⊆ G := by simpa [W] using connectedComponentIn_subset G v
  have hWsubC : W ⊆ C := by
    intro z hz
    have hzG : z ∈ G := hWsubG hz
    exact ⟨hzG.2, hRsub hzG.1⟩
  have hWsubV : W ⊆ V := by
    have hWsubCompV : W ⊆ connectedComponentIn C v :=
      (isPreconnected_connectedComponentIn).subset_connectedComponentIn hvW hWsubC
    have hcomp : connectedComponentIn C v = V := by
      have h := connectedComponentIn_eq (by simpa [V] using hvV)
      exact h.symm
    simpa [hcomp] using hWsubCompV
  have hpK : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfront
  have hpnotG : p ∉ G := by
    intro hpG
    exact hpG.2 hpK
  have hpnotW : p ∈ Wᶜ := by
    intro hpW
    exact hpnotG (hWsubG hpW)
  have hvy : 2 * dist v p < δ := by
    dsimp [η] at hvpdist
    nlinarith
  obtain ⟨q, hqfrontW, hqdistδ, hqaccW⟩ :=
    exists_straightSegmentAccessible_frontier_point_near_complement_point
      (W := W) hWopen hvW hpnotW hvy
  have hqdistε : dist q p < ε := lt_of_lt_of_le hqdistδ hδleε
  have hqballR : q ∈ Metric.ball p R := lt_of_lt_of_le hqdistδ hδleR
  have hqoff : q ∈ (filledJulia c₂)ᶜ := hRsub hqballR
  have hqclW : q ∈ closure W := frontier_subset_closure hqfrontW
  have hqnotW : q ∉ W := by
    have htmp : q ∈ closure W \ W := by simpa [hWopen.frontier_eq] using hqfrontW
    exact htmp.2
  have hqnotΩ₁ : q ∉ (filledJulia c₁)ᶜ := by
    intro hqΩ₁
    have hqG : q ∈ G := ⟨hqballR, hqΩ₁⟩
    have hqW : q ∈ W := connectedComponentIn_relatively_closed (G := G) (v := v) hvG ⟨hqclW, hqG⟩
    exact hqnotW hqW
  have hqK : q ∈ filledJulia c₁ := by simpa using hqnotΩ₁
  have hWsubΩ₁ : W ⊆ (filledJulia c₁)ᶜ := fun z hz => (hWsubG hz).2
  have hqclΩ₁ : q ∈ closure (filledJulia c₁)ᶜ := closure_mono hWsubΩ₁ hqclW
  have hqfrontK : q ∈ frontier (filledJulia c₁) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hqK, hqclΩ₁⟩
  have hqclV : q ∈ closure V := closure_mono hWsubV hqclW
  have hVsubΩ₁ : V ⊆ (filledJulia c₁)ᶜ := by
    intro z hz
    exact (connectedComponentIn_subset C u (by simpa [V] using hz)).1
  have hqnotV : q ∉ V := by
    intro hqV
    exact hVsubΩ₁ hqV hqK
  have hqfrontV : q ∈ frontier V := by
    simpa [hVopen.frontier_eq] using And.intro hqclV hqnotV
  have hqaccV : StraightSegmentAccessibleFrom V q := by
    rcases hqaccW with ⟨x, hxW, _hxfront, hxseg⟩
    exact ⟨x, hWsubV hxW, hqfrontV, fun t ht0 ht1 => hWsubV (hxseg t ht0 ht1)⟩
  exact ⟨q, hqfrontK, hqoff, by simpa [V] using hqfrontV, hqdistε, by simpa [V] using hqaccV⟩

end

end Bottcher

namespace Bottcher

/-- Analytic continuation across a boundary point from a specified approach set.  This is weaker than
`ContinuesAcross f D z₀`, which uses the full `nhdsWithin z₀ D` filter; it is the component-relative
continuation notion used by the accessible-boundary crossing argument. -/
def ContinuesAcrossWithin (f : ℂ → ℂ) (A : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ z in 𝓝[A] z₀, g z = f z

/-- A separable analytic fibre forces continuation of the basin branch from any preconnected approach
set on which the relation holds.  This is the formal core of the GPT crossing route: the approach set
may be one component/tail of the common exterior, not the full punctured basin ball. -/
theorem continuesAcrossWithin_of_branch_analytic_approach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {z₀ : ℂ}
    {r : ℝ} {A : Set ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hr : 0 < r)
    (hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z₀ ρ ∩ A))
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z₀ ρ ∩ A).Nonempty)
    (hβcA : ContinuousOn β (Metric.ball z₀ r ∩ A))
    (hβrelA : ∀ z ∈ Metric.ball z₀ r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧
      ContinuesAcrossWithin β (Metric.ball z₀ ρ ∩ A) z₀ := by
  obtain ⟨rBranch, w, hrBranch, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ : ℝ := min r rBranch with hρdef
  have hρ : 0 < ρ := lt_min hr hrBranch
  have hρr : ρ ≤ r := min_le_left _ _
  have hρBranch : ρ ≤ rBranch := min_le_right _ _
  let Approach : Set ℂ := Metric.ball z₀ ρ ∩ A
  have hApproachBallBranch : Approach ⊆ Metric.ball z₀ rBranch := by
    intro z hz
    exact Metric.ball_subset_ball hρBranch hz.1
  have hApproachPre : IsPreconnected Approach := hApre ρ hρ hρr
  have hβcApproach : ContinuousOn β Approach := by
    refine hβcA.mono ?_
    intro z hz
    exact ⟨Metric.ball_subset_ball hρr hz.1, hz.2⟩
  have hβrelApproach : ∀ z ∈ Approach, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    exact hβrelA z ⟨Metric.ball_subset_ball hρr hz.1, hz.2⟩
  obtain ⟨z₁, hz₁⟩ := hAne ρ hρ hρr
  have hwcApproach : ∀ k, ContinuousOn (w k) Approach :=
    fun k => (hwc k).mono hApproachBallBranch
  have hwsepApproach : ∀ z ∈ Approach, ∀ k l, k ≠ l → w k z ≠ w l z :=
    fun z hz => hwsep z (hApproachBallBranch hz)
  have hwdegApproach : ∀ z ∈ Approach, (fibrePoly a s z).natDegree = N :=
    fun z hz => hwdeg z (hApproachBallBranch hz)
  have hwrelApproach : ∀ k, ∀ z ∈ Approach, ∑ i ∈ s, a i z * (w k z) ^ i = 0 :=
    fun k z hz => hwrel k z (hApproachBallBranch hz)
  obtain ⟨k, hk⟩ :=
    eqOn_branch_of_relation_analytic hN1 w β hApproachPre hwcApproach hβcApproach
      hwsepApproach hwdegApproach hwrelApproach hβrelApproach hz₁
  have hwkAt : ContinuousAt (w k) z₀ :=
    (hwc k).continuousAt (Metric.ball_mem_nhds z₀ hrBranch)
  have hz₀ball : z₀ ∈ Metric.ball z₀ rBranch := Metric.mem_ball_self hrBranch
  have hroot : ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0 :=
    hwrel k z₀ hz₀ball
  have hrootQ : (fibrePoly a s z₀).eval (w k z₀) = 0 := by
    rw [eval_fibrePoly]
    exact hroot
  have hd : (fibrePoly a s z₀).derivative.eval (w k z₀) ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep hrootQ
  have hpart := relation_hasDerivAt_w_analytic a s z₀ (w k z₀)
  have hβlim : Tendsto β (𝓝[Approach] z₀) (𝓝 (w k z₀)) :=
    tendsto_within_of_eqOn hwkAt hk
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ :=
    exists_analyticAt_branch_analytic ha hroot hpart hd
  have hrelFilt : ∀ᶠ z in 𝓝[Approach] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelApproach
  have hmatchβ : ∀ᶠ z in 𝓝[Approach] z₀, g z = β z :=
    branch_unique_within_analytic (fun i hi => (ha i hi).continuousAt) hpart hd
      hgAt.continuousAt hgz₀ hβlim (hgrel.filter_mono nhdsWithin_le_nhds) hrelFilt
  exact ⟨ρ, hρ, hρr, g, hgAt, hmatchβ⟩

/-- Component-relative natural-boundary contradiction from a separable fibre.  The obstruction needed
here is not full-filter noncontinuability; it is the stronger one-sided/component noncontinuability used
in the paper proof package. -/
theorem false_of_branch_analytic_component_approach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} {A : Set ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hr : 0 < r) (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z₀ ρ ∩ A))
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z₀ ρ ∩ A).Nonempty)
    (hβcA : ContinuousOn β (Metric.ball z₀ r ∩ A))
    (hβrelA : ∀ z ∈ Metric.ball z₀ r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hnbWithin : ∀ B : Set ℂ,
      B ⊆ (filledJulia c)ᶜ →
      (∀ ε : ℝ, 0 < ε → (Metric.ball z₀ ε ∩ B).Nonempty) →
      ¬ ContinuesAcrossWithin β B z₀) :
    False := by
  obtain ⟨ρ, hρ, hρr, hcont⟩ :=
    continuesAcrossWithin_of_branch_analytic_approach
      hsupp hN hN1 ha hlead hsep hr hApre hAne hβcA hβrelA
  exact hnbWithin (Metric.ball z₀ ρ ∩ A)
    (by
      intro z hz
      exact hAsub hz.2)
    (by
      intro ε hε
      set δ : ℝ := min ε ρ with hδdef
      have hδ : 0 < δ := lt_min hε hρ
      have hδr : δ ≤ r := le_trans (min_le_right _ _) hρr
      obtain ⟨z, hzball, hzA⟩ := hAne δ hδ hδr
      refine ⟨z, ?_, ?_⟩
      · exact Metric.ball_subset_ball (min_le_left _ _) hzball
      · exact ⟨Metric.ball_subset_ball (min_le_right _ _) hzball, hzA⟩)
    hcont

end Bottcher

namespace Bottcher

/-- A nonempty set with no isolated points cannot be contained in a discrete subset.  This is the
abstract avoidance step in the component-frontier proof: once the frontier slice is shown to have no
isolated points, it automatically avoids every discrete analytic bad locus. -/
theorem not_subset_discrete_of_no_isolated {S B : Set ℂ}
    (hne : S.Nonempty)
    (hacc : ∀ p ∈ S, ∀ r : ℝ, 0 < r → ∃ q ∈ S, q ≠ p ∧ q ∈ Metric.ball p r)
    (hBdisc : IsDiscrete B) :
    ¬ S ⊆ B := by
  intro hsub
  obtain ⟨p, hpS⟩ := hne
  have hpB : p ∈ B := hsub hpS
  obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hBdisc hpB
  obtain ⟨q, hqS, hqne, hqball⟩ := hacc p hpS ε hε
  have hqmem : q ∈ Metric.ball p ε ∩ B := ⟨hqball, hsub hqS⟩
  have hqp : q = p := by
    have hsingle : q ∈ ({p} : Set ℂ) := by
      rw [← hball]
      exact hqmem
    simpa using hsingle
  exact hqne hqp

end Bottcher

namespace Bottcher

/-- Existence form of `not_subset_discrete_of_no_isolated`: a nonempty set with no isolated points has
at least one point outside any discrete bad locus. -/
theorem exists_mem_not_mem_discrete_of_no_isolated {S B : Set ℂ}
    (hne : S.Nonempty)
    (hacc : ∀ p ∈ S, ∀ r : ℝ, 0 < r → ∃ q ∈ S, q ≠ p ∧ q ∈ Metric.ball p r)
    (hBdisc : IsDiscrete B) :
    ∃ q : ℂ, q ∈ S ∧ q ∉ B := by
  by_contra hnone
  have hsub : S ⊆ B := by
    intro z hzS
    by_contra hzB
    exact hnone ⟨z, hzS, hzB⟩
  exact not_subset_discrete_of_no_isolated hne hacc hBdisc hsub

end Bottcher

open Set Metric
open scoped Pointwise

namespace Bottcher

/-- A punctured Euclidean disk in `ℂ` is preconnected.  The proof writes the centered punctured disk
as `(0,r) • sphere(0,1)` and then translates. -/
lemma punctured_ball_isPreconnected_complex {p : ℂ} {r : ℝ} (_hr : 0 < r) :
    IsPreconnected (Metric.ball p r \ ({p} : Set ℂ)) := by
  have hSphere : IsPreconnected (Metric.sphere (0 : ℂ) (1 : ℝ)) := by
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    exact isPreconnected_sphere hrank (0 : ℂ) (1 : ℝ)
  have hProd : IsPreconnected (Set.Ioo (0 : ℝ) r ×ˢ Metric.sphere (0 : ℂ) (1 : ℝ)) :=
    isPreconnected_Ioo.prod hSphere
  let f : ℝ × ℂ → ℂ := fun x => x.1 • x.2
  have hfcont : ContinuousOn f (Set.Ioo (0 : ℝ) r ×ˢ Metric.sphere (0 : ℂ) (1 : ℝ)) := by
    fun_prop
  have hImage : IsPreconnected (f '' (Set.Ioo (0 : ℝ) r ×ˢ Metric.sphere (0 : ℂ) (1 : ℝ))) :=
    hProd.image f hfcont
  have hImageEqSmul :
      f '' (Set.Ioo (0 : ℝ) r ×ˢ Metric.sphere (0 : ℂ) (1 : ℝ)) =
        Set.Ioo (0 : ℝ) r • Metric.sphere (0 : ℂ) (1 : ℝ) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx.1, x.2, hx.2, rfl⟩
    · rintro ⟨a, ha, y, hy, rfl⟩
      exact ⟨(a, y), ⟨ha, hy⟩, rfl⟩
  have hSmulEq :
      Set.Ioo (0 : ℝ) r • Metric.sphere (0 : ℂ) (1 : ℝ) =
        Metric.ball (0 : ℂ) r \ Metric.closedBall (0 : ℂ) (0 : ℝ) := by
    simpa [mul_one] using
      (Ioo_smul_sphere_zero (E := ℂ) (a := 0) (b := r) (r := 1) (by norm_num) zero_lt_one)
  have hClosedBallZero : Metric.closedBall (0 : ℂ) (0 : ℝ) = ({0} : Set ℂ) := by
    ext z
    simp
  have h0 : IsPreconnected (Metric.ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
    simpa [hImageEqSmul, hSmulEq, hClosedBallZero] using hImage
  let g : ℂ → ℂ := fun z => p + z
  have hgcont : ContinuousOn g (Metric.ball (0 : ℂ) r \ ({0} : Set ℂ)) := by
    fun_prop
  have hgImage : IsPreconnected (g '' (Metric.ball (0 : ℂ) r \ ({0} : Set ℂ))) :=
    h0.image g hgcont
  have hgImageEq :
      g '' (Metric.ball (0 : ℂ) r \ ({0} : Set ℂ)) = Metric.ball p r \ ({p} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      constructor
      · simpa [g, dist_eq_norm, add_comm, add_left_comm, add_assoc] using hw.1
      · intro hz
        have hw0 : w = 0 := by
          simpa [g] using congrArg (fun t => t - p) hz
        exact hw.2 (by simp [hw0])
    · intro hz
      refine ⟨z - p, ?_, ?_⟩
      · constructor
        · simpa [g, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz.1
        · intro hw0
          have hz_eq : z = p := sub_eq_zero.mp (by simpa using hw0)
          exact hz.2 hz_eq
      · simp [g]
  simpa [hgImageEq] using hgImage

/-- If a preconnected set meets an open set and does not meet its frontier, then it is contained in
that open set. -/
lemma subset_of_isPreconnected_of_inter_frontier_empty_of_inter_nonempty
    {Y A : Set ℂ} (hY : IsPreconnected Y) (hAopen : IsOpen A)
    (hYA : (Y ∩ A).Nonempty) (hYfront : Y ∩ frontier A = ∅) :
    Y ⊆ A := by
  have hcover : Y ⊆ A ∪ interior Aᶜ := by
    intro y hyY
    by_cases hyA : y ∈ A
    · exact Or.inl hyA
    · right
      have hynfront : y ∉ frontier A := by
        intro hyfront
        have hyempty : y ∈ (∅ : Set ℂ) := by
          rw [← hYfront]
          exact ⟨hyY, hyfront⟩
        exact hyempty
      have hycomplFront : y ∈ (frontier A)ᶜ := hynfront
      rw [compl_frontier_eq_union_interior] at hycomplFront
      rcases hycomplFront with hyintA | hyintAc
      · exact False.elim (hyA (interior_subset hyintA))
      · exact hyintAc
  have hdisj : Y ∩ (A ∩ interior Aᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro z ⟨_hzY, hzA, hzintAc⟩
    exact interior_subset hzintAc hzA
  have hsub_or := (isPreconnected_iff_subset_of_disjoint.mp hY)
    A (interior Aᶜ) hAopen isOpen_interior hcover hdisj
  rcases hsub_or with hsub | hsub
  · exact hsub
  · rcases hYA with ⟨y, hyY, hyA⟩
    exact False.elim (interior_subset (hsub hyY) hyA)

/-- Abstract form of boundary-slice no-isolatedness.  If `V` is open, lies outside `J`, is closed
relative to `Ω \ J`, and `J` has no isolated points, then `J ∩ Ω ∩ frontier V` has no isolated
points. -/
lemma boundary_slice_no_isolated_of_relative_component
    {Ω J V : Set ℂ}
    (hΩopen : IsOpen Ω) (hVopen : IsOpen V)
    (hVsubJc : V ⊆ Jᶜ)
    (hrelclosed : closure V ∩ (Ω \ J) ⊆ V)
    (hJacc : ∀ p ∈ J, ∀ r : ℝ, 0 < r → ∃ q ∈ J, q ≠ p ∧ q ∈ Metric.ball p r) :
    ∀ p ∈ (J ∩ Ω ∩ frontier V), ∀ r : ℝ, 0 < r →
      ∃ q ∈ (J ∩ Ω ∩ frontier V), q ≠ p ∧ q ∈ Metric.ball p r := by
  intro p hpE r hr
  by_contra hnone
  have hpJ : p ∈ J := hpE.1.1
  have hpΩ : p ∈ Ω := hpE.1.2
  have hpfront : p ∈ frontier V := hpE.2
  have hEball_single : ∀ q, q ∈ (J ∩ Ω ∩ frontier V) → q ∈ Metric.ball p r → q = p := by
    intro q hqE hqball
    by_contra hqne
    exact hnone ⟨q, hqE, hqne, hqball⟩
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp hΩopen p hpΩ
  let δ : ℝ := min (r / 2) R
  have hδpos : 0 < δ := lt_min (by linarith) hRpos
  have hδleR : δ ≤ R := min_le_right _ _
  have hδltr : δ < r := by
    have hδle : δ ≤ r / 2 := min_le_left _ _
    linarith
  let Y : Set ℂ := Metric.ball p δ \ ({p} : Set ℂ)
  have hYpre : IsPreconnected Y := by
    simpa [Y] using punctured_ball_isPreconnected_complex (p := p) hδpos
  have hpclV : p ∈ closure V := frontier_subset_closure hpfront
  have hpnotV : p ∉ V := by
    intro hpV
    have hpVF : p ∈ V ∩ frontier V := ⟨hpV, hpfront⟩
    have hempty := hVopen.inter_frontier_eq
    rw [hempty] at hpVF
    exact hpVF
  obtain ⟨v, hvV, hvball⟩ := Metric.mem_closure_iff.mp hpclV δ hδpos
  have hvne : v ≠ p := by
    intro hvp
    exact hpnotV (by simpa [hvp] using hvV)
  have hYV : (Y ∩ V).Nonempty := by
    refine ⟨v, ?_, hvV⟩
    exact ⟨by simpa [dist_comm] using hvball, by simp [hvne]⟩
  have hYfront : Y ∩ frontier V = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxY, hxfront⟩
    have hxΩ : x ∈ Ω := hRsub (Metric.ball_subset_ball hδleR hxY.1)
    have hxJ : x ∈ J := by
      by_contra hxnotJ
      have hxΩJ : x ∈ Ω \ J := ⟨hxΩ, hxnotJ⟩
      have hxclV : x ∈ closure V := frontier_subset_closure hxfront
      have hxV : x ∈ V := hrelclosed ⟨hxclV, hxΩJ⟩
      have hxVF : x ∈ V ∩ frontier V := ⟨hxV, hxfront⟩
      have hempty := hVopen.inter_frontier_eq
      rw [hempty] at hxVF
      exact hxVF
    have hxE : x ∈ J ∩ Ω ∩ frontier V := ⟨⟨hxJ, hxΩ⟩, hxfront⟩
    have hxballr : x ∈ Metric.ball p r := Metric.ball_subset_ball (le_of_lt hδltr) hxY.1
    have hxp : x = p := hEball_single x hxE hxballr
    exact hxY.2 (by simp [hxp])
  have hYsubV : Y ⊆ V :=
    subset_of_isPreconnected_of_inter_frontier_empty_of_inter_nonempty hYpre hVopen hYV hYfront
  obtain ⟨q, hqJ, hqne, hqball⟩ := hJacc p hpJ δ hδpos
  have hqY : q ∈ Y := ⟨hqball, by simp [hqne]⟩
  have hqV : q ∈ V := hYsubV hqY
  exact hVsubJc hqV hqJ

end Bottcher

namespace Bottcher

/-- Component-side noncontinuability at one Julia-boundary point, stated in the exact form consumed by
`false_of_branch_analytic_component_approach`.  The proof in
`docs/reports/theorem-b-component-side-noncontinuability-answer.md` reduces this to the Fatou-Ritt
exceptional-polynomial theorem. -/
def ComponentSideNoncontinuableAt (c : ℂ) (β : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ B : Set ℂ,
    B ⊆ (filledJulia c)ᶜ →
    (∀ ε : ℝ, 0 < ε → (Metric.ball z₀ ε ∩ B).Nonempty) →
    ¬ ContinuesAcrossWithin β B z₀

/-- The component-side branch contradiction, with Theorem B supplied as the named noncontinuability
input. -/
theorem false_of_branch_analytic_component_approach_of_noncontinuable
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} {A : Set ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hr : 0 < r) (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z₀ ρ ∩ A))
    (hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z₀ ρ ∩ A).Nonempty)
    (hβcA : ContinuousOn β (Metric.ball z₀ r ∩ A))
    (hβrelA : ∀ z ∈ Metric.ball z₀ r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hnbAt : ComponentSideNoncontinuableAt c β z₀) :
    False :=
  false_of_branch_analytic_component_approach
    hsupp hN hN1 ha hlead hsep hr hAsub hApre hAne hβcA hβrelA hnbAt

/-- The local data obtained in Theorem C after choosing an accessible point outside the finite bad locus
of an irreducible separable one-coordinate relation. -/
structure OneCoordinateSeparableCrossingData (c : ℂ) (β : ℂ → ℂ) where
  a : ℕ → ℂ → ℂ
  s : Finset ℕ
  N : ℕ
  z0 : ℂ
  r : ℝ
  A : Set ℂ
  hsupp : s ⊆ Finset.range (N + 1)
  hN : N ∈ s
  hN1 : 1 ≤ N
  ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z0
  hlead : a N z0 ≠ 0
  hsep : (fibrePoly a s z0).Separable
  hr : 0 < r
  hAsub : A ⊆ (filledJulia c)ᶜ
  hApre : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → IsPreconnected (Metric.ball z0 ρ ∩ A)
  hAne : ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → (Metric.ball z0 ρ ∩ A).Nonempty
  hβcA : ContinuousOn β (Metric.ball z0 r ∩ A)
  hβrelA : ∀ z ∈ Metric.ball z0 r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0

/-- Theorem C's final step: once a one-coordinate relation has been reduced to good separable crossing
data, component-side noncontinuability gives a contradiction. -/
theorem false_of_oneCoordinateSeparableCrossingData
    {c : ℂ} {β : ℂ → ℂ} (D : OneCoordinateSeparableCrossingData c β)
    (hnbAt : ComponentSideNoncontinuableAt c β D.z0) :
    False :=
  false_of_branch_analytic_component_approach_of_noncontinuable
    D.hsupp D.hN D.hN1 D.ha D.hlead D.hsep D.hr D.hAsub D.hApre D.hAne D.hβcA D.hβrelA hnbAt

end Bottcher

namespace Bottcher

noncomputable section

/-- Concrete common-exterior form of Theorem A.  If the first filled Julia set is perfect with empty
interior, then its slice lying in the other exterior and on the frontier of the chosen common-exterior
component has no isolated points. -/
theorem commonExterior_boundarySlice_no_isolated_of_perfect_emptyInterior
    {c₁ c₂ u : ℂ}
    (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅) :
    ∀ p ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)),
      ∀ r : ℝ, 0 < r →
        ∃ q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
          frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)),
          q ≠ p ∧ q ∈ Metric.ball p r := by
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hfront_eq : frontier (filledJulia c₁) = filledJulia c₁ := by
    rw [(isClosed_filledJulia c₁).frontier_eq, hempty]
    ext z
    simp
  have hΩopen : IsOpen ((filledJulia c₂)ᶜ : Set ℂ) := (isClosed_filledJulia c₂).isOpen_compl
  have hCopen : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVopen : IsOpen V := by
    simpa [V, C] using hCopen.connectedComponentIn (x := u)
  have hVsubJc : V ⊆ (filledJulia c₁)ᶜ := by
    intro z hzV
    exact (connectedComponentIn_subset C u (by simpa [V] using hzV)).1
  have hrelclosed : closure V ∩ ((filledJulia c₂)ᶜ \ filledJulia c₁) ⊆ V := by
    intro z hz
    have hzC : z ∈ C := ⟨hz.2.2, hz.2.1⟩
    by_cases huC : u ∈ C
    · exact connectedComponentIn_relatively_closed (G := C) (v := u) huC
        (by simpa [V] using ⟨hz.1, hzC⟩)
    · have hVempty : V = ∅ := by
        simpa [V] using connectedComponentIn_eq_empty (F := C) (x := u) huC
      have hzcl : z ∈ closure V := hz.1
      rw [hVempty] at hzcl
      simpa using hzcl
  have hJacc : ∀ p ∈ filledJulia c₁, ∀ r : ℝ, 0 < r →
      ∃ q ∈ filledJulia c₁, q ≠ p ∧ q ∈ Metric.ball p r := by
    intro p hp r hr
    have hpacc : AccPt p (𝓟 (filledJulia c₁)) := hK.acc p hp
    rw [accPt_iff_nhds] at hpacc
    obtain ⟨q, hq, hqne⟩ := hpacc (Metric.ball p r) (Metric.ball_mem_nhds p hr)
    exact ⟨q, hq.2, hqne, hq.1⟩
  have habstract := boundary_slice_no_isolated_of_relative_component
    (Ω := (filledJulia c₂)ᶜ) (J := filledJulia c₁) (V := V)
    hΩopen hVopen hVsubJc hrelclosed hJacc
  intro p hp r hr
  have hpAbs : p ∈ filledJulia c₁ ∩ (filledJulia c₂)ᶜ ∩ frontier V := by
    exact ⟨⟨by simpa [hfront_eq] using hp.1.1, hp.1.2⟩, by simpa [V] using hp.2⟩
  obtain ⟨q, hqAbs, hqne, hqball⟩ := habstract p hpAbs r hr
  refine ⟨q, ?_, hqne, hqball⟩
  exact ⟨⟨by simpa [hfront_eq] using hqAbs.1.1, hqAbs.1.2⟩, by simpa [V] using hqAbs.2⟩

/-- Countable/discrete bad-locus avoidance on the same common-exterior boundary slice. -/
theorem exists_commonExterior_boundarySlice_not_mem_discrete_of_perfect_emptyInterior
    {c₁ c₂ u : ℂ} {B : Set ℂ}
    (hK : Perfect (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hne : (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)).Nonempty)
    (hBdisc : IsDiscrete B) :
    ∃ q,
      q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      q ∉ B := by
  exact exists_mem_not_mem_discrete_of_no_isolated hne
    (commonExterior_boundarySlice_no_isolated_of_perfect_emptyInterior hK hempty) hBdisc

end

end Bottcher

namespace Bottcher

/-- Global component-side noncontinuability on the Julia frontier.  The paper proof of Theorem B
supplies this for the Böttcher coordinate when `c ≠ -2`, `filledJulia c` is connected, and
`interior (filledJulia c) = ∅`; the Fatou-Ritt classification is the external analytic input. -/
def ComponentSideNoncontinuabilityOnJulia (c : ℂ) (β : ℂ → ℂ) : Prop :=
  ∀ z₀, z₀ ∈ frontier (filledJulia c) → ComponentSideNoncontinuableAt c β z₀

/-- Theorem C consumed through the global noncontinuability interface supplied by Theorem B. -/
theorem false_of_oneCoordinateSeparableCrossingData_of_noncontinuabilityOnJulia
    {c : ℂ} {β : ℂ → ℂ} (D : OneCoordinateSeparableCrossingData c β)
    (hz0 : D.z0 ∈ frontier (filledJulia c))
    (hnb : ComponentSideNoncontinuabilityOnJulia c β) :
    False :=
  false_of_oneCoordinateSeparableCrossingData D (hnb D.z0 hz0)

end Bottcher

namespace Bottcher

/-- Final bivariate-relation algebra step.  If the boundary-crossing argument proves that every
relation `P(F,G)=0` already has zero specialization `P(X,G)` as a polynomial in `X`, then
transcendence of `G` kills all coefficients of `P`, so the original bivariate relation is zero. -/
theorem noRelation_of_specialization_zero_of_transcendental
    {K M : Type*} [Field K] [Field M] [Algebra K M] {F G : M}
    (hG : Transcendental K G)
    (hspecialize : ∀ P : Polynomial (Polynomial K),
      (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
      P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom = 0) :
    NoRelation K F G := by
  intro P hrel
  have hmap0 := hspecialize P hrel
  refine Polynomial.ext (fun i => ?_)
  rw [Polynomial.coeff_zero]
  have hcoeff : (aeval G) (P.coeff i) = 0 := by
    have h := congrArg (fun Q : Polynomial M => Q.coeff i) hmap0
    simpa [Polynomial.coeff_map] using h
  by_contra hne
  exact hG ⟨P.coeff i, hne, hcoeff⟩

end Bottcher

namespace Bottcher

noncomputable section

/-- Connected-empty-interior common-exterior form of Theorem A.  This removes the auxiliary `Perfect`
hypothesis from `commonExterior_boundarySlice_no_isolated_of_perfect_emptyInterior` using the existing
perfectness theorem for connected nontrivial filled Julia sets. -/
theorem commonExterior_boundarySlice_no_isolated_of_preconnected_emptyInterior
    {c₁ c₂ u : ℂ}
    (hconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅) :
    ∀ p ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)),
      ∀ r : ℝ, 0 < r →
        ∃ q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
          frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)),
          q ≠ p ∧ q ∈ Metric.ball p r :=
  commonExterior_boundarySlice_no_isolated_of_perfect_emptyInterior
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial c₁)) hempty

/-- Connected-empty-interior discrete bad-locus avoidance on the common-exterior boundary slice. -/
theorem exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior
    {c₁ c₂ u : ℂ} {B : Set ℂ}
    (hconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hne : (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)).Nonempty)
    (hBdisc : IsDiscrete B) :
    ∃ q,
      q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      q ∉ B :=
  exists_commonExterior_boundarySlice_not_mem_discrete_of_perfect_emptyInterior
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial c₁))
    hempty hne hBdisc

end

end Bottcher

namespace Bottcher

/-- Component-level branch continuation from a separated analytic branch family.  Unlike
`continuesAcrossWithin_of_branch_analytic_approach`, this does not require every small ball slice of the
approach set to be preconnected; it only requires the chosen approach set itself to be preconnected. -/
theorem continuesAcrossWithin_of_branch_family_preconnected_approach
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {z₀ : ℂ}
    {A : Set ℂ} {β : ℂ → ℂ} {w : Fin N → ℂ → ℂ}
    (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hsep0 : (fibrePoly a s z₀).Separable)
    (hApre : IsPreconnected A) (hAne : A.Nonempty)
    (hwcA : ∀ k, ContinuousOn (w k) A)
    (hwAt : ∀ k, ContinuousAt (w k) z₀)
    (hwsepA : ∀ z ∈ A, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hwdegA : ∀ z ∈ A, (fibrePoly a s z).natDegree = N)
    (hwrelA : ∀ k, ∀ z ∈ A, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    (hwrel0 : ∀ k, ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0)
    (hβcA : ContinuousOn β A)
    (hβrelA : ∀ z ∈ A, ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ContinuesAcrossWithin β A z₀ := by
  obtain ⟨z₁, hz₁A⟩ := hAne
  obtain ⟨k, hk⟩ :=
    eqOn_branch_of_relation_analytic hN1 w β hApre hwcA hβcA hwsepA hwdegA hwrelA hβrelA hz₁A
  have hroot : ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0 := hwrel0 k
  have hrootQ : (fibrePoly a s z₀).eval (w k z₀) = 0 := by
    rw [eval_fibrePoly]
    exact hroot
  have hd : (fibrePoly a s z₀).derivative.eval (w k z₀) ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsep0 hrootQ
  have hpart := relation_hasDerivAt_w_analytic a s z₀ (w k z₀)
  have hβlim : Tendsto β (𝓝[A] z₀) (𝓝 (w k z₀)) :=
    tendsto_within_of_eqOn (hwAt k) hk
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ :=
    exists_analyticAt_branch_analytic ha hroot hpart hd
  have hrelFilt : ∀ᶠ z in 𝓝[A] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin hβrelA
  have hmatchβ : ∀ᶠ z in 𝓝[A] z₀, g z = β z :=
    branch_unique_within_analytic (fun i hi => (ha i hi).continuousAt) hpart hd
      hgAt.continuousAt hgz₀ hβlim (hgrel.filter_mono nhdsWithin_le_nhds) hrelFilt
  exact ⟨g, hgAt, hmatchβ⟩

/-- Component-level contradiction from a separated analytic branch family and component-side
noncontinuability.  This is the local form needed after choosing a connected approach component in the
squarefree factor proof. -/
theorem false_of_branch_family_preconnected_approach_of_noncontinuable
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {A : Set ℂ} {β : ℂ → ℂ} {w : Fin N → ℂ → ℂ}
    (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hsep0 : (fibrePoly a s z₀).Separable)
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hAacc : ∀ ε : ℝ, 0 < ε → (Metric.ball z₀ ε ∩ A).Nonempty)
    (hApre : IsPreconnected A)
    (hwcA : ∀ k, ContinuousOn (w k) A)
    (hwAt : ∀ k, ContinuousAt (w k) z₀)
    (hwsepA : ∀ z ∈ A, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hwdegA : ∀ z ∈ A, (fibrePoly a s z).natDegree = N)
    (hwrelA : ∀ k, ∀ z ∈ A, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    (hwrel0 : ∀ k, ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0)
    (hβcA : ContinuousOn β A)
    (hβrelA : ∀ z ∈ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hnbAt : ComponentSideNoncontinuableAt c β z₀) :
    False := by
  have hAne : A.Nonempty := by
    obtain ⟨z, _hzball, hzA⟩ := hAacc 1 (by norm_num)
    exact ⟨z, hzA⟩
  exact hnbAt A hAsub hAacc
    (continuesAcrossWithin_of_branch_family_preconnected_approach hN1 ha hsep0 hApre hAne
      hwcA hwAt hwsepA hwdegA hwrelA hwrel0 hβcA hβrelA)

end Bottcher

namespace Bottcher

/-- Julia-level contradiction from a separated analytic branch family and component-side
noncontinuability on the Julia set.  This is the endpoint used after Theorem A chooses a boundary
point avoiding the finite/discrete bad locus in the squarefree factor argument. -/
theorem false_of_branch_family_preconnected_approach_of_noncontinuabilityOnJulia
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {A : Set ℂ} {β : ℂ → ℂ} {w : Fin N → ℂ → ℂ}
    (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hsep0 : (fibrePoly a s z₀).Separable)
    (hz₀J : z₀ ∈ frontier (filledJulia c))
    (hAsub : A ⊆ (filledJulia c)ᶜ)
    (hAacc : ∀ ε : ℝ, 0 < ε → (Metric.ball z₀ ε ∩ A).Nonempty)
    (hApre : IsPreconnected A)
    (hwcA : ∀ k, ContinuousOn (w k) A)
    (hwAt : ∀ k, ContinuousAt (w k) z₀)
    (hwsepA : ∀ z ∈ A, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hwdegA : ∀ z ∈ A, (fibrePoly a s z).natDegree = N)
    (hwrelA : ∀ k, ∀ z ∈ A, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    (hwrel0 : ∀ k, ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0)
    (hβcA : ContinuousOn β A)
    (hβrelA : ∀ z ∈ A, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hnb : ComponentSideNoncontinuabilityOnJulia c β) :
    False :=
  false_of_branch_family_preconnected_approach_of_noncontinuable hN1 ha hsep0 hAsub hAacc hApre
    hwcA hwAt hwsepA hwdegA hwrelA hwrel0 hβcA hβrelA (hnb z₀ hz₀J)

end Bottcher

namespace Bottcher

/-- One-coordinate crossing data in the component form used by the final proof.  The approach set is a
single preconnected component/tail from the common exterior, equipped with the separated local branch
family for the squarefree fibre polynomial. -/
structure OneCoordinateBranchFamilyCrossingData (c : ℂ) (β : ℂ → ℂ) where
  a : ℕ → ℂ → ℂ
  s : Finset ℕ
  N : ℕ
  z0 : ℂ
  A : Set ℂ
  w : Fin N → ℂ → ℂ
  hN1 : 1 ≤ N
  ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z0
  hsep0 : (fibrePoly a s z0).Separable
  hz0J : z0 ∈ frontier (filledJulia c)
  hAsub : A ⊆ (filledJulia c)ᶜ
  hAacc : ∀ ε : ℝ, 0 < ε → (Metric.ball z0 ε ∩ A).Nonempty
  hApre : IsPreconnected A
  hwcA : ∀ k, ContinuousOn (w k) A
  hwAt : ∀ k, ContinuousAt (w k) z0
  hwsepA : ∀ z ∈ A, ∀ k l, k ≠ l → w k z ≠ w l z
  hwdegA : ∀ z ∈ A, (fibrePoly a s z).natDegree = N
  hwrelA : ∀ k, ∀ z ∈ A, ∑ i ∈ s, a i z * (w k z) ^ i = 0
  hwrel0 : ∀ k, ∑ i ∈ s, a i z0 * (w k z0) ^ i = 0
  hβcA : ContinuousOn β A
  hβrelA : ∀ z ∈ A, ∑ i ∈ s, a i z * (β z) ^ i = 0

/-- Theorem C's component-form endpoint.  Once the one-coordinate relation has been reduced to a good
separable fibre over one accessible approach component, Theorem B's component-side noncontinuability
contradicts the relation. -/
theorem false_of_oneCoordinateBranchFamilyCrossingData_of_noncontinuabilityOnJulia
    {c : ℂ} {β : ℂ → ℂ} (D : OneCoordinateBranchFamilyCrossingData c β)
    (hnb : ComponentSideNoncontinuabilityOnJulia c β) :
    False :=
  false_of_branch_family_preconnected_approach_of_noncontinuabilityOnJulia
    (a := D.a) (s := D.s) (N := D.N) (c := c) (z₀ := D.z0) (A := D.A) (β := β) (w := D.w)
    D.hN1 D.ha D.hsep0 D.hz0J D.hAsub D.hAacc D.hApre
    D.hwcA D.hwAt D.hwsepA D.hwdegA D.hwrelA D.hwrel0 D.hβcA D.hβrelA hnb

end Bottcher

namespace Bottcher

/-- Final bivariate algebra endpoint in contradiction form.  A relation is killed either because its
specialization in the first coordinate is already zero, in which case transcendence of the second
coordinate kills every coefficient, or because a nonzero specialization triggers the supplied
contradiction. -/
theorem noRelation_of_specialization_contradiction_of_transcendental
    {K M : Type*} [Field K] [Field M] [Algebra K M] {F G : M}
    (hG : Transcendental K G)
    (hcontra : ∀ P : Polynomial (Polynomial K),
      (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
      P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom ≠ 0 →
      False) :
    NoRelation K F G := by
  intro P hrel
  by_cases hmap0 : P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom = 0
  · refine Polynomial.ext (fun i => ?_)
    rw [Polynomial.coeff_zero]
    have hcoeff : (aeval G) (P.coeff i) = 0 := by
      have h := congrArg (fun Q : Polynomial M => Q.coeff i) hmap0
      simpa [Polynomial.coeff_map] using h
    by_contra hne
    exact hG ⟨P.coeff i, hne, hcoeff⟩
  · exact False.elim (hcontra P hrel hmap0)

/-- Theorem D endpoint using the component-form Theorem C package.  The analytic reduction only has to
show that a nonzero specialization of a bivariate relation produces one good component crossing datum;
Theorem B and Theorem C then give the contradiction, while transcendence handles the zero
specialization case. -/
theorem noRelation_of_branchFamily_specialization_producer_of_transcendental
    {K M : Type*} [Field K] [Field M] [Algebra K M] {F G : M}
    {c : ℂ} {β : ℂ → ℂ}
    (hG : Transcendental K G)
    (hnb : ComponentSideNoncontinuabilityOnJulia c β)
    (hproducer : ∀ P : Polynomial (Polynomial K),
      (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
      P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom ≠ 0 →
      OneCoordinateBranchFamilyCrossingData c β) :
    NoRelation K F G :=
  noRelation_of_specialization_contradiction_of_transcendental hG
    (fun P hrel hnonzero =>
      false_of_oneCoordinateBranchFamilyCrossingData_of_noncontinuabilityOnJulia
        (hproducer P hrel hnonzero) hnb)

end Bottcher

namespace Bottcher

/-- A genuine single-valued Böttcher branch on the basin of infinity.  This is the branch class to which
the component-side theorem B applies: analytic on `Ω_c = K_cᶜ`, anchored to the normalized far-field
Böttcher coordinate, and carrying the Böttcher Green modulus. -/
structure GlobalBottcherBranch (c : ℂ) (β : ℂ → ℂ) : Prop where
  analytic : AnalyticOnNhd ℂ β (filledJulia c)ᶜ
  anchorEscape : ∀ z ∈ escapeOpen c, β z = bottcherCoord c z
  modulus : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)

/-- The component-side form of theorem B, restricted to genuine Böttcher branches.  This is the formal
shape of `docs/reports/theorem-b-component-side-noncontinuability-open-lean-obstruction-answer.md`:
a branch matching the normalized Böttcher coordinate cannot have a one-sided/component holomorphic
continuation across a Julia point. -/
def ComponentSideBottcherNoncontinuabilityOnJulia (c : ℂ) : Prop :=
  ∀ β : ℂ → ℂ, GlobalBottcherBranch c β →
    ∀ z₀, z₀ ∈ frontier (filledJulia c) → ComponentSideNoncontinuableAt c β z₀

/-- Theorem C endpoint with theorem B stated for genuine Böttcher branches. -/
theorem false_of_oneCoordinateBranchFamilyCrossingData_of_bottcherNoncontinuabilityOnJulia
    {c : ℂ} {β : ℂ → ℂ} (D : OneCoordinateBranchFamilyCrossingData c β)
    (hbranch : GlobalBottcherBranch c β)
    (hnb : ComponentSideBottcherNoncontinuabilityOnJulia c) :
    False :=
  false_of_oneCoordinateBranchFamilyCrossingData_of_noncontinuabilityOnJulia D
    (hnb β hbranch)

/-- Theorem D endpoint with theorem B stated for genuine Böttcher branches.  A nonzero specialization
must produce component crossing data for the same global Böttcher branch; theorem B then supplies the
component-side contradiction, while transcendence kills the zero-specialization case. -/
theorem noRelation_of_branchFamily_specialization_producer_of_bottcherNoncontinuability
    {K M : Type*} [Field K] [Field M] [Algebra K M] {F G : M}
    {c : ℂ} {β : ℂ → ℂ}
    (hG : Transcendental K G)
    (hbranch : GlobalBottcherBranch c β)
    (hnb : ComponentSideBottcherNoncontinuabilityOnJulia c)
    (hproducer : ∀ P : Polynomial (Polynomial K),
      (P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom).eval F = 0 →
      P.map (aeval G : Polynomial K →ₐ[K] M).toRingHom ≠ 0 →
      OneCoordinateBranchFamilyCrossingData c β) :
    NoRelation K F G :=
  noRelation_of_specialization_contradiction_of_transcendental hG
    (fun P hrel hnonzero =>
      false_of_oneCoordinateBranchFamilyCrossingData_of_bottcherNoncontinuabilityOnJulia
        (hproducer P hrel hnonzero) hbranch hnb)

end Bottcher

namespace Bottcher

/-- Theorem C in algebraic form: if every nonzero univariate algebraic relation for `G` produces the
component crossing datum from the one-coordinate proof, then `G` is transcendental.  The contradiction
uses theorem B only through the genuine-Böttcher-branch component noncontinuability interface. -/
theorem transcendental_of_branchFamily_relation_producer_of_bottcherNoncontinuability
    {K M : Type*} [Field K] [Field M] [Algebra K M] {G : M}
    {c : ℂ} {β : ℂ → ℂ}
    (hbranch : GlobalBottcherBranch c β)
    (hnb : ComponentSideBottcherNoncontinuabilityOnJulia c)
    (hproducer : ∀ P : Polynomial K,
      aeval G P = 0 → P ≠ 0 → OneCoordinateBranchFamilyCrossingData c β) :
    Transcendental K G := by
  rw [transcendental_iff]
  intro P hP
  by_contra hPne
  exact false_of_oneCoordinateBranchFamilyCrossingData_of_bottcherNoncontinuabilityOnJulia
    (hproducer P hP hPne) hbranch hnb

/-- Theorem C specialized to the actual Böttcher meromorphic germ `phiMero c`.  The remaining producer is
exactly the proof step in `theorem-c-one-coordinate-transcendence-open-lean-obstruction-answer.md`: a
nonzero univariate relation is made squarefree, a good accessible boundary point is chosen, and the local
root branches give component crossing data. -/
theorem transcendental_phiMero_of_branchFamily_relation_producer
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (β : ℂ → ℂ)
    (hbranch : GlobalBottcherBranch c β)
    (hnb : ComponentSideBottcherNoncontinuabilityOnJulia c)
    (hproducer :
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ P : Polynomial (RatFunc ℂ),
        aeval (phiMero c hU) P = 0 → P ≠ 0 → OneCoordinateBranchFamilyCrossingData c β) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendental_of_branchFamily_relation_producer_of_bottcherNoncontinuability
    hbranch hnb hproducer

/-- Theorem D on the actual `phiMero` carrier, with Theorem C supplying the one-coordinate
transcendence of the second coordinate.  The two remaining producers are the two constructive parts of
the supplied proofs: univariate squarefree boundary crossing for C, and nonzero-specialization
squarefree boundary-slice crossing for D. -/
theorem noRelation_phiMero_of_branchFamily_relation_producers
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (β₁ β₂ : ℂ → ℂ)
    (hbranch₁ : GlobalBottcherBranch c₁ β₁)
    (hbranch₂ : GlobalBottcherBranch c₂ β₂)
    (hnb₁ : ComponentSideBottcherNoncontinuabilityOnJulia c₁)
    (hnb₂ : ComponentSideBottcherNoncontinuabilityOnJulia c₂)
    (hGproducer :
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ P : Polynomial (RatFunc ℂ),
        aeval (phiMero c₂ hU₂) P = 0 → P ≠ 0 → OneCoordinateBranchFamilyCrossingData c₂ β₂)
    (hSpecializationProducer :
      letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      ∀ P : Polynomial (Polynomial (RatFunc ℂ)),
        (P.map (aeval (phiMero c₂ hU₂) : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom).eval
            (phiMero c₁ hU₁) = 0 →
        (P.map (aeval (phiMero c₂ hU₂) : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom) ≠ 0 →
        OneCoordinateBranchFamilyCrossingData c₁ β₁) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    transcendental_phiMero_of_branchFamily_relation_producer hUo hUc hUne hUinf c₂ hU₂ β₂
      hbranch₂ hnb₂ hGproducer
  exact noRelation_of_branchFamily_specialization_producer_of_bottcherNoncontinuability
    hG hbranch₁ hnb₁ hSpecializationProducer

/-- A global Böttcher branch produced by the existing level-root/modulus construction, packaged in the
new theorem-B-specific branch structure. -/
theorem exists_globalBottcherBranch_of_level_roots_modulus
    (c : ℂ) (βlev : ℕ → ℂ → ℂ)
    (hanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c n))
    (hpow : ∀ n, ∀ z ∈ escapeLevel c n,
      (βlev n z) ^ (2 ^ n) = bottcherCoord c ((quadratic c)^[n] z))
    (hne : ∀ n, ∀ z ∈ escapeLevel c n, βlev n z ≠ 0)
    (hanchorEsc : ∀ n, ∀ z ∈ escapeOpen c, βlev n z = bottcherCoord c z) :
    ∃ β : ℂ → ℂ, GlobalBottcherBranch c β := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c βlev hanalytic hpow hne hanchorEsc
  exact ⟨β, ⟨hβan, hβesc, hβmod⟩⟩

end Bottcher

namespace Bottcher

noncomputable section

/-- Boundary-slice bad-locus avoidance from a concrete off-other filled-Julia point.  This is the
component form used in theorem D: if the chosen common exterior component starts at `u` and there is a
point of `K_{c₁}` still lying in the other exterior, then the `J_{c₁}` side of that component has a
frontier point in `Ω_{c₂}` outside any discrete bad locus. -/
theorem exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior_offOtherPoint
    {c₁ c₂ u x : ℂ} {B : Set ℂ}
    (hu : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ)
    (hxK : x ∈ filledJulia c₁)
    (hxoff : x ∈ (filledJulia c₂)ᶜ)
    (hconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hBdisc : IsDiscrete B) :
    ∃ q,
      q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      q ∉ B := by
  obtain ⟨p, hpfront, hpoff, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component (a := c₁) (b := c₂) (u := u) (x := x)
      hu hxK hxoff
  let C : Set ℂ := (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ
  let V : Set ℂ := connectedComponentIn C u
  have hCopen : IsOpen C :=
    (isClosed_filledJulia c₁).isOpen_compl.inter (isClosed_filledJulia c₂).isOpen_compl
  have hVopen : IsOpen V := by
    simpa [V, C] using hCopen.connectedComponentIn (x := u)
  have hpK : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfront
  have hpnotV : p ∉ V := by
    intro hpV
    have hpC : p ∈ C := connectedComponentIn_subset C u hpV
    exact hpC.1 hpK
  have hpfrontV : p ∈ frontier V := by
    simpa [hVopen.frontier_eq, V] using And.intro (by simpa [V, C] using hpcl) hpnotV
  have hne : (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
      frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)).Nonempty := by
    refine ⟨p, ?_⟩
    exact ⟨⟨hpfront, hpoff⟩, by simpa [V, C] using hpfrontV⟩
  exact exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior
    hconn hempty hne hBdisc

end

end Bottcher

namespace Bottcher

noncomputable section

/-- Symmetric boundary-slice bad-locus avoidance for distinct parameters.  A distinct pair supplies a
point in one filled Julia set and outside the other; applying the off-other-point wrapper in that
orientation gives a good common-component boundary point outside the corresponding discrete bad locus. -/
theorem exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior_symmDiff
    {c₁ c₂ u : ℂ} {B₁ B₂ : Set ℂ}
    (hu : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ)
    (hne : c₁ ≠ c₂)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hconn₂ : IsPreconnected (filledJulia c₂))
    (hempty₁ : interior (filledJulia c₁) = ∅)
    (hempty₂ : interior (filledJulia c₂) = ∅)
    (hB₁disc : IsDiscrete B₁)
    (hB₂disc : IsDiscrete B₂) :
    (∃ q,
      q ∈ (frontier (filledJulia c₁) ∩ (filledJulia c₂)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u)) ∧
      q ∉ B₁) ∨
    (∃ q,
      q ∈ (frontier (filledJulia c₂) ∩ (filledJulia c₁)ᶜ ∩
        frontier (connectedComponentIn ((filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ) u)) ∧
      q ∉ B₂) := by
  obtain ⟨x, hx | hx⟩ := exists_point_filledJulia_symmDiff hne
  · exact Or.inl
      (exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior_offOtherPoint
        hu hx.1 hx.2 hconn₁ hempty₁ hB₁disc)
  · have hu' : u ∈ (filledJulia c₂)ᶜ ∩ (filledJulia c₁)ᶜ := ⟨hu.2, hu.1⟩
    exact Or.inr
      (exists_commonExterior_boundarySlice_not_mem_discrete_of_preconnected_emptyInterior_offOtherPoint
        hu' hx.1 hx.2 hconn₂ hempty₂ hB₂disc)

end

end Bottcher

namespace Bottcher

noncomputable section

/-- A straight component-access arc supplies the connected approach set required by the branch-family
contradiction.  This is the component-side replacement for the false local slit/one-arm condition: the
approach set is a tail of one accessible segment, not a whole punctured ball. -/
theorem false_of_accessible_branch_family_relation_of_noncontinuable
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c q : ℂ}
    {V : Set ℂ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) q)
    (hlead : a N q ≠ 0)
    (hsep : (fibrePoly a s q).Separable)
    (hqJ : q ∈ frontier (filledJulia c))
    (hVsub : V ⊆ (filledJulia c)ᶜ)
    (hacc : StraightSegmentAccessibleFrom V q)
    (hβcV : ContinuousOn β V)
    (hβrelV : ∀ z ∈ V, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hnbAt : ComponentSideNoncontinuableAt c β q) :
    False := by
  obtain ⟨r, xbranch, hr, hxbranchc, hxbranchsep, hxbranchdeg, hxbranchrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  rcases hacc with ⟨x, hxV, hqfrontV, hsegV⟩
  have hqK : q ∈ filledJulia c := mem_filledJulia_of_frontier hqJ
  have hqnotV : q ∉ V := by
    intro hqV
    exact hVsub hqV hqK
  have hxne : x ≠ q := by
    intro hxq
    exact hqnotV (by simpa [hxq] using hxV)
  have hdistpos : 0 < dist x q := dist_pos.mpr hxne
  let d : ℝ := dist x q
  have hdpos : 0 < d := by simpa [d] using hdistpos
  let δ : ℝ := min (1 / 2 : ℝ) (r / (2 * d))
  have hδpos : 0 < δ := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hrd : 0 < r / (2 * d) := by positivity
    exact lt_min hhalf hrd
  have hδlehalf : δ ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hδle_r : δ ≤ r / (2 * d) := min_le_right _ _
  let t₀ : ℝ := 1 - δ
  have ht₀nonneg : 0 ≤ t₀ := by
    dsimp [t₀]
    nlinarith [hδlehalf]
  let A : Set ℂ := (fun t : ℝ => AffineMap.lineMap x q t) '' Set.Ico t₀ 1
  have hAV : A ⊆ V := by
    rintro z ⟨t, ht, rfl⟩
    exact hsegV t (le_trans ht₀nonneg ht.1) ht.2
  have hAball : A ⊆ Metric.ball q r := by
    rintro z ⟨t, ht, rfl⟩
    have ht_nonneg : 0 ≤ t := le_trans ht₀nonneg ht.1
    have hone_minus_nonneg : 0 ≤ 1 - t := by linarith [ht.2]
    have hone_minus_le_delta : 1 - t ≤ δ := by
      dsimp [t₀] at ht
      linarith [ht.1]
    have hnorm : ‖(1 : ℝ) - t‖ = 1 - t := Real.norm_of_nonneg hone_minus_nonneg
    have hdist : dist (AffineMap.lineMap x q t) q = (1 - t) * d := by
      rw [dist_lineMap_right, hnorm]
    have hmul : (1 - t) * d < r := by
      have hle : (1 - t) * d ≤ δ * d := by
        exact mul_le_mul_of_nonneg_right hone_minus_le_delta (le_of_lt hdpos)
      have hδd : δ * d ≤ r / 2 := by
        have hdnonzero : d ≠ 0 := ne_of_gt hdpos
        have htmp : δ * d ≤ (r / (2 * d)) * d :=
          mul_le_mul_of_nonneg_right hδle_r (le_of_lt hdpos)
        have heq : (r / (2 * d)) * d = r / 2 := by field_simp [hdnonzero]
        nlinarith [htmp, heq]
      nlinarith [hle, hδd, hr]
    simpa [Metric.mem_ball, hdist] using hmul
  have hApre : IsPreconnected A := by
    have hI : IsPreconnected (Set.Ico t₀ (1 : ℝ)) := isPreconnected_Ico
    have hf : ContinuousOn (fun t : ℝ => AffineMap.lineMap x q t) (Set.Ico t₀ 1) := by
      fun_prop
    exact hI.image _ hf
  have hAacc : ∀ ε : ℝ, 0 < ε → (Metric.ball q ε ∩ A).Nonempty := by
    intro ε hε
    let τ : ℝ := min (δ / 2) (ε / (2 * d))
    have hτpos : 0 < τ := by
      have hδ2 : 0 < δ / 2 := by positivity
      have hεd : 0 < ε / (2 * d) := by positivity
      exact lt_min hδ2 hεd
    have hτleδ2 : τ ≤ δ / 2 := min_le_left _ _
    have hτleεδ : τ ≤ ε / (2 * d) := min_le_right _ _
    have hτleδ : τ ≤ δ := by nlinarith [hτleδ2]
    let t : ℝ := 1 - τ
    have htI : t ∈ Set.Ico t₀ (1 : ℝ) := by
      refine ⟨?_, ?_⟩
      · dsimp [t, t₀]
        linarith [hτleδ]
      · dsimp [t]
        linarith [hτpos]
    refine ⟨AffineMap.lineMap x q t, ?_, ⟨t, htI, rfl⟩⟩
    have hτnonneg : 0 ≤ τ := le_of_lt hτpos
    have hnorm : ‖(1 : ℝ) - t‖ = τ := by
      dsimp [t]
      rw [sub_sub_cancel]
      exact Real.norm_of_nonneg hτnonneg
    have hdist : dist (AffineMap.lineMap x q t) q = τ * d := by
      rw [dist_lineMap_right, hnorm]
    have hτd : τ * d < ε := by
      have hle : τ * d ≤ (ε / (2 * d)) * d :=
        mul_le_mul_of_nonneg_right hτleεδ (le_of_lt hdpos)
      have hdnonzero : d ≠ 0 := ne_of_gt hdpos
      have heq : (ε / (2 * d)) * d = ε / 2 := by field_simp [hdnonzero]
      nlinarith [hle, heq, hε]
    · simpa [Metric.mem_ball, hdist] using hτd
    · exact ⟨t, htI, rfl⟩
  have hxbranchAt : ∀ k, ContinuousAt (xbranch k) q := by
    intro k
    exact (hxbranchc k).continuousAt (Metric.ball_mem_nhds q hr)
  have hxbranchrel0 : ∀ k, ∑ i ∈ s, a i q * (xbranch k q) ^ i = 0 := by
    intro k
    exact hxbranchrel k q (Metric.mem_ball_self hr)
  exact false_of_branch_family_preconnected_approach_of_noncontinuable
    hN1 ha hsep (fun z hz => hVsub (hAV hz)) hAacc hApre
    (fun k => (hxbranchc k).mono hAball) hxbranchAt
    (fun z hz => hxbranchsep z (hAball hz))
    (fun z hz => hxbranchdeg z (hAball hz))
    (fun k z hz => hxbranchrel k z (hAball hz)) hxbranchrel0
    (hβcV.mono hAV) (fun z hz => hβrelV z (hAV hz)) hnbAt

end

end Bottcher
