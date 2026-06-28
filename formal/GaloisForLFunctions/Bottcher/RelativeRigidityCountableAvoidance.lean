import GaloisForLFunctions.Bottcher.RelativeRigidityNaturalBoundary
import GaloisForLFunctions.Bottcher.Q62ConnectedAssembly
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect

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
