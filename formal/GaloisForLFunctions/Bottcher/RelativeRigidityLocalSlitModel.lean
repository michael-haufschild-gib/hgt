import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a pointwise rotated local slit model.** The local perfect-frontier target set is
built internally. The only geometric slit input left is pointwise and local-radius: every target in a
small frontier/off-other window admits some unit direction and positive radius whose rotated slit sector
lies in the basin. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty hγan₂ hγmatch
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, hlocal⟩ :=
        hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
          hrLocal hrOther hsector hother
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, rTip, hu, hrTip, hslit⟩ := hlocal z₀ ⟨⟨hzball, hzfront⟩, hzoff₂⟩
      exact ⟨mem_filledJulia_of_frontier hzfront, hzoff₂, rTip, hrTip,
        local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
          (K := filledJulia c₁) (u := u) (z₀ := z₀) hu hslit⟩)

/-- **hRigid from a pointwise rotated local slit model.** -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from a pointwise rotated local slit model.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch hinput)

end Bottcher

namespace Bottcher

variable {U : Set ℂ}

/-- **Natural-boundary NoRelation from a pointwise rotated local slit model.** This is the same local
perfect-frontier target-set reduction as the empty-interior endpoint above, but the natural-boundary
input is supplied directly instead of derived from the modulus formula. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_carrierClosureLocalTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
    (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, hlocal⟩ :=
        hinput Q s hnt hEqOn
      obtain ⟨S, havoid, hclosure, hSlocal⟩ :=
        exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
          hrLocal hrOther hsector hother
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hclosure, ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, rTip, hu, hrTip, hslit⟩ := hlocal z₀ ⟨⟨hzball, hzfront⟩, hzoff₂⟩
      exact ⟨hzfront, hzoff₂, rTip, hrTip,
        local_tip_preconnected_of_rotated_translated_slitPlane_subset_compl_le
          (K := filledJulia c₁) (u := u) (z₀ := z₀) hu hslit⟩)

/-- **Natural-boundary hRigid from a pointwise rotated local slit model.** -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hKconn hempty
      hγan₂ hγmatch hnb (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from natural-boundary pointwise rotated local slit model.** -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hKconn : IsPreconnected (filledJulia c₁))
    (hempty : interior (filledJulia c₁) = ∅)
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
            ∃ (u : ℂ) (rTip : ℝ), ‖u‖ = 1 ∧ 0 < rTip ∧
              ∀ ρ, 0 < ρ → ρ ≤ rTip →
                Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆
                  Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelLocalTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hKconn hempty
      hγan₂ hγmatch hnb hinput)

end Bottcher
