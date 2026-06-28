import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance
import GaloisForLFunctions.Bottcher.RelativeDenseApproach

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from countable avoidance plus dense approach geometry.**  The sparse-fibre
countable-avoidance gate still chooses the target outside the analytic lead/separability bad locus.
At that chosen target the branch contradiction only needs a dense preconnected approach set `A`, not
preconnectedness of the whole punctured basin ball. -/
theorem noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V A : Set ℂ),
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ A ⊆ V ∧
            A ⊆ (filledJulia c₁)ᶜ ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              IsPreconnected (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              (Metric.ball z₀ ρ ∩ A).Nonempty))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
    hgeom⟩ := hinput Q s hnt hEqOn
  let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
  obtain ⟨z₀, hz₀S, hlead, hsep⟩ :=
    exists_sparse_fibre_separable_countableAvoidance
      (a := a) (s := s) (N := N) hN1 hsupp hN hΩc haΩ hw hleadw hsepw havoid
  obtain ⟨r, V, A, hz₀K₁, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hAV,
    hAsub, hApre, hAdense, hAne⟩ := hgeom z₀ hz₀S
  have hγV : AnalyticOnNhd ℂ γ V := hγan₂.mono hVbasin₂
  have haV : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) V := by
    intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγV (Q i)
  have hγAt : AnalyticAt ℂ γ z₀ := hγan₂ z₀ hz₀off₂
  have haAt : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀ := by
    intro i _hi
    exact (analyticAt_eval₂_of_analyticAt hγAt (Q i)).contDiffAt
  have hmatch : ∀ i ∈ s, ∀ z ∈ U,
      a i z = (Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) := by
    intro i _hi z hz
    dsimp [a]
    simpa using congrArg (fun y => (Q i).eval₂ (Polynomial.evalRingHom z) y) (hγmatch z hz)
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
  have hβV : AnalyticOnNhd ℂ β V := hβan.mono hVbasin₁
  have hrelan : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s, a i z * (β z) ^ i) V :=
    analyticOnNhd_relation_analytic haV hβV
  obtain ⟨u, huU⟩ := hUne
  have hev : (fun z => ∑ i ∈ s, a i z * (β z) ^ i) =ᶠ[𝓝 u] (fun _ => (0 : ℂ)) := by
    filter_upwards [hUo.mem_nhds huU] with z hz
    exact hrelU z hz
  have hrelV : Set.EqOn (fun z => ∑ i ∈ s, a i z * (β z) ^ i) 0 V :=
    hrelan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc (hUV huU) hev
  have hβcA : ContinuousOn β (Metric.ball z₀ r ∩ A) :=
    hβan.continuousOn.mono (by
      intro z hz
      exact hAsub hz.2)
  have hβrelA : ∀ z ∈ Metric.ball z₀ r ∩ A, ∑ i ∈ s, a i z * (β z) ^ i = 0 := by
    intro z hz
    exact hrelV (hAV hz)
  have hβmodA : ∀ z ∈ Metric.ball z₀ r ∩ A,
      ‖β z‖ = Real.exp (greenFunctionDyn c₁ z) := by
    intro z hz
    exact hβmod z (hAsub hz.2)
  exact false_of_global_basin_branch_analytic_denseApproach_on
    (c := c₁) (z₀ := z₀) (r := r) (A := A)
    hsupp hN hN1 haAt (by simpa [a] using hlead) (by simpa [a] using hsep)
    hr hz₀K₁ hApre hAdense hAsub hAne hβcA hβrelA hβmodA

/-- **hRigid from countable avoidance plus dense approach geometry.** -/
theorem hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V A : Set ℂ),
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ A ⊆ V ∧
            A ⊆ (filledJulia c₁)ᶜ ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              IsPreconnected (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              (Metric.ball z₀ ρ ∩ A).Nonempty))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus dense approach geometry.** -/
theorem q62_independence_connected_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
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
          (∀ z₀ ∈ S, ∃ (r : ℝ) (V A : Set ℂ),
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
            V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
            Metric.ball z₀ r ∩ A ⊆ V ∧
            A ⊆ (filledJulia c₁)ᶜ ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              IsPreconnected (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              Metric.ball z₀ ρ ⊆ closure (Metric.ball z₀ ρ ∩ A)) ∧
            (∀ ρ : ℝ, 0 < ρ → ρ ≤ r →
              (Metric.ball z₀ ρ ∩ A).Nonempty))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch hinput)

end Bottcher

namespace Bottcher

/-- Countable-avoidance input whose selected targets carry a local rotated-slit dense approach landing
in a common-basin region. -/
abbrev CountableRotatedSlitDenseApproachInput (U : Set ℂ) (c₁ c₂ : ℂ)
    (hU₂ : U ⊆ escapeOpen c₂) (γ : ℂ → ℂ) : Prop :=
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
      (∀ z₀ ∈ S, ∃ (r : ℝ) (V : Set ℂ) (u : ℂ),
        z₀ ∈ filledJulia c₁ ∧
        z₀ ∈ (filledJulia c₂)ᶜ ∧
        ‖u‖ = 1 ∧ 0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
        V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
        Metric.ball z₀ r ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} ⊆ V)

/-- **NoRelation from countable avoidance plus a rotated-slit dense approach.** -/
theorem noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : CountableRotatedSlitDenseApproachInput U c₁ c₂ hU₂ γ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_denseApproach
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        hgeom⟩ := hinput Q s hnt hEqOn
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid, ?_⟩
      intro z₀ hz₀S
      obtain ⟨r, V, u, hz₀K₁, hz₀off₂, hu, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂,
        hslitV⟩ := hgeom z₀ hz₀S
      let A : Set ℂ := Metric.ball z₀ r ∩ {z | u * (z - z₀) ∈ Complex.slitPlane}
      refine ⟨r, V, A, hz₀K₁, hz₀off₂, hr, hVo, hVc, hUV, hVbasin₁, hVbasin₂, ?_,
        ?_, ?_, ?_, ?_⟩
      · intro z hz
        exact hslitV ⟨hz.1, hz.2.2⟩
      · intro z hz
        exact hVbasin₁ (hslitV hz)
      · intro ρ hρ hρle
        have hball_eq : Metric.ball z₀ ρ ∩ A =
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
          ext z
          constructor
          · intro hz
            exact ⟨hz.1, hz.2.2⟩
          · intro hz
            exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
        rw [hball_eq]
        exact isPreconnected_ball_inter_rotated_translated_slitPlane u z₀ hu hρ
      · intro ρ hρ hρle
        have hball_eq : Metric.ball z₀ ρ ∩ A =
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
          ext z
          constructor
          · intro hz
            exact ⟨hz.1, hz.2.2⟩
          · intro hz
            exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
        rw [hball_eq]
        exact ball_subset_closure_ball_inter_rotated_translated_slitPlane u z₀ hu
      · intro ρ hρ hρle
        have hball_eq : Metric.ball z₀ ρ ∩ A =
            Metric.ball z₀ ρ ∩ {z | u * (z - z₀) ∈ Complex.slitPlane} := by
          ext z
          constructor
          · intro hz
            exact ⟨hz.1, hz.2.2⟩
          · intro hz
            exact ⟨hz.1, ⟨Metric.ball_subset_ball hρle hz.1, hz.2⟩⟩
        rw [hball_eq]
        exact nonempty_ball_inter_rotated_translated_slitPlane u z₀ hu hρ)

/-- **hRigid from countable avoidance plus a rotated-slit dense approach.** -/
theorem hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ γ : ℂ → ℂ,
      AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
      (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
      CountableRotatedSlitDenseApproachInput U c₁ c₂ hU₂ γ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch
      (hinput γ hγan₂ hγmatch))

/-- **Connected q62 from countable avoidance plus a rotated-slit dense approach.** -/
theorem q62_independence_connected_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hne : c₁ ≠ c₂) (hx₁ : c₁ ∉ Exceptional) (hx₂ : c₂ ∉ Exceptional)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ γ : ℂ → ℂ,
      AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
      (∀ z ∈ U, γ z = bottcherCoord c₂ z) →
      CountableRotatedSlitDenseApproachInput U c₁ c₂ hU₂ γ) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch hinput)

end Bottcher

namespace Bottcher

/-- **Dense-approach NoRelation from a pointwise rotated local slit model.**  This closes the
local-frontier rotated-slit interface through the dense-approach obstruction: after the internal
countable-avoidance target selection, the slit radius is shrunk into the local carrier ball and the
common-basin continuation region is simply `U`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach
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
  exact noRelation_phiMero_of_commonBasin_gamma_offOther_countableAvoidance_rotatedSlitDenseApproach
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hγan₂ hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, p, rLocal, rOther, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw,
        hsepw, hpK, hpΩ, hrLocal, hrOther, hsector, hother, hlocal⟩ :=
        hinput Q s hnt hEqOn
      obtain ⟨S, havoid, _hclosure, hSlocal⟩ :=
        exists_local_frontier_target_set_countableAvoidance_closure_frontier_of_preconnected_emptyInterior
          (U := U) (Ω := Ω) (c₁ := c₁) (c₂ := c₂) hKconn hempty hpK hpΩ
          hrLocal hrOther hsector hother
      refine ⟨N, Ω, w, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw, havoid,
        ?_⟩
      intro z₀ hz₀S
      obtain ⟨hzball, hzfront, hzoff₂⟩ := hSlocal z₀ hz₀S
      obtain ⟨u, rTip, hu, hrTip, hslit⟩ := hlocal z₀ ⟨⟨hzball, hzfront⟩, hzoff₂⟩
      obtain ⟨rIn, hrIn, hballIn⟩ := Metric.isOpen_iff.mp isOpen_ball z₀ hzball
      let r : ℝ := min rTip rIn
      have hr : 0 < r := by
        simpa [r] using lt_min hrTip hrIn
      have hr_le_tip : r ≤ rTip := by
        simp [r]
      have hr_le_in : r ≤ rIn := by
        simp [r]
      refine ⟨r, U, u, mem_filledJulia_of_frontier hzfront, hzoff₂, hu, hr, hUo, hUc,
        subset_rfl, ?_, ?_, ?_⟩
      · intro z hz
        exact escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)
      · intro z hz
        exact escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz)
      · intro z hz
        have hzballIn : z ∈ Metric.ball p rLocal :=
          hballIn (Metric.ball_subset_ball hr_le_in hz.1)
        have hzbasin : z ∈ (filledJulia c₁)ᶜ :=
          (hslit r hr hr_le_tip ⟨hz.1, hz.2⟩).2
        exact hsector ⟨hzballIn, hzbasin⟩)

/-- **Dense-approach hRigid from a pointwise rotated local slit model.** -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach
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
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch (hinput γ hγan₂ hγmatch))

/-- **Dense-approach connected q62 from a pointwise rotated local slit model.** -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach
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
    (hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_countableAvoidance_localFrontierRotatedSlitModelDenseApproach
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hKconn hempty
      hγan₂ hγmatch hinput)

end Bottcher
