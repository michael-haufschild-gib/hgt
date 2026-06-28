import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranch
import GaloisForLFunctions.Bottcher.RelativeNaturalBoundary
import GaloisForLFunctions.Bottcher.DendriteContinuesAcross
import GaloisForLFunctions.Bottcher.RelativeFibreGeneric
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect
import GaloisForLFunctions.U0.U0NaturalBoundary

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- **NoRelation from a natural-boundary frontier fibre.** This is the non-periodic hRigid bridge:
a cleared relation is impossible once, at a frontier natural-boundary point, the continued coefficient
fibre is separable and the basin branch has a boundary value. The algebraic IFT gives an analytic
branch through the simple root; branch uniqueness identifies it with the basin branch, producing a
forbidden analytic continuation across the natural boundary. -/
theorem noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG (by
    intro Q s hnt hEqOn
    obtain ⟨z₀, w₀, hsep, hfront, hβlim⟩ := hinput Q s hnt hEqOn
    let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
    have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ := by
      intro i _hi
      exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
    have hγAt : AnalyticAt ℂ γ z₀ := hγfront z₀ hfront
    have haAt : ∀ i ∈ s, AnalyticAt ℂ (a i) z₀ := by
      intro i _hi
      exact analyticAt_eval₂_of_analyticAt hγAt (Q i)
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
    have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
      relation_eq_zero_basin_analytic_of_open hUo hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
    have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
    have hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
      nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront
    have hrootSum : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 :=
      relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
        (fun i hi => (haAt i hi).continuousAt) hNeBot hβlim hβrel
    have hrootPoly : (fibrePoly a s z₀).eval w₀ = 0 := by
      rwa [eval_fibrePoly]
    have hderiv : (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 :=
      eval_derivative_ne_zero_of_separable (by simpa [a] using hsep) hrootPoly
    obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic
      (fun i hi => (haAt i hi).contDiffAt) hrootSum (relation_hasDerivAt_w_analytic a s z₀ w₀) hderiv
    have hmatchβ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z :=
      branch_unique_within_analytic (fun i hi => (haAt i hi).continuousAt)
        (relation_hasDerivAt_w_analytic a s z₀ w₀) hderiv hgAt.continuousAt hgz₀ hβlim
        (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
    exact (hnb z₀ hfront) ⟨g, hgAt, hmatchβ⟩)

/-- **hRigid from a natural-boundary frontier fibre.** This packages
`noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` as the hRigid
`TranscendentalOverAdjoin` input. -/
theorem hrig_phiMero_of_naturalBoundary_global_gamma_frontier_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan hγfront hγmatch hnb hinput)

/-- **NoRelation from empty-interior natural boundary and a frontier fibre.** This specializes
`noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable` to the dendrite/empty-interior
case: the natural-boundary predicate is derived from the basin modulus rather than supplied as `hnb`. -/
theorem noRelation_phiMero_of_emptyInterior_global_gamma_frontier_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan hγfront hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) hinput

/-- **hRigid from empty-interior natural boundary and a frontier fibre.** This is the hRigid package of
`noRelation_phiMero_of_emptyInterior_global_gamma_frontier_separable`. -/
theorem hrig_phiMero_of_emptyInterior_global_gamma_frontier_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγfront : AnalyticOnNhd ℂ γ (frontier (filledJulia c₁)))
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_global_gamma_frontier_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan hγfront hγmatch hinput)

/-- **NoRelation from a natural-boundary fibre with point-local γ analyticity.** This is the
same contradiction as `noRelation_phiMero_of_naturalBoundary_global_gamma_frontier_separable`, but the
selected frontier point carries only `AnalyticAt γ z₀`; no frontier-wide analytic continuation of `γ` is
required. -/
theorem noRelation_phiMero_of_naturalBoundary_global_gamma_local_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG (by
    intro Q s hnt hEqOn
    obtain ⟨z₀, w₀, hsep, hfront, hγAt, hβlim⟩ := hinput Q s hnt hEqOn
    let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
    have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ := by
      intro i _hi
      exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
    have haAt : ∀ i ∈ s, AnalyticAt ℂ (a i) z₀ := by
      intro i _hi
      exact analyticAt_eval₂_of_analyticAt hγAt (Q i)
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
    have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
      relation_eq_zero_basin_analytic_of_open hUo hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
    have hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
      Filter.eventually_of_mem self_mem_nhdsWithin hβrel_all
    have hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot :=
      nhdsWithin_compl_filledJulia_neBot_of_mem_frontier hfront
    have hrootSum : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0 :=
      relation_boundary_root_of_tendsto (c := c₁) (β := β) (a := a) (s := s)
        (fun i hi => (haAt i hi).continuousAt) hNeBot hβlim hβrel
    have hrootPoly : (fibrePoly a s z₀).eval w₀ = 0 := by
      rwa [eval_fibrePoly]
    have hderiv : (fibrePoly a s z₀).derivative.eval w₀ ≠ 0 :=
      eval_derivative_ne_zero_of_separable (by simpa [a] using hsep) hrootPoly
    obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic
      (fun i hi => (haAt i hi).contDiffAt) hrootSum (relation_hasDerivAt_w_analytic a s z₀ w₀) hderiv
    have hmatchβ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z :=
      branch_unique_within_analytic (fun i hi => (haAt i hi).continuousAt)
        (relation_hasDerivAt_w_analytic a s z₀ w₀) hderiv hgAt.continuousAt hgz₀ hβlim
        (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
    exact (hnb z₀ hfront) ⟨g, hgAt, hmatchβ⟩)

/-- **hRigid from a natural-boundary fibre with point-local γ analyticity.** This packages
`noRelation_phiMero_of_naturalBoundary_global_gamma_local_separable` as the hRigid input. -/
theorem hrig_phiMero_of_naturalBoundary_global_gamma_local_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_global_gamma_local_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan hγmatch hnb hinput)

/-- **NoRelation from empty-interior natural boundary with point-local γ analyticity.** This derives
the natural-boundary predicate from the basin modulus, while the selected fibre supplies only local
analyticity of `γ`. -/
theorem noRelation_phiMero_of_emptyInterior_global_gamma_local_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_global_gamma_local_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) hinput

/-- **hRigid from empty-interior natural boundary with point-local γ analyticity.** This packages
`noRelation_phiMero_of_emptyInterior_global_gamma_local_separable`. -/
theorem hrig_phiMero_of_emptyInterior_global_gamma_local_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_global_gamma_local_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan hγmatch hinput)

/-- **NoRelation from a natural-boundary fibre whose γ point lies off `K_{c₂}`.** Local analyticity of
`γ` at the chosen frontier point is derived from an analytic branch on `(filledJulia c₂)ᶜ`. -/
theorem noRelation_phiMero_of_naturalBoundary_global_gamma_offOther_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_global_gamma_local_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₁ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨z₀, w₀, hsep, hfront, hz₀off, hβlim⟩ := hinput Q s hnt hEqOn
      exact ⟨z₀, w₀, hsep, hfront, hγan₂ z₀ hz₀off, hβlim⟩)

/-- **hRigid from a natural-boundary fibre whose γ point lies off `K_{c₂}`.** This packages
`noRelation_phiMero_of_naturalBoundary_global_gamma_offOther_separable`. -/
theorem hrig_phiMero_of_naturalBoundary_global_gamma_offOther_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hnb : ∀ z₀ ∈ frontier (filledJulia c₁), ¬ ContinuesAcross β (filledJulia c₁)ᶜ z₀)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_global_gamma_offOther_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₁ hγan₂ hγmatch hnb hinput)

/-- **NoRelation from empty-interior natural boundary and an off-other γ point.** This combines the
empty-interior natural-boundary source with local γ analyticity derived from `(filledJulia c₂)ᶜ`. -/
theorem noRelation_phiMero_of_emptyInterior_global_gamma_offOther_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_global_gamma_offOther_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₁ hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) hinput

/-- **hRigid from empty-interior natural boundary and an off-other γ point.** This is the hRigid package
for `noRelation_phiMero_of_emptyInterior_global_gamma_offOther_separable`. -/
theorem hrig_phiMero_of_emptyInterior_global_gamma_offOther_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (z₀ w₀ : ℂ),
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_global_gamma_offOther_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₁ hγan₂ hγmatch hinput)

/-- **Analytic branch-family continuation across a frontier point.** A full-degree separable analytic
fibre at a frontier point, plus preconnected punctured basin sectors, makes the basin branch `β` follow
one analytic root branch up to the frontier.  This creates the actual `ContinuesAcross β (K_c)ᶜ z₀`
predicate consumed by the Eremenko--van Strien/natural-boundary interface.  Unlike
`false_of_global_basin_branch_analytic`, this lemma does not use an empty-interior or modulus
contradiction; it constructs the continuation object itself. -/
theorem continuesAcross_of_global_basin_branch_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    {N : ℕ} {c z₀ : ℂ} {r : ℝ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hr : 0 < r) (hfront : z₀ ∈ frontier (filledJulia c))
    (htip : ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ))
    (hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ContinuesAcross β (filledJulia c)ᶜ z₀ := by
  obtain ⟨r', w, hr', hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ : ℝ := min r r' with hρdef
  have hρ : 0 < ρ := lt_min hr hr'
  have hρr : ρ ≤ r := min_le_left _ _
  have hρr' : ρ ≤ r' := min_le_right _ _
  set W : Set ℂ := Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ with hWdef
  have hWball' : W ⊆ Metric.ball z₀ r' := fun z hz => Metric.ball_subset_ball hρr' hz.1
  have hWball : W ⊆ Metric.ball z₀ r ∩ (filledJulia c)ᶜ :=
    fun z hz => ⟨Metric.ball_subset_ball hρr hz.1, hz.2⟩
  have hWbasin : W ⊆ (filledJulia c)ᶜ := inter_subset_right
  have hWc : IsPreconnected W := htip ρ hρ
  have hWnhds : W ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hρ)
    rwa [inter_comm] at h
  have hβcW : ContinuousOn β W := hβc.mono hWball
  have hβrelW : ∀ z ∈ W, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    fun z hz => hβrel z (hWball hz)
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  obtain ⟨z₁, hz₁⟩ := hNeBot.nonempty_of_mem hWnhds
  obtain ⟨w₀, d, hroot, hpart, hd, hβlim⟩ :=
    dendrite_branch_limit_analytic hN1 hr' hsep w hwc hwsep hwdeg hwrel
      hWball' hWbasin hWc hWnhds hβcW hβrelW hz₁
  have hballbasin : Metric.ball z₀ r ∩ (filledJulia c)ᶜ ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hr)
    rwa [inter_comm] at h
  have hβrel_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀,
      ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem hballbasin hβrel
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ :=
    exists_analyticAt_branch_analytic ha hroot hpart hd
  have hmatchβ : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, g z = β z :=
    branch_unique_within_analytic (fun i hi => (ha i hi).continuousAt) hpart hd
      hgAt.continuousAt hgz₀ hβlim
      (hgrel.filter_mono nhdsWithin_le_nhds) hβrel_filt
  exact ⟨g, hgAt, hmatchβ⟩

/-- Local-radius form of `continuesAcross_of_global_basin_branch_analytic`.  The branch-family proof
only needs preconnectedness at one radius, so a tip model valid below some positive `rTip` suffices. -/
theorem continuesAcross_of_global_basin_branch_analytic_localTip {a : ℕ → ℂ → ℂ} {s : Finset ℕ}
    {N : ℕ} {c z₀ : ℂ} {r rTip : ℝ} {β : ℂ → ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    (hr : 0 < r) (hrTip : 0 < rTip) (hfront : z₀ ∈ frontier (filledJulia c))
    (htip : ∀ ρ, 0 < ρ → ρ ≤ rTip →
      IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ))
    (hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    ContinuesAcross β (filledJulia c)ᶜ z₀ := by
  obtain ⟨r', w, hr', hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ : ℝ := min r (min r' rTip) with hρdef
  have hρ : 0 < ρ := lt_min hr (lt_min hr' hrTip)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρr' : ρ ≤ r' := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρTip : ρ ≤ rTip := le_trans (min_le_right _ _) (min_le_right _ _)
  set W : Set ℂ := Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ with hWdef
  have hWball' : W ⊆ Metric.ball z₀ r' := fun z hz => Metric.ball_subset_ball hρr' hz.1
  have hWball : W ⊆ Metric.ball z₀ r ∩ (filledJulia c)ᶜ :=
    fun z hz => ⟨Metric.ball_subset_ball hρr hz.1, hz.2⟩
  have hWbasin : W ⊆ (filledJulia c)ᶜ := inter_subset_right
  have hWc : IsPreconnected W := htip ρ hρ hρTip
  have hWnhds : W ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hρ)
    rwa [inter_comm] at h
  have hβcW : ContinuousOn β W := hβc.mono hWball
  have hβrelW : ∀ z ∈ W, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    fun z hz => hβrel z (hWball hz)
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  obtain ⟨z₁, hz₁⟩ := hNeBot.nonempty_of_mem hWnhds
  obtain ⟨w₀, d, hroot, hpart, hd, hβlim⟩ :=
    dendrite_branch_limit_analytic hN1 hr' hsep w hwc hwsep hwdeg hwrel
      hWball' hWbasin hWc hWnhds hβcW hβrelW hz₁
  have hballbasin : Metric.ball z₀ r ∩ (filledJulia c)ᶜ ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hr)
    rwa [inter_comm] at h
  have hβrel_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀,
      ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem hballbasin hβrel
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ :=
    exists_analyticAt_branch_analytic ha hroot hpart hd
  have hmatchβ : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, g z = β z :=
    branch_unique_within_analytic (fun i hi => (ha i hi).continuousAt) hpart hd
      hgAt.continuousAt hgz₀ hβlim
      (hgrel.filter_mono nhdsWithin_le_nhds) hβrel_filt
  exact ⟨g, hgAt, hmatchβ⟩

/-- **NoRelation from a common region and a branch-family continuation, using an abstract natural
boundary predicate.** This is the E-vS-ready analogue of
`noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable`: the branch-family
machinery creates `ContinuesAcross β (K_{c₁})ᶜ z₀`, and `hnb` rules it out. -/
theorem noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr, hVo, hVc,
    hUV, hVbasin, hsectorV, hγV, htip⟩ := hinput Q s hnt hEqOn
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
  exact (hnb z₀ hfront)
    (continuesAcross_of_global_basin_branch_analytic hsupp hN hN1 haAt
      (by simpa [a] using hlead) (by simpa [a] using hsep) hr hfront htip hβc hβrel)

/-- **Local-tip version of the common-region natural-boundary endpoint.**  This is the same
branch-family `NoRelation` theorem as
`noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable`, but it only
requires the punctured-basin preconnectedness below one positive local radius.  The continuation
construction shrinks its working ball before applying the local tip model. -/
theorem noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable_localTip
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
        ∃ (N : ℕ) (z₀ : ℂ) (r rTip : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → ρ ≤ rTip →
            IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨N, z₀, r, rTip, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr,
    hrTip, hVo, hVc, hUV, hVbasin, hsectorV, hγV, htip⟩ := hinput Q s hnt hEqOn
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
  exact (hnb z₀ hfront)
    (continuesAcross_of_global_basin_branch_analytic_localTip hsupp hN hN1 haAt
      (by simpa [a] using hlead) (by simpa [a] using hsep) hr hrTip hfront htip hβc hβrel)

/-- **hRigid from a common region and a branch-family continuation, using an abstract natural boundary
predicate.** This packages
`noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable`. -/
theorem hrig_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
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
    (noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb hinput)

/-- **NoRelation from a common-basin region and branch-family continuation, using an abstract natural
boundary predicate.** This derives `γ` analyticity on the common region from `V ⊆ (filledJulia c₂)ᶜ`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr, hVo, hVc,
        hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ := hinput Q s hnt hEqOn
      exact ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr, hVo, hVc,
        hUV, hVbasin₁, hsectorV, hγan₂.mono hVbasin₂, htip⟩)

/-- **Local-tip common-basin natural-boundary endpoint.**  This is the common-basin analogue of
`noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable_localTip`: the
caller only proves punctured-basin preconnectedness below a positive local radius, while `γ`
analyticity is still derived from `V ⊆ (filledJulia c₂)ᶜ`. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
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
        ∃ (N : ℕ) (z₀ : ℂ) (r rTip : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
          V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → ρ ≤ rTip →
            IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonRegion_gamma_offOther_branch_separable_localTip
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, z₀, r, rTip, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr,
        hrTip, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ :=
        hinput Q s hnt hEqOn
      exact ⟨N, z₀, r, rTip, V, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, hr,
        hrTip, hVo, hVc, hUV, hVbasin₁, hsectorV, hγan₂.mono hVbasin₂, htip⟩)

/-- **hRigid from a local-tip common-basin branch-family continuation.**  Packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip` as the
relative transcendence input used by connected q62. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
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
        ∃ (N : ℕ) (z₀ : ℂ) (r rTip : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ 0 < rTip ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧
          V ⊆ (filledJulia c₁)ᶜ ∧ V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → ρ ≤ rTip →
            IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable_localTip
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **hRigid from a common-basin region and branch-family continuation, using an abstract natural
boundary predicate.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable`. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **NoRelation from sparse generic crossing and common-basin target geometry, using an abstract natural
boundary predicate.** This is the E-vS-ready counterpart of
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing`: the separable frontier fibre is
created internally from sparse crossing data, and `hnb` supplies the final natural-boundary contradiction. -/
theorem noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing
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
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        hz₁, haccum, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂)
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁ haccum hgeom)

/-- **hRigid from sparse generic crossing and common-basin target geometry, using an abstract natural
boundary predicate.** This packages
`noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing`. -/
theorem hrig_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing
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
    (noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch hnb
      (hinput γ hγan₂ hγmatch))

/-- **NoRelation with the boundary value constructed from a local branch family.** In the
empty-interior case the natural-boundary contradiction no longer needs the selected fibre to supply
`w₀` or `Tendsto β ...`.  A separable full-degree fibre at a frontier point, together with preconnected
punctured basin sectors, forces the basin branch to follow one analytic root branch; this produces the
boundary value internally via `false_of_global_basin_branch_analytic`. -/
theorem noRelation_phiMero_of_emptyInterior_global_gamma_local_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨N, z₀, hsupp, hN, hN1, hlead, hsep, hfront, hγAt, htip⟩ :=
    hinput Q s hnt hEqOn
  let a : ℕ → ℂ → ℂ := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)
  have ha : ∀ i ∈ s, AnalyticOnNhd ℂ (a i) (filledJulia c₁)ᶜ := by
    intro i _hi
    exact analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q i)
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
  have hβrel_all : ∀ z ∈ (filledJulia c₁)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    relation_eq_zero_basin_analytic_of_open hUo hUne
      (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz)) ha hβan hrelU
  have hβc : ContinuousOn β (Metric.ball z₀ (1 : ℝ) ∩ (filledJulia c₁)ᶜ) :=
    hβan.continuousOn.mono inter_subset_right
  have hβrel : ∀ z ∈ Metric.ball z₀ (1 : ℝ) ∩ (filledJulia c₁)ᶜ,
      ∑ i ∈ s, a i z * (β z) ^ i = 0 := fun z hz => hβrel_all z hz.2
  have hβmod_local : ∀ z ∈ Metric.ball z₀ (1 : ℝ) ∩ (filledJulia c₁)ᶜ,
      ‖β z‖ = Real.exp (greenFunctionDyn c₁ z) := fun z hz => hβmod z hz.2
  have hK : z₀ ∈ filledJulia c₁ := mem_filledJulia_of_frontier hfront
  have hempty_local : Metric.ball z₀ (1 : ℝ) ∩ interior (filledJulia c₁) = ∅ := by
    rw [hempty, inter_empty]
  exact false_of_global_basin_branch_analytic hsupp hN hN1 haAt (by simpa [a] using hlead)
    (by simpa [a] using hsep) (by norm_num : (0 : ℝ) < 1) hK hempty_local htip
    hβc hβrel hβmod_local

/-- **hRigid with the boundary value constructed from a local branch family.** This packages
`noRelation_phiMero_of_emptyInterior_global_gamma_local_branch_separable`. -/
theorem hrig_phiMero_of_emptyInterior_global_gamma_local_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          AnalyticAt ℂ γ z₀ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_global_gamma_local_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan hγmatch hinput)

/-- **NoRelation with branch-family boundary value and γ analytic from the other basin.** This replaces
the local `AnalyticAt γ z₀` field by the geometric condition `z₀ ∈ (filledJulia c₂)ᶜ`. -/
theorem noRelation_phiMero_of_emptyInterior_global_gamma_offOther_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_global_gamma_local_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₁ hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨N, z₀, hsupp, hN, hN1, hlead, hsep, hfront, hz₀off, htip⟩ :=
        hinput Q s hnt hEqOn
      exact ⟨N, z₀, hsupp, hN, hN1, hlead, hsep, hfront, hγan₂ z₀ hz₀off, htip⟩)

/-- **hRigid with branch-family boundary value and γ analytic from the other basin.** This packages
`noRelation_phiMero_of_emptyInterior_global_gamma_offOther_branch_separable`. -/
theorem hrig_phiMero_of_emptyInterior_global_gamma_offOther_branch_separable
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (β γ : ℂ → ℂ)
    (hβan : AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ)
    (hβesc : ∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z)
    (hβmod : ∀ z ∈ (filledJulia c₁)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c₁ z))
    (hempty : interior (filledJulia c₁) = ∅)
    (hγan₁ : AnalyticOnNhd ℂ γ (filledJulia c₁)ᶜ)
    (hγan₂ : AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ)
    (hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z)
    (hinput : ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ frontier (filledJulia c₁) ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_global_gamma_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₁ hγan₂ hγmatch hinput)

/-- **NoRelation from a common basin region and a branch-family boundary value.** This is the
localized form of the empty-interior/off-other route: `γ` need not be analytic on the whole
`(filledJulia c₁)ᶜ`.  For each relation it is enough to supply one preconnected open region `V` inside
the `c₁` basin, containing the original carrier `U` and the local basin sector at the selected filled-Julia
point, on which `γ` is analytic.  The relation propagates across `V`, and the boundary value of `β` is
constructed internally from the separable full-degree fibre. -/
theorem noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          AnalyticOnNhd ℂ γ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  apply noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG
  intro Q s hnt hEqOn
  obtain ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hK, hz₀off, hr, hVo, hVc,
    hUV, hVbasin, hsectorV, hγV, htip⟩ := hinput Q s hnt hEqOn
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
    (by simpa [a] using hsep) hr hK hempty_local htip hβc hβrel hβmod_local

/-- **hRigid from a common basin region and a branch-family boundary value.** This packages
`noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable`. -/
theorem hrig_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
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
    (noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from a common-basin region and a branch-family boundary value.** This is the geometric
common-region wrapper: instead of supplying analyticity of `γ` on `V` per relation, it is derived from
`V ⊆ (filledJulia c₂)ᶜ` and the global `c₂` basin branch. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_emptyInterior_commonRegion_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan₂ hγmatch (by
      intro Q s hnt hEqOn
      obtain ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hK, hz₀off, hr, hVo, hVc,
        hUV, hVbasin₁, hVbasin₂, hsectorV, htip⟩ := hinput Q s hnt hEqOn
      exact ⟨N, z₀, r, V, hsupp, hN, hN1, hlead, hsep, hK, hz₀off, hr, hVo, hVc,
        hUV, hVbasin₁, hsectorV, hγan₂.mono hVbasin₂, htip⟩)

/-- **hRigid from a common-basin region and a branch-family boundary value.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable
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
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
      (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable
        hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
        hγan₂ hγmatch hinput)

/-- **NoRelation from sparse generic crossing and common-basin target geometry.** This consumes the
resultant/discriminant crossing theorem `exists_commonBasin_input_of_sparse_fibre_crossing`: the callback no
longer supplies a chosen full-degree separable fibre.  Instead, for each cleared relation it supplies a
preconnected analytic region `Ω` for the sparse coefficient family, one full-degree separable witness in
`Ω`, an accumulating target set `S`, and pointwise common-basin geometry on `S`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing
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
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        hz₁, haccum, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) hempty
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁ haccum hgeom)

/-- **NoRelation from sparse crossing and one global common-basin region.** This is the reduced-geometry
form of `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing`: the per-relation input
supplies a single open preconnected common-basin region `V`; pointwise target geometry only has to put the
local basin sectors into that `V`.  The separable frontier fibre is still created internally. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion
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
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ S, ∃ r : ℝ,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  exact noRelation_phiMero_of_naturalBoundary_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hγan₂ hγmatch
    (hnb_of_emptyInterior_modulus hempty hβmod) (by
      intro Q s hnt hEqOn
      obtain ⟨N, Ω, w, z₁, S, V, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        hz₁, haccum, hVo, hVc, hUV, hVbasin₁, hVbasin₂, hgeom⟩ :=
        hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_globalRegion
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) (V := V) hempty
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁ haccum hVo hVc hUV hVbasin₁ hVbasin₂ hgeom)

/-- **NoRelation from sparse crossing and the common-basin component containing `U`.** This is the
component-created version of
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion`: the per-relation
input no longer supplies an open preconnected region `V`, nor sector inclusion into it.  Lean constructs
`V` as the connected component of `(filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ` containing the carrier `U`, and
uses closure contact of that component at the target set to derive the local sector inclusion. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_commonComponent
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
      obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        hz₁, haccum, hcomponent, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_commonComponent
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) hempty hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁ haccum hcomponent hgeom)

/-- **NoRelation from sparse crossing and carrier-closure contact.** This is the carrier-closure
version of `noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_commonComponent`:
the per-relation input no longer mentions `connectedComponentIn`.  It only supplies that the target set
lies in `closure U`; preconnectedness of `U` inside the common basin creates the component-closure
payload internally. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_carrierClosure
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
      obtain ⟨N, Ω, w, z₁, S, hsupp, hN, hN1, hΩc, haΩ, hw, hleadw, hsepw,
        hz₁, haccum, hSclosure, hgeom⟩ := hinput Q s hnt hEqOn
      exact exists_commonBasin_frontier_input_of_sparse_fibre_crossing_emptyInterior_carrierClosure
        (U := U) (a := fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z))
        (s := s) (N := N) (c₁ := c₁) (c₂ := c₂) hempty hUo hUc hUne
        (fun z hz => escapeOpen_subset_compl_filledJulia c₁ (hU₁ hz))
        (fun z hz => escapeOpen_subset_compl_filledJulia c₂ (hU₂ hz))
        hN1 hsupp hN hΩc haΩ hw hleadw hsepw hz₁ haccum hSclosure hgeom)

/-- **hRigid from sparse generic crossing and common-basin target geometry.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing
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
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
      hγan₂ hγmatch hinput)

/-- **NoRelation from level-root branches and a common-basin region.** The `c₁` and `c₂` basin branches
are constructed internally from coherent level-root towers; the remaining per-relation datum is purely
the common-basin region and the separable full-degree filled-Julia fibre for the constructed `γ` branch. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
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
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hβanalytic hβpow hβne hβanchorEsc
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₂ γlev hγanalytic hγpow hγne hγanchorEsc
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan (fun z hz => hγesc z (hU₂ hz)) (hinput γ hγan hγesc)

/-- **hRigid from level-root branches and a common-basin region.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
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
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput)

/-- **NoRelation from level-root branches, sparse generic crossing, and common-basin geometry.** The
`c₁`/`c₂` basin branches are constructed internally from coherent level-root towers; the per-relation input
now supplies crossing data, not a pre-selected separable fibre. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing
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
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hβanalytic hβpow hβne hβanchorEsc
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₂ γlev hγanalytic hγpow hγne hγanchorEsc
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan (fun z hz => hγesc z (hU₂ hz)) (hinput γ hγan hγesc)

/-- **NoRelation from level-root branches, sparse crossing, and one global common-basin region.** This is
the reduced-geometry version of
`noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing`: level-root towers still
construct the `c₁`/`c₂` basin branches internally, while the per-relation sparse-crossing input supplies one
shared open preconnected common-basin region `V` plus local sector data for the accumulating target set. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing_globalRegion
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
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (Ω : Set ℂ) (w z₁ : ℂ) (S V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          IsPreconnected Ω ∧
          (∀ i ∈ s, AnalyticOnNhd ℂ
            (fun z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) Ω) ∧
          w ∈ Ω ∧
          (Q N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s w).Separable ∧
          z₁ ∈ Ω ∧
          (∃ᶠ z in 𝓝[≠] z₁, z ∈ S) ∧
          IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          (∀ z₀ ∈ S, ∃ r : ℝ,
            z₀ ∈ filledJulia c₁ ∧
            z₀ ∈ (filledJulia c₂)ᶜ ∧
            0 < r ∧
            Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
            (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ)))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₁ βlev hβanalytic hβpow hβne hβanchorEsc
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_level_roots_modulus c₂ γlev hγanalytic hγpow hγne hγanchorEsc
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing_globalRegion
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan (fun z hz => hγesc z (hU₂ hz)) (hinput γ hγan hγesc)

/-- **hRigid from level-root branches, sparse generic crossing, and common-basin geometry.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing
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
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput)

/-- **Connected-case `q62` endpoint from the common-basin level-root hRigid route.** This composes the
level-root/common-basin natural-boundary hRigid producer with the concrete connected carrier bridge,
yielding the actual `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` conclusion. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
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
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput)

/-- **Connected-case endpoint with `φ_{c₂}` transcendence produced internally.** This replaces the
abstract `Transcendental (RatFunc ℂ) (phiMero c₂ hU₂)` input by the current no-extra
non-strong-count repelling interface for `c₂`, then applies
`q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable_repellingG
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
    (hempty : interior (filledJulia c₁) = ∅)
    (hinput : ∀ (γ : ℂ → ℂ),
        AnalyticOnNhd ℂ γ (filledJulia c₂)ᶜ →
        (∀ z ∈ escapeOpen c₂, γ z = bottcherCoord c₂ z) →
        ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
        (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
        Set.EqOn (fun z => ∑ i ∈ s,
            ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
              * (bottcherCoord c₁ z) ^ i) 0 U →
        ∃ (N : ℕ) (z₀ : ℂ) (r : ℝ) (V : Set ℂ),
          s ⊆ Finset.range (N + 1) ∧ N ∈ s ∧ 1 ≤ N ∧
          (Q N).eval₂ (Polynomial.evalRingHom z₀) (γ z₀) ≠ 0 ∧
          (fibrePoly (fun i z => (Q i).eval₂ (Polynomial.evalRingHom z) (γ z)) s z₀).Separable ∧
          z₀ ∈ filledJulia c₁ ∧
          z₀ ∈ (filledJulia c₂)ᶜ ∧
          0 < r ∧ IsOpen V ∧ IsPreconnected V ∧ U ⊆ V ∧ V ⊆ (filledJulia c₁)ᶜ ∧
          V ⊆ (filledJulia c₂)ᶜ ∧
          Metric.ball z₀ r ∩ (filledJulia c₁)ᶜ ⊆ V ∧
          (∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c₁)ᶜ))) :
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
  exact q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_branch_separable
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput

/-- **Connected-case `q62` endpoint from level roots, sparse generic crossing, and common-basin geometry.**
This composes the crossing-driven hRigid producer with the concrete connected carrier bridge. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_crossing
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
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_level_roots_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput)

/-- **Connected-case crossing endpoint with `φ_{c₂}` transcendence produced internally.** This replaces
the abstract `hG` input by the current no-extra non-strong-count repelling interface for `c₂`, then applies
`q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_crossing`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_crossing_repellingG
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
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_emptyInterior_commonBasin_level_roots_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβpow hβne hβanchorEsc hγanalytic hγpow hγne hγanchorEsc hempty hinput

/-- **NoRelation from square-root towers, sparse generic crossing, and common-basin geometry.** The
square-root families now construct the modulus-carrying global basin branches directly; the `2^n` power
laws are internal to `exists_global_branch_of_sqrt_family_modulus`. -/
theorem noRelation_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
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
  obtain ⟨β, hβan, hβesc, _hβ0, hβmod⟩ :=
    exists_global_branch_of_sqrt_family_modulus c₁ βlev hβanalytic hβne hβanchorEsc hβsqrt
  obtain ⟨γ, hγan, hγesc, _hγ0, _hγmod⟩ :=
    exists_global_branch_of_sqrt_family_modulus c₂ γlev hγanalytic hγne hγanchorEsc hγsqrt
  exact noRelation_phiMero_of_emptyInterior_commonBasin_gamma_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG β γ hβan hβesc hβmod hempty
    hγan (fun z hz => hγesc z (hU₂ hz)) (hinput γ hγan hγesc)

/-- **hRigid from square-root towers, sparse generic crossing, and common-basin geometry.** This packages
`noRelation_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing`. -/
theorem hrig_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
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
    TranscendentalOverAdjoin (K := RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact transcendentalOverAdjoin_of_noRelation _ _
    (noRelation_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput)

/-- **Connected-case `q62` endpoint from square-root towers and sparse generic crossing.** This replaces
the level-root power-law hypotheses by the square-root recursion. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
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
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact q62_independence_connected_of_inputs hUo hUc hUne
    (phiAnalytic c₁ hU₁) (phiAnalytic c₂ hU₂) c₁ c₂ hne hx₁ hx₂ hG
    (hrig_phiMero_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
      hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hG βlev γlev
      hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput)

/-- **Connected-case square-root crossing endpoint with `φ_{c₂}` transcendence produced internally.**
This removes the abstract `hG` input using the current no-extra non-strong-count repelling interface. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_repellingG
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
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_standard_squarefree_budget_strongRoots_clearedDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput

/-- **Connected-case empty-interior square-root crossing with asymptotic `c₂` production.**
This is the empty-interior counterpart of
`q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_eventualG`:
the abstract `hG` input is produced internally from finite eventual supports for the non-strong and
multiplier-one fixed roots, plus pointwise eventual analytic-order bounds on the multiplier-one
support.  Lean converts analytic order to local duplicate-excess, takes the finite maximum, builds the
fixed content denominator witness from minimality, derives the root-defect bound, and supplies the
exponential domination by `2^p`. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_eventualG
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
        ∃ (E F : Finset ℂ),
          (∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧ multiplierOneFixedPointRoots c₂ p ⊆ F) ∧
          (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
            1 ≤ p ∧
              analyticOrderAt (fun y : ℂ => (fixedPointPoly c₂ p).eval y) z ≤
                ((Lz + 1 : ℕ) : ℕ∞)) ∧
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
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hG : Transcendental (RatFunc ℂ) (phiMero c₂ hU₂) :=
    phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseAnalyticOrder_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput

end Bottcher
