import GaloisForLFunctions.Bottcher.RelativeRigidityReturnOrder
import GaloisForLFunctions.Bottcher.ConnectedRepellingStrongRoots

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- Absolute connected `phi_c` transcendence from an eventual bound on exact multiplier-one return
periods.  This is the concrete finite-period form of the multiplier-one-period support predicate:
after the relation-dependent cutoff, every multiplier-one root has an exact multiplier-one period
`q ≤ N`, and non-strong roots have finite eventual support. -/
theorem phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (E : Finset ℂ) (N : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z ∈ multiplierOneFixedPointRoots c p, ∃ q : ℕ,
              q ≤ N ∧
              z ∈ multiplierOneFixedPointRoots c q ∧
              1 ≤ q ∧
              (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c m → q ∣ m)) ∧
          (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_multiplierOnePeriod_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst
  obtain ⟨E, N, hperiod, hnonStrong⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst
  exact ⟨E, finiteExactMultiplierOnePeriodSupport c (Finset.range (N + 1)),
    repellingMultiplierOnePeriodEventualSupport_of_eventually_exactPeriod_le hperiod hnonStrong⟩

/-- Absolute connected `phi_c` transcendence from an eventual bound on exact multiplier-one return
periods and an eventual cardinality bound on non-strong roots.  This is the finite-support-free
version of
`phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_contentDenominator_noExtra_input`. -/
theorem phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_cardBound_contentDenominator_noExtra_input
    {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c : ℂ) (hU : U ⊆ escapeOpen c)
    (hinput : ∀ (P : Polynomial (Polynomial ℂ)) (_hP0 : P ≠ 0)
        (_hdeg : 1 ≤ P.natDegree)
        (_hPrel : ∀ z ∈ U, ∑ i ∈ P.support,
          (P.coeff i).aeval z * (bottcherCoord c z) ^ i = 0)
        (_hPmin : ∀ R : Polynomial (Polynomial ℂ), R ≠ 0 →
          (∀ z ∈ U, ∑ i ∈ R.support,
            (R.coeff i).aeval z * (bottcherCoord c z) ^ i = 0) →
          P.natDegree ≤ R.natDegree)
        (_hcount : {z ∈ U | ∑ i ∈ (Polynomial.derivative P).support,
          ((Polynomial.derivative P).coeff i).aeval z * (bottcherCoord c z) ^ i = 0}.Countable)
        (_hconst : P.coeff 0 ≠ 0),
        ∃ (K N : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z ∈ multiplierOneFixedPointRoots c p, ∃ q : ℕ,
              q ≤ N ∧
              z ∈ multiplierOneFixedPointRoots c q ∧
              1 ≤ q ∧
              (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c m → q ∣ m)) ∧
          (∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ K)) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_multiplierOne_cardBound_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst
  obtain ⟨K, N, hperiod, hnonStrong⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst
  let F := finiteExactMultiplierOnePeriodSupport c (Finset.range (N + 1))
  have hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F :=
    eventually_multiplierOne_subset_finiteExactMultiplierOnePeriodSupport_of_eventually_exactPeriod_le
      hperiod
  have hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      z ∈ multiplierOneFixedPointRoots c q ∧
      (∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p) := by
    intro z hzF
    obtain ⟨q, _hqF, hzq, hqpos, hqexact⟩ :=
      (mem_finiteExactMultiplierOnePeriodSupport.mp hzF)
    exact ⟨q, hqpos, hzq, hqexact⟩
  obtain ⟨L, hpayload⟩ :=
    eventually_multiplierOne_payload_of_eventually_support_and_multiplierOnePeriod_memMultiplierOne
      c F hmultiplierOne hdata
  exact ⟨K, F, L, hpayload, hnonStrong⟩

/-- Eventual exact multiplier-one-period bounds plus eventual bounded non-strong count imply the
unbounded strong-root input used by the leanest absolute hRigid bridge. -/
theorem frequently_strongFixedPointRoots_card_gt_of_eventually_exactMultiplierOnePeriodBound_nonStrong_card_le
    (c : ℂ) (K N : ℕ)
    (hperiod : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z ∈ multiplierOneFixedPointRoots c p, ∃ q : ℕ,
        q ≤ N ∧
        z ∈ multiplierOneFixedPointRoots c q ∧
        1 ≤ q ∧
        (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c m → q ∣ m))
    (hnonStrong : ∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c p).card ≤ K) :
    ∀ A : ℕ, ∃ᶠ p : ℕ in atTop, A < (strongFixedPointRoots c p).card := by
  let F := finiteExactMultiplierOnePeriodSupport c (Finset.range (N + 1))
  have hmultiplierOne : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F :=
    eventually_multiplierOne_subset_finiteExactMultiplierOnePeriodSupport_of_eventually_exactPeriod_le
      hperiod
  have hdata : ∀ z ∈ F, ∃ q : ℕ,
      1 ≤ q ∧
      z ∈ multiplierOneFixedPointRoots c q ∧
      (∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p) := by
    intro z hzF
    obtain ⟨q, _hqF, hzq, hqpos, hqexact⟩ :=
      (mem_finiteExactMultiplierOnePeriodSupport.mp hzF)
    exact ⟨q, hqpos, hzq, hqexact⟩
  obtain ⟨L, hpayload⟩ :=
    eventually_multiplierOne_payload_of_eventually_support_and_multiplierOnePeriod_memMultiplierOne
      c F hmultiplierOne hdata
  exact
    frequently_strongFixedPointRoots_card_gt_of_eventually_multiplierOne_subset_nonStrong_card_le
      c F L K hpayload hnonStrong

/-- Connected-case natural-boundary square-root crossing with the root-of-unity-safe
multiplier-one-period hRigid payload. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_multiplierOnePeriodG
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
        ∃ (E F : Finset ℂ), RepellingMultiplierOnePeriodEventualSupport c₂ E F)
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ (2 : ℕ) = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ (2 : ℕ) = γlev n (quadratic c₂ z))
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
  apply q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_eventualG
    (βlev := βlev) (γlev := γlev)
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂
  · intro P hP0 hdeg hPrel hPmin hcount hconst
    obtain ⟨E, F, hEF⟩ := hGinput P hP0 hdeg hPrel hPmin hcount hconst
    rcases repellingMultiplierOnePeriodEventualSupport_to_pointwiseAnalyticOrder hEF with
      ⟨hmultiplierOne, hbounds, hnonStrong⟩
    exact ⟨E, F, hmultiplierOne, hbounds, hnonStrong⟩
  · exact hβanalytic
  · exact hβne
  · exact hβanchorEsc
  · exact hβsqrt
  · exact hγanalytic
  · exact hγne
  · exact hγanchorEsc
  · exact hγsqrt
  · exact hnb
  · exact hinput

/-- Empty-interior connected q62 endpoint with the root-of-unity-safe multiplier-one-period hRigid
payload. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_multiplierOnePeriodG
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
        ∃ (E F : Finset ℂ), RepellingMultiplierOnePeriodEventualSupport c₂ E F)
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ (2 : ℕ) = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ (2 : ℕ) = γlev n (quadratic c₂ z))
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
  apply q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_eventualG
    (βlev := βlev) (γlev := γlev)
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂
  · intro P hP0 hdeg hPrel hPmin hcount hconst
    obtain ⟨E, F, hEF⟩ := hGinput P hP0 hdeg hPrel hPmin hcount hconst
    rcases repellingMultiplierOnePeriodEventualSupport_to_pointwiseAnalyticOrder hEF with
      ⟨hmultiplierOne, hbounds, hnonStrong⟩
    exact ⟨E, F, hmultiplierOne, hbounds, hnonStrong⟩
  · exact hβanalytic
  · exact hβne
  · exact hβanchorEsc
  · exact hβsqrt
  · exact hγanalytic
  · exact hγne
  · exact hγanchorEsc
  · exact hγsqrt
  · exact hempty
  · exact hinput

/-- Natural-boundary connected q62 endpoint from an eventual exact multiplier-one-period bound and
an eventual cardinality bound on non-strong roots.  This is the direct q62-facing form of
`phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_cardBound_contentDenominator_noExtra_input`. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG
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
        ∃ (K N : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z ∈ multiplierOneFixedPointRoots c₂ p, ∃ q : ℕ,
              q ≤ N ∧
              z ∈ multiplierOneFixedPointRoots c₂ q ∧
              1 ≤ q ∧
              (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c₂ m → q ∣ m)) ∧
          (∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c₂ p).card ≤ K))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ (2 : ℕ) = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ (2 : ℕ) = γlev n (quadratic c₂ z))
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
    phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_cardBound_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hnb hinput

/-- Empty-interior connected q62 endpoint from an eventual exact multiplier-one-period bound and
an eventual cardinality bound on non-strong roots. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_exactMultiplierOnePeriodBoundCardG
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
        ∃ (K N : ℕ),
          (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
            ∀ z ∈ multiplierOneFixedPointRoots c₂ p, ∃ q : ℕ,
              q ≤ N ∧
              z ∈ multiplierOneFixedPointRoots c₂ q ∧
              1 ≤ q ∧
              (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c₂ m → q ∣ m)) ∧
          (∀ᶠ p : ℕ in atTop, (nonStrongFixedPointRoots c₂ p).card ≤ K))
    (βlev γlev : ℕ → ℂ → ℂ)
    (hβanalytic : ∀ n, AnalyticOnNhd ℂ (βlev n) (escapeLevel c₁ n))
    (hβne : ∀ n, ∀ z ∈ escapeLevel c₁ n, βlev n z ≠ 0)
    (hβanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₁, βlev n z = bottcherCoord c₁ z)
    (hβsqrt : ∀ n, ∀ z ∈ escapeLevel c₁ (n + 1),
      (βlev (n + 1) z) ^ (2 : ℕ) = βlev n (quadratic c₁ z))
    (hγanalytic : ∀ n, AnalyticOnNhd ℂ (γlev n) (escapeLevel c₂ n))
    (hγne : ∀ n, ∀ z ∈ escapeLevel c₂ n, γlev n z ≠ 0)
    (hγanchorEsc : ∀ n, ∀ z ∈ escapeOpen c₂, γlev n z = bottcherCoord c₂ z)
    (hγsqrt : ∀ n, ∀ z ∈ escapeLevel c₂ (n + 1),
      (γlev (n + 1) z) ^ (2 : ℕ) = γlev n (quadratic c₂ z))
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
    phiMero_transcendental_of_repelling_eventually_exactMultiplierOnePeriodBound_cardBound_contentDenominator_noExtra_input
      hUo hUc hUne hUinf c₂ hU₂ (by
        intro P hP0 hdeg hPrel hPmin hcount hconst
        exact hGinput P hP0 hdeg hPrel hPmin hcount hconst)
  exact q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing
    hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂ hG βlev γlev
    hβanalytic hβne hβanchorEsc hβsqrt hγanalytic hγne hγanchorEsc hγsqrt hempty hinput

end Bottcher
