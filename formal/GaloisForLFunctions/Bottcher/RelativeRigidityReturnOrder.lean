import GaloisForLFunctions.Bottcher.RelativeRigidityHNBCrossing

open Polynomial Filter Topology Set Metric U0NaturalBoundary

namespace Bottcher

variable {U : Set ℂ}

/-- The finite-support hRigid payload in the form produced by the local parabolic return-order
bridge.  It packages:
* eventual finite support for multiplier-one roots;
* exact-period divisibility plus finite first-return order at each support point;
* eventual finite support for non-strong roots. -/
def RepellingReturnOrderEventualSupport (c : ℂ) (E F : Finset ℂ) : Prop :=
  (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
  (∀ z ∈ F, ∃ (q r : ℕ),
    (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p) ∧
    2 ≤ r ∧
    analyticOrderAt (fun y : ℂ => (quadratic c)^[q] y - y) z = (r : ℕ∞)) ∧
  (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)

/-- The still-lower finite-support hRigid payload: each multiplier-one support point is assigned an
exact period `q` and membership in the period-`q` multiplier-one locus.  The local return order is
then derived internally from the multiplier-one root condition. -/
def RepellingMemMultiplierOneEventualSupport (c : ℂ) (E F : Finset ℂ) : Prop :=
  (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
  (∀ z ∈ F, ∃ q : ℕ,
    1 ≤ q ∧
    z ∈ multiplierOneFixedPointRoots c q ∧
    (∀ p : ℕ, (quadratic c)^[p] z = z → q ∣ p)) ∧
  (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)

/-- Root-of-unity-safe multiplier-one period support.  Here `q` is exact only among
multiplier-one return periods, which is weaker than exactness among all fixed return periods and is
the general hRigid/q62-facing support predicate. -/
def RepellingMultiplierOnePeriodEventualSupport (c : ℂ) (E F : Finset ℂ) : Prop :=
  (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
  (∀ z ∈ F, ∃ q : ℕ,
    1 ≤ q ∧
    z ∈ multiplierOneFixedPointRoots c q ∧
    (∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p)) ∧
  (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)

/-- Minimal-period form of the finite-support hRigid payload.  The exact-period divisibility
condition is derived from `Function.minimalPeriod`, so callers only identify the minimal period of
each support point. -/
def RepellingMinimalPeriodEventualSupport (c : ℂ) (E F : Finset ℂ) : Prop :=
  (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
  (∀ z ∈ F, ∃ q : ℕ,
    1 ≤ q ∧
    z ∈ multiplierOneFixedPointRoots c q ∧
    Function.minimalPeriod (quadratic c) z = q) ∧
  (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E)

/-- Points in the period-`q` multiplier-one locus whose actual minimal period is exactly `q`. -/
noncomputable def minimalPeriodMultiplierOneRoots (c : ℂ) (q : ℕ) : Finset ℂ := by
  classical
  exact (multiplierOneFixedPointRoots c q).filter fun z =>
    1 ≤ q ∧ Function.minimalPeriod (quadratic c) z = q

theorem mem_minimalPeriodMultiplierOneRoots {c z : ℂ} {q : ℕ} :
    z ∈ minimalPeriodMultiplierOneRoots c q ↔
      z ∈ multiplierOneFixedPointRoots c q ∧
      1 ≤ q ∧
      Function.minimalPeriod (quadratic c) z = q := by
  classical
  simp [minimalPeriodMultiplierOneRoots]

/-- A finite set of minimal periods gives a concrete finite support. -/
noncomputable def finiteMinimalMultiplierOneSupport (c : ℂ) (S : Finset ℕ) : Finset ℂ :=
  S.biUnion fun q => minimalPeriodMultiplierOneRoots c q

theorem mem_finiteMinimalMultiplierOneSupport {c z : ℂ} {S : Finset ℕ} :
    z ∈ finiteMinimalMultiplierOneSupport c S ↔
      ∃ q ∈ S, z ∈ multiplierOneFixedPointRoots c q ∧
        1 ≤ q ∧
        Function.minimalPeriod (quadratic c) z = q := by
  classical
  simp [finiteMinimalMultiplierOneSupport, mem_minimalPeriodMultiplierOneRoots]

/-- Points in the period-`q` multiplier-one locus for which `q` is exact among multiplier-one
return periods. -/
noncomputable def exactMultiplierOnePeriodRoots (c : ℂ) (q : ℕ) : Finset ℂ := by
  classical
  exact (multiplierOneFixedPointRoots c q).filter fun z =>
    1 ≤ q ∧ ∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p

theorem mem_exactMultiplierOnePeriodRoots {c z : ℂ} {q : ℕ} :
    z ∈ exactMultiplierOnePeriodRoots c q ↔
      z ∈ multiplierOneFixedPointRoots c q ∧
      1 ≤ q ∧
      ∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p := by
  classical
  simp [exactMultiplierOnePeriodRoots]

/-- A finite set of exact multiplier-one return periods gives a concrete finite support. -/
noncomputable def finiteExactMultiplierOnePeriodSupport (c : ℂ) (S : Finset ℕ) : Finset ℂ :=
  S.biUnion fun q => exactMultiplierOnePeriodRoots c q

theorem mem_finiteExactMultiplierOnePeriodSupport {c z : ℂ} {S : Finset ℕ} :
    z ∈ finiteExactMultiplierOnePeriodSupport c S ↔
      ∃ q ∈ S, z ∈ multiplierOneFixedPointRoots c q ∧
        1 ≤ q ∧
        ∀ p : ℕ, z ∈ multiplierOneFixedPointRoots c p → q ∣ p := by
  classical
  simp [finiteExactMultiplierOnePeriodSupport, mem_exactMultiplierOnePeriodRoots]

/-- A finite set of exact multiplier-one return periods supplies the general multiplier-one-period
finite-support payload. -/
theorem repellingMultiplierOnePeriodEventualSupport_of_finiteExactMultiplierOnePeriodSupport
    {c : ℂ} {E : Finset ℂ} {T : Finset ℕ}
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ finiteExactMultiplierOnePeriodSupport c T)
    (hnonStrong : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    RepellingMultiplierOnePeriodEventualSupport c E
      (finiteExactMultiplierOnePeriodSupport c T) := by
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hz
  obtain ⟨q, _hqT, hzmult, hq, hmultExact⟩ :=
    (mem_finiteExactMultiplierOnePeriodSupport.mp hz)
  exact ⟨q, hq, hzmult, hmultExact⟩

/-- If a finite set of periods eventually covers all multiplier-one roots by actual minimal period,
it supplies the minimal-period finite-support payload. -/
theorem repellingMinimalPeriodEventualSupport_of_finiteMinimalPeriodSupport
    {c : ℂ} {E : Finset ℂ} {T : Finset ℕ}
    (hmultiplierOne : ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ finiteMinimalMultiplierOneSupport c T)
    (hnonStrong : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    RepellingMinimalPeriodEventualSupport c E (finiteMinimalMultiplierOneSupport c T) := by
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hz
  obtain ⟨q, _hqT, hzmult, hq, hmin⟩ := (mem_finiteMinimalMultiplierOneSupport.mp hz)
  exact ⟨q, hq, hzmult, hmin⟩

/-- Minimal-period support data implies the exact-period membership-form support payload. -/
theorem repellingMinimalPeriodEventualSupport_to_memMultiplierOne
    {c : ℂ} {E F : Finset ℂ}
    (h : RepellingMinimalPeriodEventualSupport c E F) :
    RepellingMemMultiplierOneEventualSupport c E F := by
  rcases h with ⟨hmultiplierOne, hmin, hnonStrong⟩
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hzF
  obtain ⟨q, hq, hzmult, hminq⟩ := hmin z hzF
  exact ⟨q, hq, hzmult, exactPeriod_dvd_of_quadratic_minimalPeriod_eq c z hminq⟩

/-- Membership-form support data implies the return-order support payload. -/
theorem repellingMemMultiplierOneEventualSupport_to_returnOrder
    {c : ℂ} {E F : Finset ℂ}
    (h : RepellingMemMultiplierOneEventualSupport c E F) :
    RepellingReturnOrderEventualSupport c E F := by
  rcases h with ⟨hmultiplierOne, hmem, hnonStrong⟩
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hzF
  obtain ⟨q, hq, hzmult, hexact⟩ := hmem z hzF
  obtain ⟨r, hr, horder⟩ :=
    exists_returnOrder_two_le_of_mem_multiplierOneFixedPointRoots c hq hzmult
  exact ⟨q, r, hexact, hr, horder⟩

/-- Minimal-period support data directly implies the return-order support payload. -/
theorem repellingMinimalPeriodEventualSupport_to_returnOrder
    {c : ℂ} {E F : Finset ℂ}
    (h : RepellingMinimalPeriodEventualSupport c E F) :
    RepellingReturnOrderEventualSupport c E F :=
  repellingMemMultiplierOneEventualSupport_to_returnOrder
    (repellingMinimalPeriodEventualSupport_to_memMultiplierOne h)

/-- Return-order support data implies the older pointwise analytic-order input consumed by the
existing connected q62 endpoints. -/
theorem repellingReturnOrderEventualSupport_to_pointwiseAnalyticOrder
    {c : ℂ} {E F : Finset ℂ}
    (h : RepellingReturnOrderEventualSupport c E F) :
    (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
    (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((Lz + 1 : ℕ) : ℕ∞)) ∧
    (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) := by
  rcases h with ⟨hmultiplierOne, hreturn, hnonStrong⟩
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hzF
  obtain ⟨q, r, hexact, hr, horder⟩ := hreturn z hzF
  exact ⟨r, eventually_analyticOrderAt_fixedPointPoly_eval_le_of_exact_period_returnOrder
    c z hexact hr horder⟩

/-- Multiplier-one-period support data implies the older pointwise analytic-order input consumed by
the existing connected q62 endpoints.  The local bound only needs multiplier-one-period divisibility:
when a fixed-point root is not multiplier-one it is simple, and when it is multiplier-one the supplied
divisibility makes it a positive multiple of the exact multiplier-one return. -/
theorem repellingMultiplierOnePeriodEventualSupport_to_pointwiseAnalyticOrder
    {c : ℂ} {E F : Finset ℂ}
    (h : RepellingMultiplierOnePeriodEventualSupport c E F) :
    (∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ multiplierOneFixedPointRoots c p ⊆ F) ∧
    (∀ z ∈ F, ∃ Lz : ℕ, ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        analyticOrderAt (fun y : ℂ => (fixedPointPoly c p).eval y) z ≤
          ((Lz + 1 : ℕ) : ℕ∞)) ∧
    (∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) := by
  rcases h with ⟨hmultiplierOne, hperiod, hnonStrong⟩
  refine ⟨hmultiplierOne, ?_, hnonStrong⟩
  intro z hzF
  obtain ⟨q, hq, hzmult, hmultExact⟩ := hperiod z hzF
  obtain ⟨r, hr, horder⟩ :=
    exists_returnOrder_two_le_of_mem_multiplierOneFixedPointRoots c hq hzmult
  exact ⟨r,
    eventually_analyticOrderAt_fixedPointPoly_eval_le_of_multiplierOne_period_returnOrder
      (c := c) (z := z) (q := q) (r := r) hmultExact hr horder⟩

/-- Absolute connected `φ_c` transcendence from the root-of-unity-safe multiplier-one-period support
predicate.  This is the q62-facing hRigid bridge for the general parabolic support case. -/
theorem phiMero_transcendental_of_repelling_eventually_multiplierOnePeriod_contentDenominator_noExtra_input
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
        ∃ (E F : Finset ℂ), RepellingMultiplierOnePeriodEventualSupport c E F) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_repelling_eventually_multiplierOne_pointwiseAnalyticOrder_contentDenominator_noExtra_input
    hUo hUc hUne hUinf c hU
  intro P hP0 hdeg hPrel hPmin hcount hconst
  obtain ⟨E, F, hEF⟩ := hinput P hP0 hdeg hPrel hPmin hcount hconst
  rcases repellingMultiplierOnePeriodEventualSupport_to_pointwiseAnalyticOrder hEF with
    ⟨hmultiplierOne, hbounds, hnonStrong⟩
  exact ⟨E, F, hmultiplierOne, hbounds, hnonStrong⟩

/-- Connected-case natural-boundary square-root crossing with the return-order hRigid payload.
This is the same q62 endpoint as
`q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_eventualG`,
but callers supply the sharper local data produced by
`eventually_multiplierOne_payload_of_eventually_support_and_exactPeriod_returnOrder`. -/
theorem q62_independence_connected_of_naturalBoundary_commonBasin_sqrt_family_offOther_crossing_returnOrderG
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
        ∃ (E F : Finset ℂ), RepellingReturnOrderEventualSupport c₂ E F)
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
    rcases repellingReturnOrderEventualSupport_to_pointwiseAnalyticOrder hEF with
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

/-- Empty-interior connected q62 endpoint with the return-order hRigid payload. -/
theorem q62_independence_connected_of_emptyInterior_commonBasin_sqrt_family_offOther_crossing_returnOrderG
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
        ∃ (E F : Finset ℂ), RepellingReturnOrderEventualSupport c₂ E F)
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
    rcases repellingReturnOrderEventualSupport_to_pointwiseAnalyticOrder hEF with
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

end Bottcher

namespace Bottcher

/-- If exact multiplier-one return periods are eventually bounded by `N`, then the concrete finite
support `finiteExactMultiplierOnePeriodSupport c (range (N+1))` eventually contains every
multiplier-one fixed root. -/
theorem eventually_multiplierOne_subset_finiteExactMultiplierOnePeriodSupport_of_eventually_exactPeriod_le
    {c : ℂ} {N : ℕ}
    (hperiod : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z ∈ multiplierOneFixedPointRoots c p, ∃ q : ℕ,
        q ≤ N ∧
        z ∈ multiplierOneFixedPointRoots c q ∧
        1 ≤ q ∧
        (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c m → q ∣ m)) :
    ∀ᶠ p : ℕ in atTop,
      1 ≤ p ∧
        multiplierOneFixedPointRoots c p ⊆
          finiteExactMultiplierOnePeriodSupport c (Finset.range (N + 1)) := by
  filter_upwards [hperiod] with p hp
  refine ⟨hp.1, ?_⟩
  intro z hz
  obtain ⟨q, hqle, hzq, hqpos, hqexact⟩ := hp.2 z hz
  rw [mem_finiteExactMultiplierOnePeriodSupport]
  exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hqle), hzq, hqpos, hqexact⟩

/-- Bounded exact multiplier-one return periods plus finite eventual non-strong support produce the
general root-of-unity-safe hRigid support predicate. -/
theorem repellingMultiplierOnePeriodEventualSupport_of_eventually_exactPeriod_le
    {c : ℂ} {E : Finset ℂ} {N : ℕ}
    (hperiod : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z ∈ multiplierOneFixedPointRoots c p, ∃ q : ℕ,
        q ≤ N ∧
        z ∈ multiplierOneFixedPointRoots c q ∧
        1 ≤ q ∧
        (∀ m : ℕ, z ∈ multiplierOneFixedPointRoots c m → q ∣ m))
    (hnonStrong : ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    RepellingMultiplierOnePeriodEventualSupport c E
      (finiteExactMultiplierOnePeriodSupport c (Finset.range (N + 1))) :=
  repellingMultiplierOnePeriodEventualSupport_of_finiteExactMultiplierOnePeriodSupport
    (eventually_multiplierOne_subset_finiteExactMultiplierOnePeriodSupport_of_eventually_exactPeriod_le
      hperiod)
    hnonStrong

end Bottcher
