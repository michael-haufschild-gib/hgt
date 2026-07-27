import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.MeromorphicRestrictionHypertranscendence
import GaloisForLFunctions.HTGeometry.EllipticHypertranscendenceFreeProof

/-!
# Every doubly periodic meromorphic germ is differentially algebraic

An element of the global meromorphic field fixed by two `ℝ`-independent translations is
differentially algebraic over the embedded rational coordinate field.  Nothing is assumed about the
element beyond the two invariances: no entirety, no growth bound, no presentation by theta
functions.

The proof realizes the germ as an honest fraction `A / B` of entire functions, transports the two
invariances into genuine periodicity of the canonical normal form of `A / B`, applies the
unconditional elliptic differential-algebraicity theorem to that normal form, and then descends the
resulting relation back into the field through a disc on which `B` does not vanish, where the
fraction is analytic and the jet bridge applies.

* **`differentialAlgebraicOver_of_translation_fixed`**;
* **`differentialAlgebraicOver_of_mem_ellipticMeroField`** — the elliptic field
  `ellipticMeroField τ` consists of differentially algebraic elements whenever `1, τ` are
  `ℝ`-independent.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

local instance ellipticMeroFieldDADomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticMeroFieldDADifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticMeroFieldDARatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

/-! ## A nonvanishing chart -/

/-- Every complex ball of positive radius is infinite. -/
theorem infinite_ball (z₀ : ℂ) {r : ℝ} (hr : 0 < r) : (Metric.ball z₀ r).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => z₀ + ((r / ((n : ℝ) + 2) : ℝ) : ℂ)) ?_ ?_
  · intro m n hmn
    simp only [add_right_inj, Complex.ofReal_inj] at hmn
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    field_simp at hmn
    have h3 : (m : ℝ) = (n : ℝ) := by linarith
    exact_mod_cast h3
  · intro n
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h2 : 0 < r / ((n : ℝ) + 2) := by positivity
    have h1 : r / ((n : ℝ) + 2) < r := by
      rw [div_lt_iff₀ hn]
      nlinarith
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h2]
    exact h1

/-- A nonzero entire germ has a disc on which every representative is nonvanishing. -/
theorem exists_ball_ne_zero_of_ne_zero {b : analyticSubring (Set.univ : Set ℂ)} (hb : b ≠ 0)
    {B : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ)) :
    ∃ (z₀ : ℂ) (r : ℝ), 0 < r ∧ ∀ z ∈ Metric.ball z₀ r, B z ≠ 0 := by
  obtain ⟨z₀, hz₀⟩ := exists_univGermEval_ne_zero_of_ne_zero hb
  have hB0 : B z₀ ≠ 0 := by
    rw [← hBb] at hz₀
    simpa using hz₀
  have hcont : ContinuousAt B z₀ := (hB z₀ (Set.mem_univ z₀)).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hB0)
  exact ⟨z₀, r, hr, fun z hz => hball (Metric.mem_ball.mp hz)⟩

/-! ## Restriction of an entire germ -/

/-- Restricting an entire germ to a subdomain keeps the same representative. -/
theorem restrictAnalytic_analyticFunctionElement {V : Set ℂ} (hV : V ⊆ (Set.univ : Set ℂ))
    {C : analyticSubring (Set.univ : Set ℂ)} {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Set.univ : Set ℂ))
    (hGc : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) G = (C : Germ (𝓟 Set.univ) ℂ)) :
    restrictAnalytic hV C = analyticFunctionElement G (hG.mono hV) := by
  apply Subtype.ext
  change (restrictGermHom hV) (C : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) =
    ((G : ℂ → ℂ) : Germ (𝓟 V) ℂ)
  rw [← hGc]
  change (↑G : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto id
      (tendsto_principal_principal.mpr (fun _ hx => hV hx)) = ((G : ℂ → ℂ) : Germ (𝓟 V) ℂ)
  rw [Germ.coe_compTendsto]
  rfl

/-! ## The theorem -/

set_option maxHeartbeats 1000000 in
/-- **Descending a normal-form relation into the field.**  If the canonical normal form of a
fraction of entire representatives satisfies an algebraic differential equation, then the fraction
is differentially algebraic as an element of the global meromorphic differential field.  The
relation is transported through a disc on which the denominator does not vanish, where the fraction
is analytic and the jet bridge applies, and pulled back along the injective restriction
embedding. -/
theorem differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb0 : b ≠ 0)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ))
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (hDA : DifferentiallyAlgebraic
      (toMeromorphicNFOn (fun z => A z / B z) (Set.univ : Set ℂ))) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) := by
  set H : ℂ → ℂ := fun z => A z / B z with hHdef
  have hHmer : MeromorphicOn H (Set.univ : Set ℂ) :=
    hA.meromorphicOn.div hB.meromorphicOn
  set F : ℂ → ℂ := toMeromorphicNFOn H (Set.univ : Set ℂ) with hFdef
  have hNF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  obtain ⟨n, P, hP0, hPrel⟩ := hDA
  obtain ⟨z₀, r, hr, hBne⟩ := exists_ball_ne_zero_of_ne_zero hb0 hB hBb
  set V : Set ℂ := Metric.ball z₀ r with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball
  have hVc : IsPreconnected V := (convex_ball z₀ r).isPreconnected
  have hVne : V.Nonempty := ⟨z₀, Metric.mem_ball_self hr⟩
  have hVinf : V.Infinite := infinite_ball z₀ hr
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  letI := meroFieldDifferential hVo hVc hVne
  have hAV : AnalyticOnNhd ℂ A V := hA.mono (Set.subset_univ V)
  have hBV : AnalyticOnNhd ℂ B V := hB.mono (Set.subset_univ V)
  have hHV : AnalyticOnNhd ℂ H V := hAV.div hBV (fun z hz => hBne z hz)
  have hrelV : ∀ z ∈ V, MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) H z) P = 0 := by
    intro z hz
    have hHan : AnalyticAt ℂ H z := hHV z hz
    have hHord : 0 ≤ meromorphicOrderAt H z :=
      hHan.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hHan
    have hFord : 0 ≤ meromorphicOrderAt F z := by
      rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hHmer (Set.mem_univ z)]
      exact hHord
    have hFan : AnalyticAt ℂ F z :=
      (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hFord
    have heq : F =ᶠ[𝓝[≠] z] H := by
      rw [hFdef]
      exact hHmer.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    have hjets : (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) F z) =
        fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) H z := by
      funext j
      exact Filter.EventuallyEq.iteratedDeriv_eq (j : ℕ)
        (eventuallyEq_nhds_of_nhdsNE_of_continuousAt heq hFan.continuousAt hHan.continuousAt)
    have := hPrel z
    rwa [hjets] at this
  have hDAV : DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement H hHV) :=
    differentialAlgebraicOver_analyticMeroElement_of_relation hVo hVc hVne hVinf hHV hP0 hrelV
  have hBVne : analyticMeroElement B hBV ≠ 0 := by
    intro hzero
    have hgerm : analyticFunctionElement B hBV = 0 := by
      apply IsFractionRing.injective (analyticSubring V) (meroField V)
      rw [map_zero]
      exact hzero
    have hval := congrArg Subtype.val hgerm
    rw [ZeroMemClass.coe_zero] at hval
    change ((B : ℂ → ℂ) : Germ (𝓟 V) ℂ) = 0 at hval
    rw [← Germ.coe_zero, Germ.coe_eq] at hval
    exact hBne z₀ (Metric.mem_ball_self hr)
      (eventually_principal.mp hval z₀ (Metric.mem_ball_self hr))
  have hHB : analyticMeroElement H hHV * analyticMeroElement B hBV =
      analyticMeroElement A hAV := by
    rw [← analyticMeroElement_mul hHV hBV]
    have hfun : analyticFunctionElement (fun z => H z * B z) (hHV.mul hBV) =
        analyticFunctionElement A hAV := by
      apply Subtype.ext
      change ((fun z => H z * B z : ℂ → ℂ) : Germ (𝓟 V) ℂ) = ((A : ℂ → ℂ) : Germ (𝓟 V) ℂ)
      rw [Germ.coe_eq]
      refine eventually_principal.mpr fun z hz => ?_
      have hBz : B z ≠ 0 := hBne z hz
      simp only [hHdef]
      field_simp
    unfold analyticMeroElement
    rw [hfun]
  set ρ := restrictMeroAlgHomRatFunc (Set.subset_univ V) isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hVo hVc hVne hVinf with hρdef
  have hρa : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a) =
      analyticMeroElement A hAV := by
    rw [hρdef]
    change Bottcher.restrictMeroHom (Set.subset_univ V) isOpen_univ isPreconnected_univ
      Set.univ_nonempty hVo hVc hVne _ = _
    rw [Bottcher.restrictMeroHom_algebraMap, restrictAnalytic_analyticFunctionElement _ hA hAa]
    rfl
  have hρb : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) =
      analyticMeroElement B hBV := by
    rw [hρdef]
    change Bottcher.restrictMeroHom (Set.subset_univ V) isOpen_univ isPreconnected_univ
      Set.univ_nonempty hVo hVc hVne _ = _
    rw [Bottcher.restrictMeroHom_algebraMap, restrictAnalytic_analyticFunctionElement _ hB hBb]
    rfl
  have hρx : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b) =
      analyticMeroElement H hHV := by
    rw [map_div₀, hρa, hρb, ← hHB]
    field_simp
  by_contra hxnot
  have hHTρ := hypertranscendentalOver_restrictMeroAlgHomRatFunc (Set.subset_univ V) isOpen_univ
    isPreconnected_univ Set.univ_nonempty Set.infinite_univ hVo hVc hVne hVinf _ hxnot
  rw [← hρdef, hρx] at hHTρ
  exact hHTρ hDAV

/-- **A meromorphic germ fixed by two `ℝ`-independent translations is differentially algebraic.** -/
theorem differentialAlgebraicOver_of_translation_fixed
    {α β : ℂ} (hindep : LinearIndependent ℝ ![α, β])
    {x : meroField (Set.univ : Set ℂ)}
    (hα : addTranslationMeroEquiv α x = x) (hβ : addTranslationMeroEquiv β x = x) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (analyticSubring Set.univ) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨A, hA, hAa⟩ := a.2
  obtain ⟨B, hB, hBb⟩ := b.2
  refine differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn
    hb0 hA hB hAa hBb ?_
  set H : ℂ → ℂ := fun z => A z / B z with hHdef
  have hHmer : MeromorphicOn H (Set.univ : Set ℂ) :=
    hA.meromorphicOn.div hB.meromorphicOn
  set F : ℂ → ℂ := toMeromorphicNFOn H (Set.univ : Set ℂ) with hFdef
  have hNF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hperα : Function.Periodic F α :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hHmer α
      (fun z => fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed α hb0 hB hAa hBb hα z)
  have hperβ : Function.Periodic F β :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hHmer β
      (fun z => fraction_eventually_periodic_of_addTranslationMeroEquiv_fixed β hb0 hB hAa hBb hβ z)
  have hlat : ∀ p ∈ (⟨α, β, hindep⟩ : PeriodPair).lattice, Function.Periodic F p := by
    intro p hp
    refine periodic_of_mem_span_range ![α, β] (fun i => ?_) p ?_
    · fin_cases i
      · exact hperα
      · exact hperβ
    · rw [range_cons_two]
      exact hp
  exact differentiallyAlgebraic_of_lattice_periodic_meromorphicNF ⟨α, β, hindep⟩ hNF hlat

/-- **The elliptic meromorphic field is differentially algebraic.**  If `1` and `τ` are
`ℝ`-independent, every germ fixed by both translations satisfies an algebraic differential equation
over the rational coordinate field. -/
theorem differentialAlgebraicOver_of_mem_ellipticMeroField {τ : ℂ}
    (hindep : LinearIndependent ℝ ![(1 : ℂ), τ])
    {x : meroField (Set.univ : Set ℂ)} (hx : x ∈ ellipticMeroField τ) :
    DifferentialAlgebraicOver (RatFunc ℂ) x :=
  differentialAlgebraicOver_of_translation_fixed hindep hx.1 hx.2

end

end GaloisForLFunctions.HTGeometry
