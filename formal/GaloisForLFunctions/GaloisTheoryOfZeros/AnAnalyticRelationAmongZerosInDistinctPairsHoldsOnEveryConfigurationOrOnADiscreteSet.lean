import GaloisForLFunctions.GaloisTheoryOfZeros.TheConfigurationsOfZerosInDistinctPairsOverTheForwardTimesAreConnected
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions

/-!
# An analytic relation among zeros in distinct pairs holds on every configuration or on a discrete set

The configurations `(τ, z₁, …, zₙ)` of zeros of `H_τ` in distinct pairs over the forward times off
the branch times form a connected set, and near each configuration they are the graph of analytic
functions of the time. So they form an irreducible analytic curve:

* **Analytic charts** (`exists_analyticAt_configuration_chart`). Near a configuration `x` every
  configuration is `(τ, r₁(τ), …, rₙ(τ))` with `rᵢ` analytic at the time of `x`.
* **Identity theorem** (`forall_eq_zero_or_forall_eventually_ne_zero`). Let `F` be a function of
  `(τ, z₁, …, zₙ)` that is analytic at every configuration. Then `F` vanishes on every
  configuration, or every configuration has a neighbourhood in which `F` vanishes at no other
  configuration.
* **Polynomial relations with analytic coefficients**
  (`eq_zero_of_frequently_eval_eq_zero`). Let `P_τ` be a polynomial in `n` variables of bounded
  support whose coefficients are analytic functions of the forward time. If `P_τ(z₁, …, zₙ) = 0`
  on configurations that accumulate at a configuration, then `P_τ = 0` at every forward time off
  the branch times: zeros in distinct pairs are algebraically independent over the analytic
  functions of the time.

Proof. The implicit function theorem gives the charts. Along a chart `F` is an analytic function
of the time, so it vanishes near the configuration or at no other nearby configuration. The
configurations near which `F` vanishes form an open and closed subset of the connected set of
configurations.
-/

open Complex Set Filter Topology Metric
open RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## Analytic charts -/

/-- **The analytic chart of a simple zero.** Near a simple zero `(τ₀, z₀)` the zeros of the
family in a disc around `z₀` are the values of one function of the time, analytic at `τ₀`. -/
theorem exists_analyticAt_zero_chart {τ₀ z₀ : ℂ} (h0 : complexHeat τ₀ z₀ = 0)
    (h1 : deriv (complexHeat τ₀) z₀ ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r τ₀ ∧ r τ₀ = z₀ ∧ ∃ ρ > 0, ∀ᶠ τ in 𝓝 τ₀,
      complexHeat τ (r τ) = 0 ∧ ∀ z ∈ ball z₀ ρ, complexHeat τ z = 0 → z = r τ := by
  have hfd : (fderiv ℂ (fun p : ℂ × ℂ => complexHeat p.1 p.2) (τ₀, z₀)) (0, 1) ≠ 0 := by
    have hd := (analyticAt_complexHeat (τ₀, z₀)).differentiableAt.hasFDerivAt
    have hline : HasDerivAt (fun z : ℂ => (τ₀, z)) ((0 : ℂ), (1 : ℂ)) z₀ :=
      (hasDerivAt_const z₀ τ₀).prodMk (hasDerivAt_id z₀)
    have h2 := hd.comp_hasDerivAt z₀ hline
    have h3 : ((fun p : ℂ × ℂ => complexHeat p.1 p.2) ∘ fun z : ℂ => (τ₀, z)) =
        complexHeat τ₀ := rfl
    rw [h3] at h2
    rwa [h2.deriv] at h1
  obtain ⟨r, hr, hr0, hrz⟩ := parametric_holo_implicit
    (f := fun p : ℂ × ℂ => complexHeat p.1 p.2) (analyticAt_complexHeat (τ₀, z₀)) h0 hfd
  obtain ⟨W, hW, hτW, ρ, hρ, ζ, -, -, hchart⟩ := exists_simple_zero_chart h0 h1
  refine ⟨r, hr, hr0, ρ, hρ, ?_⟩
  have hball : ∀ᶠ τ in 𝓝 τ₀, r τ ∈ ball z₀ ρ := by
    have h := hr.continuousAt.tendsto
    rw [hr0] at h
    exact h.eventually_mem (ball_mem_nhds z₀ hρ)
  filter_upwards [hrz, hball, hW.mem_nhds hτW] with τ g1 g2 g3
  exact ⟨g1, fun z hz hzz =>
    ((hchart τ g3).2.2.2 z hz hzz).trans ((hchart τ g3).2.2.2 (r τ) g2 g1).symm⟩

variable {n : ℕ}

/-- **Near a configuration the configurations are the graph of analytic functions of the
time.** -/
theorem exists_analyticAt_configuration_chart {x : ℂ × (Fin n → ℂ)}
    (hx : x ∈ forwardPairConfigurations n) :
    ∃ r : ℂ → Fin n → ℂ, (∀ i, AnalyticAt ℂ (fun τ => r τ i) x.1) ∧ r x.1 = x.2 ∧
      ∀ᶠ y in 𝓝[forwardPairConfigurations n] x, y.2 = r y.1 := by
  obtain ⟨⟨-, hb, hz⟩, -⟩ : (0 < x.1.re ∧ x.1 ∉ branchTimes ∧
      ∀ i, complexHeat x.1 (x.2 i) = 0) ∧ ∀ i j, i ≠ j → x.2 j ≠ x.2 i ∧ x.2 j ≠ -x.2 i := hx
  have hch : ∀ i, ∃ r : ℂ → ℂ, AnalyticAt ℂ r x.1 ∧ r x.1 = x.2 i ∧ ∃ ρ > 0, ∀ᶠ τ in 𝓝 x.1,
      complexHeat τ (r τ) = 0 ∧ ∀ z ∈ ball (x.2 i) ρ, complexHeat τ z = 0 → z = r τ := fun i =>
    exists_analyticAt_zero_chart (hz i)
      (deriv_complexHeat_ne_zero_of_not_mem_branchTimes hb (hz i))
  choose r hr hr0 ρ hρ hev using hch
  refine ⟨fun τ i => r i τ, hr, funext hr0, ?_⟩
  -- near `x` the time lies in every chart and the `i`-th zero in the `i`-th disc
  have h1 : ∀ i, ∀ᶠ y in 𝓝[forwardPairConfigurations n] x,
      ∀ z ∈ ball (x.2 i) (ρ i), complexHeat y.1 z = 0 → z = r i y.1 := fun i =>
    ((continuous_fst.tendsto x).eventually ((hev i).mono fun τ h => h.2)).filter_mono
      nhdsWithin_le_nhds
  have h2 : ∀ i, ∀ᶠ y in 𝓝[forwardPairConfigurations n] x,
      y.2 i ∈ ball (x.2 i) (ρ i) := fun i =>
    ((((continuous_apply i).comp continuous_snd).tendsto x).eventually_mem
      (ball_mem_nhds _ (hρ i))).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_all.2 h1, eventually_all.2 h2, self_mem_nhdsWithin] with y g1 g2 hy
  exact funext fun i => g1 i (y.2 i) (g2 i) (hy.1.2.2 i)

/-! ## The identity theorem on the configurations -/

/-- At a configuration an analytic function vanishes at all nearby configurations or at no other
nearby configuration. -/
theorem eventually_eq_zero_or_eventually_ne_zero_of_analyticAt {F : ℂ × (Fin n → ℂ) → ℂ}
    {x : ℂ × (Fin n → ℂ)} (hx : x ∈ forwardPairConfigurations n) (hF : AnalyticAt ℂ F x) :
    (∀ᶠ y in 𝓝[forwardPairConfigurations n] x, F y = 0) ∨
      ∀ᶠ y in 𝓝[forwardPairConfigurations n \ {x}] x, F y ≠ 0 := by
  obtain ⟨r, hr, hr0, hloc⟩ := exists_analyticAt_configuration_chart hx
  -- the function along the chart is analytic in the time
  have hg : AnalyticAt ℂ (fun τ => F (τ, r τ)) x.1 := by
    have hmap : AnalyticAt ℂ (fun τ : ℂ => (τ, r τ)) x.1 := analyticAt_id.prod (AnalyticAt.pi hr)
    have hFx : AnalyticAt ℂ F ((fun τ : ℂ => (τ, r τ)) x.1) := by
      have e : (fun τ : ℂ => (τ, r τ)) x.1 = x := Prod.ext rfl hr0
      rw [e]
      exact hF
    exact AnalyticAt.comp (g := F) (f := fun τ : ℂ => (τ, r τ)) hFx hmap
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with h | h
  · left
    have h' : ∀ᶠ y in 𝓝[forwardPairConfigurations n] x, F (y.1, r y.1) = 0 :=
      ((continuous_fst.tendsto x).eventually h).filter_mono nhdsWithin_le_nhds
    filter_upwards [h', hloc] with y hy1 hy2
    have e : F (y.1, y.2) = 0 := by
      rw [hy2]
      exact hy1
    exact e
  · right
    have h' : ∀ᶠ y in 𝓝[forwardPairConfigurations n \ {x}] x,
        y.1 ≠ x.1 → F (y.1, r y.1) ≠ 0 :=
      ((continuous_fst.tendsto x).eventually (eventually_nhdsWithin_iff.1 h)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [h', hloc.filter_mono (nhdsWithin_mono x sdiff_subset),
      self_mem_nhdsWithin] with y hy1 hy2 hy3
    -- a configuration of the chart over the same time is `x`
    have hne : y.1 ≠ x.1 := fun e => hy3.2 (Prod.ext e (by rw [hy2, e, hr0]))
    have e := hy1 hne
    rw [← hy2] at e
    exact e

/-- **An analytic function that vanishes on configurations accumulating at a configuration
vanishes on every configuration.** -/
theorem forall_eq_zero_of_frequently_eq_zero {F : ℂ × (Fin n → ℂ) → ℂ}
    (hF : ∀ x ∈ forwardPairConfigurations n, AnalyticAt ℂ F x) {x₀ : ℂ × (Fin n → ℂ)}
    (hx₀ : x₀ ∈ forwardPairConfigurations n)
    (hfreq : ∃ᶠ y in 𝓝[forwardPairConfigurations n \ {x₀}] x₀, F y = 0) :
    ∀ x ∈ forwardPairConfigurations n, F x = 0 := by
  classical
  -- the configurations near which the function vanishes form an open and closed set
  have hf : ContinuousOn (fun x : ℂ × (Fin n → ℂ) =>
      decide (∀ᶠ y in 𝓝[forwardPairConfigurations n] x, F y = 0))
      (forwardPairConfigurations n) := by
    intro x hx
    by_cases h : ∀ᶠ y in 𝓝[forwardPairConfigurations n] x, F y = 0
    · exact (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : ℂ × (Fin n → ℂ) => true) _ x).congr_of_eventuallyEq
        ((eventually_eventually_nhdsWithin.2 h).mono fun y hy => decide_eq_true hy)
        (decide_eq_true h)
    · have hne := eventually_nhdsWithin_iff.1
        ((eventually_eq_zero_or_eventually_ne_zero_of_analyticAt hx (hF x hx)).resolve_left h)
      refine (continuousWithinAt_const : ContinuousWithinAt
        (fun _ : ℂ × (Fin n → ℂ) => false) _ x).congr_of_eventuallyEq
        (eventually_nhdsWithin_iff.2 (hne.mono fun y hy hyC => decide_eq_false fun hyV => ?_))
        (decide_eq_false h)
      by_cases e : y = x
      · rw [e] at hyV
        exact h hyV
      · exact hy ⟨hyC, e⟩ (hyV.self_of_nhdsWithin hyC)
  have h₀ : ∀ᶠ y in 𝓝[forwardPairConfigurations n] x₀, F y = 0 :=
    (eventually_eq_zero_or_eventually_ne_zero_of_analyticAt hx₀ (hF x₀ hx₀)).resolve_right
      fun hne => hfreq hne
  intro x hx
  have e := (isConnected_forwardPairConfigurations n).isPreconnected.constant hf hx hx₀
  exact (of_decide_eq_true (e.trans (decide_eq_true h₀))).self_of_nhdsWithin hx

/-- **The identity theorem on the configurations.** A function that is analytic at every
configuration of `n` zeros in distinct pairs vanishes on every configuration, or each
configuration has a neighbourhood in which the function vanishes at no other configuration. -/
theorem forall_eq_zero_or_forall_eventually_ne_zero {F : ℂ × (Fin n → ℂ) → ℂ}
    (hF : ∀ x ∈ forwardPairConfigurations n, AnalyticAt ℂ F x) :
    (∀ x ∈ forwardPairConfigurations n, F x = 0) ∨
      ∀ x ∈ forwardPairConfigurations n,
        ∀ᶠ y in 𝓝[forwardPairConfigurations n \ {x}] x, F y ≠ 0 := by
  by_cases h : ∃ x ∈ forwardPairConfigurations n,
      ∃ᶠ y in 𝓝[forwardPairConfigurations n \ {x}] x, F y = 0
  · obtain ⟨x, hx, hfr⟩ := h
    exact Or.inl (forall_eq_zero_of_frequently_eq_zero hF hx hfr)
  · refine Or.inr fun x hx => ?_
    by_contra hc
    exact h ⟨x, hx, (not_eventually.1 hc).mono fun y hy => not_not.1 hy⟩

/-! ## Polynomial relations with analytic coefficients -/

/-- **Zeros in distinct pairs are algebraically independent over the analytic functions of the
time.** Let `P_τ` be polynomials in `n` variables with supports in one finite set and with
coefficients analytic in the forward time. If `P_τ(z₁, …, zₙ) = 0` on configurations that
accumulate at a configuration, then `P_τ = 0` at every forward time off the branch times. -/
theorem eq_zero_of_frequently_eval_eq_zero {P : ℂ → MvPolynomial (Fin n) ℂ}
    (S : Finset (Fin n →₀ ℕ)) (hS : ∀ τ, (P τ).support ⊆ S)
    (hP : ∀ m, ∀ τ : ℂ, 0 < τ.re → AnalyticAt ℂ (fun τ => (P τ).coeff m) τ)
    {x₀ : ℂ × (Fin n → ℂ)} (hx₀ : x₀ ∈ forwardPairConfigurations n)
    (hfreq : ∃ᶠ y in 𝓝[forwardPairConfigurations n \ {x₀}] x₀,
      MvPolynomial.eval y.2 (P y.1) = 0) {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    P τ = 0 := by
  -- the relation is a finite sum of analytic coefficients times monomials
  have hform : (fun x : ℂ × (Fin n → ℂ) => MvPolynomial.eval x.2 (P x.1)) =
      fun x => ∑ m ∈ S, (P x.1).coeff m * ∏ i, x.2 i ^ m i := by
    funext x
    rw [MvPolynomial.eval_eq']
    exact Finset.sum_subset (hS x.1) fun m _ hm => by
      rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  have hF : ∀ x ∈ forwardPairConfigurations n,
      AnalyticAt ℂ (fun x : ℂ × (Fin n → ℂ) => MvPolynomial.eval x.2 (P x.1)) x := by
    intro x hx
    obtain ⟨⟨hx0, -, -⟩, -⟩ : (0 < x.1.re ∧ x.1 ∉ branchTimes ∧
      ∀ i, complexHeat x.1 (x.2 i) = 0) ∧ ∀ i j, i ≠ j → x.2 j ≠ x.2 i ∧ x.2 j ≠ -x.2 i := hx
    rw [hform]
    refine (Finset.analyticAt_sum S
      (f := fun m (x : ℂ × (Fin n → ℂ)) => (P x.1).coeff m * ∏ i, x.2 i ^ m i)
      fun m _ => ?_).congr (Eventually.of_forall fun y => Finset.sum_apply _ _ _)
    refine AnalyticAt.mul ((hP m x.1 hx0).comp analyticAt_fst) ?_
    refine (Finset.analyticAt_prod Finset.univ
      (f := fun i (x : ℂ × (Fin n → ℂ)) => x.2 i ^ m i)
      fun i _ => ?_).congr (Eventually.of_forall fun y => Finset.prod_apply _ _ _)
    have hi : AnalyticAt ℂ (fun x : ℂ × (Fin n → ℂ) => x.2 i) x :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt _).comp
        analyticAt_snd
    exact hi.pow (m i)
  have hall := forall_eq_zero_of_frequently_eq_zero hF hx₀ hfreq
  exact eq_zero_of_forall_eval_eq_zero hτ hb fun z hz => hall (τ, z) hz

end GaloisForLFunctions.GaloisTheoryOfZeros
