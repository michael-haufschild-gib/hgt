/-
# Nguyen's Question 6.2 for one connected and one disconnected parameter

For `c₁ ∈ M ∖ {0,-2}` and `c₂ ∉ M` the Böttcher coordinates `φ_{c₁}, φ_{c₂}` are algebraically
independent over `ℂ(z)`.

The obstruction is the natural boundary of the single-valued coordinate `φ_{c₁}`; the multivalued
`φ_{c₂}` only has to be carried along.

* `0 ∈ K_{c₁} ∖ K_{c₂}`, so the far-field component `W` of `K_{c₁}ᶜ ∩ K_{c₂}ᶜ` accumulates at a
  Julia point `p` of `c₁` off `K_{c₂}`.
* A relation `∑ᵢ Qᵢ(z, φ_{c₂})·φ_{c₁}ⁱ = 0` near `∞` is a relation between the global branch of
  `φ_{c₁}` and a local branch of `φ_{c₂}`; it propagates through `W` along the branches of `φ_{c₂}`
  (`relBranchAt_of_preconnected`), together with the nonvanishing of the squarefree bad locus.
* On a disc around `p` inside the `c₂`-basin, `φ_{c₂}` has a single branch continuing the propagated
  one, the coefficients `Qᵢ(z, φ_{c₂})` are analytic, and the local natural-boundary step
  `false_of_relation_on_ball_component` applies.

Transcendence of `φ_{c₂}` over `ℂ(z)` on any far domain comes from the dyadic radical tower of the
disconnected coordinate, moved to the given domain by the identity theorem on the escape region.
-/
import GaloisForLFunctions.Bottcher.Q62BothConnectedIndependence
import GaloisForLFunctions.Bottcher.BottcherLocalBranch
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **Transcendence of a disconnected Böttcher coordinate on any far domain.** -/
theorem phiMero_transcendental_of_disconnected
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {c : ℂ} (hc : (0:ℂ) ∉ filledJulia c) (hU : U ⊆ escapeOpen c) :
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    Transcendental (RatFunc ℂ) (phiMero c hU) := by
  apply phiMero_transcendental_of_no_function_relation hUo hUc hUne hUinf c hU
  intro q hq0 hqrel
  obtain ⟨U', hU'o, hU'c, hU'ne, hU'inf, a₂, hU'esc, ha₂, htr⟩ :=
    bottcher_transcendental_of_escape c hc
  have ha₂eq : a₂ = phiAnalytic c hU'esc := Subtype.ext ha₂.symm
  subst ha₂eq
  refine no_eval₂_bottcher_relation_of_phiMero_transcendental hU'o hU'c hU'ne hU'inf c hU'esc htr
    q hq0 ?_
  obtain ⟨u, hu⟩ := hUne
  have hev : (fun z => q.eval₂ (Polynomial.evalRingHom z) (bottcherCoord c z)) =ᶠ[𝓝 u] 0 := by
    filter_upwards [hUo.mem_nhds hu] with z hz using hqrel hz
  have hf := analyticOnNhd_eval₂_bottcher c subset_rfl q
  exact (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_escapeOpen c).isPreconnected (hU hu) hev).mono hU'esc

/-- **The squarefree reduction with a bad locus valid for every substituted function.**  From a
nontrivial relation `∑ᵢ Qᵢ(z, φ_{c₂})·φ_{c₁}ⁱ = 0` on `U` it produces the squarefree relation
`∑ᵢ Q'ᵢ(z, φ_{c₂})·φ_{c₁}ⁱ = 0` of degree `N ≥ 1` and a nonzero `B ∈ ℂ[z][Y]` such that, for every
`γ`, off `B(z, γ z) = 0` the top coefficient `Q'_N(z, γ z)` is nonzero and the fibre is
separable. -/
theorem primitiveSqfreeBad_of_sparse_relation_uniform
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₂ : U ⊆ escapeOpen c₂)
    (hG : letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
          Transcendental (RatFunc ℂ) (phiMero c₂ hU₂))
    (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ)
    (hnt : ∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0)
    (hEqOn : Set.EqOn (fun z => ∑ i ∈ s,
        ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U) :
    ∃ (Q' : ℕ → Polynomial (Polynomial ℂ)) (s' : Finset ℕ) (N : ℕ)
      (B : Polynomial (Polynomial ℂ)),
      Set.EqOn (fun z => ∑ i ∈ s',
          ((Q' i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U ∧
      s' ⊆ Finset.range (N + 1) ∧ N ∈ s' ∧ 1 ≤ N ∧ B ≠ 0 ∧
      ∀ (γ : ℂ → ℂ) (w : ℂ), B.eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 →
        (Q' N).eval₂ (Polynomial.evalRingHom w) (γ w) ≠ 0 ∧
        (fibrePoly (fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z)) s' w).Separable := by
  let P := sparseRelationPoly Q s
  have hP0 : P ≠ 0 := by
    simpa [P] using sparseRelationPoly_ne_zero_of_hnt (U := U) c₂ hU₂ Q s hnt
  have hPzero : ∀ z ∈ U,
      P.eval₂ (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
        (bottcherCoord c₁ z) = 0 := by
    intro z hz
    rw [show P = sparseRelationPoly Q s from rfl, eval_sparseRelationPoly]
    exact hEqOn hz
  have hPrel : Set.EqOn (fun z => ∑ i ∈ P.support,
        ((P.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) 0 U := by
    intro z hz
    change (∑ i ∈ P.support,
        ((P.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
          * (bottcherCoord c₁ z) ^ i) = 0
    rw [← eval_sparseRelationPoly (fun i => P.coeff i) P.support z
      (bottcherCoord c₂ z) (bottcherCoord c₁ z)]
    rw [sparseRelationPoly_coeff_support_eq P]
    exact hPzero z hz
  have hPdeg : 1 ≤ P.natDegree :=
    one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hP0 hPrel
  obtain ⟨D, n, hD0, hDsq, _hDP, hPD⟩ := exists_squarefree_divisor_pow_CzY P hP0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have hdeg0 : P.natDegree = 0 := by
        have hle : P.natDegree ≤ (1 : Polynomial (Polynomial (Polynomial ℂ))).natDegree :=
          Polynomial.natDegree_le_of_dvd (by simpa using hPD) (by simp)
        simpa using hle
      omega
    · exact h
  have hDrel : Set.EqOn (fun z => ∑ i ∈ D.support,
        (D.coeff i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z) *
          (bottcherCoord c₁ z) ^ i) 0 U := by
    simpa [P] using
      (coeff_family_relation_zero_of_dvd_pow (U := U) P D hPD hn
        (bottcherCoord c₁) (bottcherCoord c₂) hPzero)
  have hdeg : 1 ≤ D.natDegree :=
    one_le_natDegree_of_coeff_family_relation_zero_of_transcendental
      hUo hUc hUne hUinf c₁ c₂ hU₂ hG hD0 hDrel
  exact ⟨fun i => D.coeff i, D.support, D.natDegree, squarefreeBadCzY D, hDrel,
    support_subset_range_natDegree_add_one_CzY D, natDegree_mem_support_of_ne_zero_CzY hD0, hdeg,
    squarefreeBadCzY_ne_zero_of_fractionField_separable D hD0 hdeg
      (fractionField_separable_of_squarefree_CzY D hDsq),
    fun γ w hB => squarefreeBadCzY_eval₂_ne_zero_topCoeff_and_fibrePoly_separable D γ hB⟩

/-- Substituting a holomorphic function into a polynomial in `ℂ[z][Y]` is analytic. -/
theorem analyticOnNhd_eval₂_of_differentiableOn (P : Polynomial (Polynomial ℂ)) {O : Set ℂ}
    {g : ℂ → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) :
    AnalyticOnNhd ℂ (fun y => P.eval₂ (Polynomial.evalRingHom y) (g y)) O :=
  analyticOnNhd_eval₂_of_analyticOnNhd (hg.analyticOnNhd hO) P

/-- **No bivariate relation between a connected and a disconnected Böttcher coordinate.** -/
theorem hno_of_mem_mandelbrot_of_disconnected
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂ : c₂ ∉ mandelbrot) :
    ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
      (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
      ¬ Set.EqOn (fun z => ∑ i ∈ s,
          ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U := by
  intro Q s hnt hEqOn
  have hc₂K : (0:ℂ) ∉ filledJulia c₂ := hc₂
  have hG := phiMero_transcendental_of_disconnected hUo hUc hUne hUinf hc₂K hU₂
  obtain ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc, hβmod, hψan, hψβ, -, -⟩ :=
    exists_connected_bottcher_package c₁ hc₁M
  obtain ⟨Q', s', N, B, hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation_uniform hUo hUc hUne hUinf c₁ c₂ hU₂ hG Q s hnt hEqOn
  -- the far-field component of the common basin
  obtain ⟨u, huU⟩ := id hUne
  have huE : u ∈ escapeOpen c₁ ∩ escapeOpen c₂ := ⟨hU₁ huU, hU₂ huU⟩
  have hu : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ huE.1, escapeOpen_subset_compl_filledJulia c₂ huE.2⟩
  set W := connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u with hWdef
  have hWo : IsOpen W := ((isClosed_filledJulia c₁).isOpen_compl.inter
    (isClosed_filledJulia c₂).isOpen_compl).connectedComponentIn
  have hWsub : W ⊆ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ := connectedComponentIn_subset _ _
  have hEW : escapeOpen c₁ ∩ escapeOpen c₂ ⊆ W :=
    (isConnected_escapeOpen_inter c₁ c₂).isPreconnected.subset_connectedComponentIn huE
      (fun y hy => ⟨escapeOpen_subset_compl_filledJulia c₁ hy.1,
        escapeOpen_subset_compl_filledJulia c₂ hy.2⟩)
  have hUW : U ⊆ W := fun z hz => hEW ⟨hU₁ hz, hU₂ hz⟩
  -- a Julia point of `c₁` off `K_{c₂}` in the closure of `W`
  obtain ⟨p, hpfr, hpoff, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component hu hc₁M hc₂K
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  obtain ⟨z₀, hz₀W, hz₀p⟩ := Metric.mem_closure_iff.mp hpcl r₀ hr₀
  have hz₀ball : z₀ ∈ ball p r₀ := by rw [mem_ball, dist_comm]; exact hz₀p
  -- the relation and the bad locus as properties of branches of `φ_{c₂}`
  set R : ℂ → ℂ → ℂ := fun y X => ∑ i ∈ s', (Q' i).eval₂ (Polynomial.evalRingHom y) X * (β y) ^ i
    with hRdef
  set S : ℂ → ℂ → ℂ := fun y X => B.eval₂ (Polynomial.evalRingHom y) X with hSdef
  have hR : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ W → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => R y (g y)) O := by
    intro O g hO hOW hg
    apply Finset.analyticOnNhd_fun_sum
    intro i _
    exact (analyticOnNhd_eval₂_of_differentiableOn (Q' i) hO hg).mul
      ((hβan.mono fun z hz => (hWsub (hOW hz)).1).pow i)
  have hS : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ W → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => S y (g y)) O :=
    fun O g hO _ hg => analyticOnNhd_eval₂_of_differentiableOn B hO hg
  -- the seed: `φ_{c₂}` itself on a disc in `U`
  obtain ⟨ρu, hρu, hρuU⟩ := Metric.isOpen_iff.mp hUo u huU
  have hseed : RelBranchAt c₂ W R S u := by
    refine ⟨ρu, hρu, hρuU.trans hUW, bottcherCoord c₂, isBasinBranch_bottcherCoord (hρuU.trans hU₂),
      fun y hy => ?_, ?_⟩
    · have hyU := hρuU hy
      have h1 := hEqOn' hyU
      simp only [Pi.zero_apply] at h1
      simp only [hRdef, hβesc y (hU₁ hyU)]
      exact h1
    · have hno := no_eval₂_bottcher_relation_of_phiMero_transcendental hUo hUc hUne hUinf c₂ hU₂ hG
        B hB0
      have hex : ∃ y ∈ U, B.eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hno fun y hy => hcon y hy
      exact exists_ne_zero_of_analyticOnNhd (analyticOnNhd_eval₂_bottcher c₂ hU₂ B) hUc isOpen_ball
        hρuU ⟨u, mem_ball_self hρu⟩ hex
  -- propagation to `z₀`
  obtain ⟨r₁, hr₁, hr₁W, g₁, hg₁, hRg₁, hSg₁⟩ :=
    relBranchAt_of_preconnected hWo isPreconnected_connectedComponentIn (fun z hz => (hWsub hz).2)
      hR hS hseed z₀ hz₀W
  -- the branch of `φ_{c₂}` on the disc around `p`
  obtain ⟨G, hGb, hGz₀⟩ := exists_isBasinBranch_ball hr₀sub z₀ (g₁ z₀)
  have hz₀r₁ : z₀ ∈ ball z₀ r₁ := mem_ball_self hr₁
  have hOo : IsOpen (ball z₀ r₁ ∩ ball p r₀) := isOpen_ball.inter isOpen_ball
  have hOc : IsPreconnected (ball z₀ r₁ ∩ ball p r₀) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hz₀O : z₀ ∈ ball z₀ r₁ ∩ ball p r₀ := ⟨hz₀r₁, hz₀ball⟩
  have hgG : EqOn g₁ G (ball z₀ r₁ ∩ ball p r₀) :=
    IsBasinBranch.eqOn_of_preconnected hOo hOc (inter_subset_right.trans hr₀sub)
      (hg₁.mono inter_subset_left) (hGb.mono inter_subset_right) hz₀O hGz₀.symm
  set a : ℕ → ℂ → ℂ := fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (G z) with hadef
  set b : ℂ → ℂ := fun z => B.eval₂ (Polynomial.evalRingHom z) (G z) with hbdef
  have haAn : ∀ i, AnalyticOnNhd ℂ (a i) (ball p r₀) := fun i =>
    analyticOnNhd_eval₂_of_differentiableOn (Q' i) isOpen_ball hGb.1
  have hbAn : AnalyticOnNhd ℂ b (ball p r₀) :=
    analyticOnNhd_eval₂_of_differentiableOn B isOpen_ball hGb.1
  obtain ⟨wstar, hwO, hbw⟩ : ∃ y ∈ ball z₀ r₁ ∩ ball p r₀, b y ≠ 0 := by
    obtain ⟨y, hyO, hy⟩ := exists_ne_zero_of_analyticOnNhd (hS _ g₁ isOpen_ball hr₁W hg₁.1)
      (convex_ball z₀ r₁).isPreconnected hOo inter_subset_left ⟨z₀, hz₀O⟩ hSg₁
    refine ⟨y, hyO, ?_⟩
    simp only [hbdef, ← hgG hyO]
    exact hy
  have hΔc : IsConnected (ball p r₀) := ⟨⟨p, mem_ball_self hr₀⟩, (convex_ball p r₀).isPreconnected⟩
  have hBdisc : IsDiscrete ({z | b z = 0} ∩ ball p r₀) := by
    have hcod := hbAn.preimage_zero_mem_codiscreteWithin hbw hwO.2 hΔc
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | b z = 0} : Set ℂ)ᶜ = b ⁻¹' {0}ᶜ := by ext z; simp
    rw [hset]; exact hcod
  -- the relation on the component of `K_{c₁}ᶜ ∩ ball p r₀` through `z₀`
  have hz₀K₁ : z₀ ∈ (filledJulia c₁)ᶜ := (hWsub hz₀W).1
  have hV₀sub : connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀ ⊆
      (filledJulia c₁)ᶜ ∩ ball p r₀ := connectedComponentIn_subset _ _
  have hrelV₀ : ∀ z ∈ connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀,
      ∑ i ∈ s', a i z * (β z) ^ i = 0 := by
    have han : AnalyticOnNhd ℂ (fun z => ∑ i ∈ s', a i z * (β z) ^ i)
        (connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀) := by
      apply Finset.analyticOnNhd_fun_sum
      intro i _
      exact ((haAn i).mono fun z hz => (hV₀sub hz).2).mul
        ((hβan.mono fun z hz => (hV₀sub hz).1).pow i)
    have hev : (fun z => ∑ i ∈ s', a i z * (β z) ^ i) =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hOo.mem_nhds hz₀O] with y hy
      have h1 := hRg₁ y hy.1
      simp only [hRdef, hgG hy] at h1
      exact h1
    exact fun z hz => han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn (mem_connectedComponentIn ⟨hz₀K₁, hz₀ball⟩) hev hz
  exact false_of_relation_on_ball_component hc₁M hc₁0 hc₁2 hhd hhe hfe hh0 hbridge hβan hβmod
    hψan hψβ hsupp hN hN1 haAn hbAn hBdisc (fun w _ hbw => hBgood G w hbw)
    (mem_filledJulia_of_frontier hpfr) ⟨hz₀K₁, hz₀ball⟩ hrelV₀

/-- **Nguyen's Question 6.2, mixed case.**  For `c₁ ∈ M ∖ {0,-2}` and `c₂ ∉ M` the Böttcher
coordinates are algebraically independent over `ℂ(z)`. -/
theorem noRelation_phiMero_of_mem_mandelbrot_of_disconnected
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂ : c₂ ∉ mandelbrot) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
    (phiMero_transcendental_of_disconnected hUo hUc hUne hUinf hc₂ hU₂)
    (hno_of_mem_mandelbrot_of_disconnected hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hc₁M hc₁0 hc₁2 hc₂)

/-- **Nguyen's Question 6.2, mixed case, other orientation.**  For `c₁ ∉ M` and
`c₂ ∈ M ∖ {0,-2}`. -/
theorem noRelation_phiMero_of_disconnected_of_mem_mandelbrot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁ : c₁ ∉ mandelbrot) (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  exact noRelation_symm (noRelation_phiMero_of_mem_mandelbrot_of_disconnected hUo hUc hUne hUinf
    c₂ c₁ hU₂ hU₁ hc₂M hc₂0 hc₂2 hc₁)

end Bottcher
