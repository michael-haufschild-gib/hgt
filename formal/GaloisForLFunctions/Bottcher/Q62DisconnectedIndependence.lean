/-
# Nguyen's Question 6.2 for two disconnected parameters, and for all parameters

For distinct `c₁, c₂ ∉ M` the Böttcher coordinates `φ_{c₁}, φ_{c₂}` are algebraically independent
over `ℂ(z)`.  Suppose `∑ᵢ Qᵢ(z, φ_{c₂})·φ_{c₁}ⁱ = 0` near `∞` and (after swapping)
`x ∈ K_{c₁} ∖ K_{c₂}`.

* The squarefree relation propagates along pairs of branches of `φ_{c₁}, φ_{c₂}` through the
  far-field component `W` of `K_{c₁}ᶜ ∩ K_{c₂}ᶜ` to a point `z₀` near a Julia point
  `p ∈ ∂K_{c₁}` off `K_{c₂}`; on a disc around `p` in the `c₂`-basin the `c₂`-branch is
  single-valued and the coefficients `aᵢ = Qᵢ(z, φ_{c₂})` are analytic.
* Inside the component `V₀` of `K_{c₁}ᶜ ∩ disc` through `z₀`, the relation `∑ aᵢ gⁱ = 0` is carried
  by branches `g` of `φ_{c₁}`.  At a point `q ∈ ∂V₀` off the discrete bad locus, the roots of the
  relation are `N` analytic branches `w_k` on a small disc `Δ`, and near a point `z₁ ∈ V₀ ∩ Δ` the
  carried branch is some `w_k`; hence `w_k` is a single-valued, nowhere vanishing branch of `φ_{c₁}`
  on the component `V` of `K_{c₁}ᶜ ∩ Δ` through `z₁`, with `‖w_k‖ = C e^{G_{c₁}}` there.
* A small piece `E` of `K_{c₁}` around a point `q' ∈ ∂V ∩ Δ` (`exists_small_piece`) lies in `Δ`, has
  `E ∖ K_{c₁}` connected and meeting `V`, so `E ∖ K_{c₁} ⊆ V`.  Then `w_k / C` is analytic near `q'`
  with modulus `e^{G_{c₁}}` off the nowhere dense `K_{c₁}`, against the Green-modulus minimum
  principle (`no_green_modulus_continuation_dense`).

Together with the connected and mixed cases this settles all nonexceptional parameters.
-/
import GaloisForLFunctions.Bottcher.Q62MixedIndependence
import GaloisForLFunctions.Bottcher.DisconnectedCantorPieces
import GaloisForLFunctions.Bottcher.DendriteBoundary

open Polynomial Filter Topology Set Metric

namespace Bottcher

variable {U : Set ℂ}

/-- **No bivariate relation between two disconnected Böttcher coordinates**, in the orientation
where some point of `K_{c₁}` lies off `K_{c₂}`. -/
theorem hno_of_disconnected_of_mem_filledJulia_not_mem
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁ : c₁ ∉ mandelbrot) (hc₂ : c₂ ∉ mandelbrot)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff : x ∉ filledJulia c₂) :
    ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
      (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
      ¬ Set.EqOn (fun z => ∑ i ∈ s,
          ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U := by
  intro Q s hnt hEqOn
  have hc₂K : (0:ℂ) ∉ filledJulia c₂ := hc₂
  have hG := phiMero_transcendental_of_disconnected hUo hUc hUne hUinf hc₂K hU₂
  obtain ⟨Q', s', N, B, hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation_uniform hUo hUc hUne hUinf c₁ c₂ hU₂ hG Q s hnt hEqOn
  have hK₁ : IsClosed (filledJulia c₁) := isClosed_filledJulia c₁
  -- the far-field component of the common basin
  obtain ⟨u, huU⟩ := id hUne
  have huE : u ∈ escapeOpen c₁ ∩ escapeOpen c₂ := ⟨hU₁ huU, hU₂ huU⟩
  have hu : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ huE.1, escapeOpen_subset_compl_filledJulia c₂ huE.2⟩
  set W := connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u with hWdef
  have hWo : IsOpen W := (hK₁.isOpen_compl.inter
    (isClosed_filledJulia c₂).isOpen_compl).connectedComponentIn
  have hWsub : W ⊆ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ := connectedComponentIn_subset _ _
  have hEW : escapeOpen c₁ ∩ escapeOpen c₂ ⊆ W :=
    (isConnected_escapeOpen_inter c₁ c₂).isPreconnected.subset_connectedComponentIn huE
      (fun y hy => ⟨escapeOpen_subset_compl_filledJulia c₁ hy.1,
        escapeOpen_subset_compl_filledJulia c₂ hy.2⟩)
  have hUW : U ⊆ W := fun z hz => hEW ⟨hU₁ hz, hU₂ hz⟩
  -- a Julia point of `c₁` off `K_{c₂}` in the closure of `W`
  obtain ⟨p, hpfr, hpoff, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component hu hxK hxoff
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  obtain ⟨z₀, hz₀W, hz₀p⟩ := Metric.mem_closure_iff.mp hpcl r₀ hr₀
  have hz₀ball : z₀ ∈ ball p r₀ := by rw [mem_ball, dist_comm]; exact hz₀p
  have hz₀K₁ : z₀ ∈ (filledJulia c₁)ᶜ := (hWsub hz₀W).1
  -- the relation and the bad locus as properties of pairs of branches
  set R : ℂ → ℂ → ℂ → ℂ := fun y X Y =>
    ∑ i ∈ s', (Q' i).eval₂ (Polynomial.evalRingHom y) Y * X ^ i with hRdef
  set S : ℂ → ℂ → ℂ → ℂ := fun y X Y => B.eval₂ (Polynomial.evalRingHom y) Y * X with hSdef
  have hR : ∀ (O : Set ℂ) (g₁ g₂ : ℂ → ℂ), IsOpen O → O ⊆ W → DifferentiableOn ℂ g₁ O →
      DifferentiableOn ℂ g₂ O → AnalyticOnNhd ℂ (fun y => R y (g₁ y) (g₂ y)) O := by
    intro O g₁ g₂ hO _ hg₁ hg₂
    apply Finset.analyticOnNhd_fun_sum
    intro i _
    exact (analyticOnNhd_eval₂_of_differentiableOn (Q' i) hO hg₂).mul
      ((hg₁.analyticOnNhd hO).pow i)
  have hS : ∀ (O : Set ℂ) (g₁ g₂ : ℂ → ℂ), IsOpen O → O ⊆ W → DifferentiableOn ℂ g₁ O →
      DifferentiableOn ℂ g₂ O → AnalyticOnNhd ℂ (fun y => S y (g₁ y) (g₂ y)) O :=
    fun O g₁ g₂ hO _ hg₁ hg₂ =>
      (analyticOnNhd_eval₂_of_differentiableOn B hO hg₂).mul (hg₁.analyticOnNhd hO)
  -- the seed: the two Böttcher coordinates on a disc in `U`
  obtain ⟨ρu, hρu, hρuU⟩ := Metric.isOpen_iff.mp hUo u huU
  have hseed : RelBranchPairAt c₁ c₂ W R S u := by
    refine ⟨ρu, hρu, hρuU.trans hUW, bottcherCoord c₁, bottcherCoord c₂,
      isBasinBranch_bottcherCoord (hρuU.trans hU₁), isBasinBranch_bottcherCoord (hρuU.trans hU₂),
      fun y hy => ?_, ?_⟩
    · have h1 := hEqOn' (hρuU hy)
      simp only [Pi.zero_apply] at h1
      exact h1
    · have hno := no_eval₂_bottcher_relation_of_phiMero_transcendental hUo hUc hUne hUinf c₂ hU₂ hG
        B hB0
      have hex : ∃ y ∈ U, B.eval₂ (Polynomial.evalRingHom y) (bottcherCoord c₂ y) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hno fun y hy => hcon y hy
      obtain ⟨y, hy, hyB⟩ := exists_ne_zero_of_analyticOnNhd
        (analyticOnNhd_eval₂_bottcher c₂ hU₂ B) hUc isOpen_ball hρuU ⟨u, mem_ball_self hρu⟩ hex
      exact ⟨y, hy, mul_ne_zero hyB (bottcherCoord_ne_zero c₁ y)⟩
  -- propagation to `z₀`
  obtain ⟨r₁, hr₁, hr₁W, g₁, g₂, hg₁, hg₂, hRg, hSg⟩ :=
    relBranchPairAt_of_preconnected hWo isPreconnected_connectedComponentIn
      (fun z hz => (hWsub hz).1) (fun z hz => (hWsub hz).2) hR hS hseed z₀ hz₀W
  have hr₁K₁ : ball z₀ r₁ ⊆ (filledJulia c₁)ᶜ := fun z hz => (hWsub (hr₁W hz)).1
  have hg₁ne : ∀ y ∈ ball z₀ r₁, g₁ y ≠ 0 := by
    obtain ⟨y, hy, hyS⟩ := hSg
    exact hg₁.ne_zero_of_ne_zero isOpen_ball (convex_ball z₀ r₁).isPreconnected hr₁K₁ hy
      (right_ne_zero_of_mul hyS)
  -- the branch of `φ_{c₂}` on the disc around `p`
  obtain ⟨G₂, hG₂b, hG₂z₀⟩ := exists_isBasinBranch_ball hr₀sub z₀ (g₂ z₀)
  have hOo : IsOpen (ball z₀ r₁ ∩ ball p r₀) := isOpen_ball.inter isOpen_ball
  have hOc : IsPreconnected (ball z₀ r₁ ∩ ball p r₀) :=
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hz₀O : z₀ ∈ ball z₀ r₁ ∩ ball p r₀ := ⟨mem_ball_self hr₁, hz₀ball⟩
  have hgG : EqOn g₂ G₂ (ball z₀ r₁ ∩ ball p r₀) :=
    IsBasinBranch.eqOn_of_preconnected hOo hOc (inter_subset_right.trans hr₀sub)
      (hg₂.mono inter_subset_left) (hG₂b.mono inter_subset_right) hz₀O hG₂z₀.symm
  set a : ℕ → ℂ → ℂ := fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (G₂ z) with hadef
  set b : ℂ → ℂ := fun z => B.eval₂ (Polynomial.evalRingHom z) (G₂ z) with hbdef
  have haAn : ∀ i, AnalyticOnNhd ℂ (a i) (ball p r₀) := fun i =>
    analyticOnNhd_eval₂_of_differentiableOn (Q' i) isOpen_ball hG₂b.1
  have hbAn : AnalyticOnNhd ℂ b (ball p r₀) :=
    analyticOnNhd_eval₂_of_differentiableOn B isOpen_ball hG₂b.1
  obtain ⟨wstar, hwO, hbw⟩ : ∃ y ∈ ball z₀ r₁ ∩ ball p r₀, b y ≠ 0 := by
    obtain ⟨y, hyO, hy⟩ := exists_ne_zero_of_analyticOnNhd
      (hS _ g₁ g₂ isOpen_ball hr₁W hg₁.1 hg₂.1) (convex_ball z₀ r₁).isPreconnected hOo
      inter_subset_left ⟨z₀, hz₀O⟩ hSg
    refine ⟨y, hyO, fun hb0 => hy ?_⟩
    change B.eval₂ (Polynomial.evalRingHom y) (g₂ y) * g₁ y = 0
    rw [hgG hyO]
    change b y * g₁ y = 0
    rw [hb0, zero_mul]
  have hΔc : IsConnected (ball p r₀) := ⟨⟨p, mem_ball_self hr₀⟩, (convex_ball p r₀).isPreconnected⟩
  have hBdisc : IsDiscrete ({z | b z = 0} ∩ ball p r₀) := by
    have hcod := hbAn.preimage_zero_mem_codiscreteWithin hbw hwO.2 hΔc
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | b z = 0} : Set ℂ)ᶜ = b ⁻¹' {0}ᶜ := by ext z; simp
    rw [hset]; exact hcod
  -- the relation along the branches of `φ_{c₁}` inside `V₀`
  set V₀ := connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀ with hV₀def
  have hV₀o : IsOpen V₀ := (hK₁.isOpen_compl.inter isOpen_ball).connectedComponentIn
  have hV₀sub : V₀ ⊆ (filledJulia c₁)ᶜ ∩ ball p r₀ := connectedComponentIn_subset _ _
  set R₁ : ℂ → ℂ → ℂ := fun y X => ∑ i ∈ s', a i y * X ^ i with hR₁def
  set S₁ : ℂ → ℂ → ℂ := fun _ X => X with hS₁def
  have hR₁ : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ V₀ → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => R₁ y (g y)) O := by
    intro O g hO hOV hg
    apply Finset.analyticOnNhd_fun_sum
    intro i _
    exact ((haAn i).mono fun z hz => (hV₀sub (hOV hz)).2).mul ((hg.analyticOnNhd hO).pow i)
  have hS₁ : ∀ (O : Set ℂ) (g : ℂ → ℂ), IsOpen O → O ⊆ V₀ → DifferentiableOn ℂ g O →
      AnalyticOnNhd ℂ (fun y => S₁ y (g y)) O := fun O g hO _ hg => hg.analyticOnNhd hO
  obtain ⟨r', hr', hr'O⟩ := Metric.isOpen_iff.mp hOo z₀ hz₀O
  have hr'V₀ : ball z₀ r' ⊆ V₀ :=
    (convex_ball z₀ r').isPreconnected.subset_connectedComponentIn (mem_ball_self hr')
      (fun z hz => ⟨hr₁K₁ (hr'O hz).1, (hr'O hz).2⟩)
  have hseed₁ : RelBranchAt c₁ V₀ R₁ S₁ z₀ := by
    refine ⟨r', hr', hr'V₀, g₁, hg₁.mono fun z hz => (hr'O hz).1, fun y hy => ?_,
      ⟨z₀, mem_ball_self hr', hg₁ne z₀ (mem_ball_self hr₁)⟩⟩
    have h1 := hRg y (hr'O hy).1
    simp only [hRdef, hgG (hr'O hy)] at h1
    exact h1
  have hprop₁ := relBranchAt_of_preconnected hV₀o isPreconnected_connectedComponentIn
    (fun z hz => (hV₀sub hz).1) hR₁ hS₁ hseed₁
  -- a nondegenerate Julia point on the frontier of `V₀`
  have hKperf := filledJulia_no_isolated_of_not_mem_mandelbrot hc₁
  have hpK₁ : p ∈ filledJulia c₁ := mem_filledJulia_of_frontier hpfr
  have hS₀ne := frontier_connectedComponentIn_inter_nonempty hK₁ isOpen_ball
    (convex_ball p r₀).isPreconnected ⟨hz₀K₁, hz₀ball⟩ ⟨p, hpK₁, mem_ball_self hr₀⟩
  have hS₀acc := frontier_connectedComponentIn_inter_no_isolated (z := z₀) (D := ball p r₀) hK₁
    isOpen_ball hKperf
  obtain ⟨q, hqS₀, hqgood⟩ := not_subset_iff_exists_mem_notMem.mp
    (not_subset_discrete_of_no_isolated hS₀ne hS₀acc hBdisc)
  have hqball : q ∈ ball p r₀ := hqS₀.2
  have hbq : b q ≠ 0 := fun h0 => hqgood ⟨h0, hqball⟩
  obtain ⟨hleadq, hsepq⟩ := hBgood G₂ q hbq
  -- the root branches on a disc around `q`
  have hbcont : ContinuousAt b q := (hbAn q hqball).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁b⟩ := Metric.eventually_nhds_iff.mp (hbcont.eventually_ne hbq)
  obtain ⟨ρ₃, hρ₃, hρ₃sub⟩ := Metric.isOpen_iff.mp isOpen_ball q hqball
  have haq : ∀ i ∈ s', ContDiffAt ℂ ⊤ (a i) q := fun i _ => (haAn i q hqball).contDiffAt
  obtain ⟨ρ₂, w, hρ₂, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 haq hleadq hsepq
  set ρ : ℝ := min (min ρ₁ ρ₂) ρ₃ with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) hρ₃
  have hΔ₁ : ball q ρ ⊆ ball q ρ₁ :=
    ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))
  have hΔ₂ : ball q ρ ⊆ ball q ρ₂ :=
    ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))
  have hΔ₃ : ball q ρ ⊆ ball p r₀ := (ball_subset_ball (min_le_right _ _)).trans hρ₃sub
  have hΔgood : ∀ z ∈ ball q ρ, (fibrePoly a s' z).Separable := fun z hz =>
    (hBgood G₂ z (hρ₁b (hΔ₁ hz))).2
  have hwAn : ∀ k, ∀ z ∈ ball q ρ, AnalyticAt ℂ (w k) z :=
    analyticAt_branch_of_separable isOpen_ball
      (fun z hz i _ => (haAn i z (hΔ₃ hz)).contDiffAt) hΔgood
      (fun k => (hwc k).mono hΔ₂) (fun k z hz => hwrel k z (hΔ₂ hz))
  -- near a point `z₁ ∈ V₀ ∩ Δ`, the carried branch of `φ_{c₁}` is a root branch
  obtain ⟨z₁, hz₁V₀, hz₁q⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hqS₀.1) ρ hρ
  have hz₁ball : z₁ ∈ ball q ρ := by rw [mem_ball, dist_comm]; exact hz₁q
  have hz₁K₁ : z₁ ∈ (filledJulia c₁)ᶜ := (hV₀sub hz₁V₀).1
  set V := connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball q ρ) z₁ with hVdef
  have hVsub : V ⊆ (filledJulia c₁)ᶜ ∩ ball q ρ := connectedComponentIn_subset _ _
  have hVo : IsOpen V := (hK₁.isOpen_compl.inter isOpen_ball).connectedComponentIn
  obtain ⟨r₂, hr₂, hr₂V₀, g, hg, hRg₁, y₂, hy₂, hgy₂⟩ := hprop₁ z₁ hz₁V₀
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp (isOpen_ball.inter isOpen_ball) z₁
    ⟨mem_ball_self hr₂, hz₁ball⟩
  have hU₁sub : ball z₁ r₃ ⊆ ball z₁ r₂ ∩ ball q ρ := hr₃sub
  obtain ⟨k, hk⟩ := eqOn_branch_of_relation_analytic hN1 w g (convex_ball z₁ r₃).isPreconnected
    (fun k => (hwc k).mono fun z hz => hΔ₂ (hU₁sub hz).2)
    (fun z hz => (hg.1.continuousOn.mono fun y hy => (hU₁sub hy).1) z hz)
    (fun z hz => hwsep z (hΔ₂ (hU₁sub hz).2)) (fun z hz => hwdeg z (hΔ₂ (hU₁sub hz).2))
    (fun k z hz => hwrel k z (hΔ₂ (hU₁sub hz).2))
    (fun z hz => hRg₁ z (hU₁sub hz).1) (mem_ball_self hr₃)
  have hballV : ball z₁ r₃ ⊆ V :=
    (convex_ball z₁ r₃).isPreconnected.subset_connectedComponentIn (mem_ball_self hr₃)
      (fun z hz => ⟨(hV₀sub (hr₂V₀ (hU₁sub hz).1)).1, (hU₁sub hz).2⟩)
  -- the root branch is a branch of `φ_{c₁}` on `V`
  have hwkAn : AnalyticOnNhd ℂ (w k) (ball q ρ) := fun z hz => hwAn k z hz
  have hωAn : AnalyticOnNhd ℂ (greenLogDeriv c₁) (filledJulia c₁)ᶜ :=
    (differentiableOn_greenLogDeriv c₁).analyticOnNhd hK₁.isOpen_compl
  have hwkbranch : IsBasinBranch c₁ V (w k) := by
    refine ⟨fun z hz => (hwAn k z (hVsub hz).2).differentiableAt.differentiableWithinAt,
      fun z hz => ?_⟩
    have han : AnalyticOnNhd ℂ (fun y => deriv (w k) y - greenLogDeriv c₁ y * w k y) V :=
      fun y hy => ((hwkAn.deriv) y (hVsub hy).2).sub
        ((hωAn y (hVsub hy).1).mul (hwkAn y (hVsub hy).2))
    have hev : (fun y => deriv (w k) y - greenLogDeriv c₁ y * w k y) =ᶠ[𝓝 z₁] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr₃)] with y hy
      have hloc : w k =ᶠ[𝓝 y] g := by
        filter_upwards [isOpen_ball.mem_nhds hy] with t ht using (hk ht).symm
      rw [Pi.zero_apply, hloc.deriv_eq, hg.2 y (hU₁sub hy).1, hk hy, sub_self]
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      (mem_connectedComponentIn ⟨hz₁K₁, hz₁ball⟩) hev hz
    exact sub_eq_zero.mp this
  have hgne : ∀ y ∈ ball z₁ r₂, g y ≠ 0 :=
    hg.ne_zero_of_ne_zero isOpen_ball (convex_ball z₁ r₂).isPreconnected
      (fun y hy => (hV₀sub (hr₂V₀ hy)).1) hy₂ hgy₂
  have hwkz₁ : w k z₁ ≠ 0 := by
    rw [← hk (mem_ball_self hr₃)]; exact hgne z₁ (mem_ball_self hr₂)
  have hwkne : ∀ y ∈ V, w k y ≠ 0 :=
    hwkbranch.ne_zero_of_ne_zero hVo isPreconnected_connectedComponentIn
      (fun y hy => (hVsub hy).1) (mem_connectedComponentIn ⟨hz₁K₁, hz₁ball⟩) hwkz₁
  obtain ⟨C, hC, hmod⟩ := hwkbranch.exists_norm_eq_mul_exp hVo isPreconnected_connectedComponentIn
    (fun y hy => (hVsub hy).1) hwkne
  -- a Julia point on the frontier of `V` and a small piece around it
  have hqK₁ : q ∈ filledJulia c₁ := frontier_connectedComponentIn_inter_subset hK₁ isOpen_ball hqS₀
  obtain ⟨q', hq'fr, hq'Δ⟩ := frontier_connectedComponentIn_inter_nonempty hK₁ isOpen_ball
    (convex_ball q ρ).isPreconnected ⟨hz₁K₁, hz₁ball⟩ ⟨q, hqK₁, mem_ball_self hρ⟩
  have hq'K₁ : q' ∈ filledJulia c₁ :=
    frontier_connectedComponentIn_inter_subset hK₁ isOpen_ball ⟨hq'fr, hq'Δ⟩
  obtain ⟨r₄, hr₄, hr₄Δ⟩ := Metric.isOpen_iff.mp isOpen_ball q' hq'Δ
  obtain ⟨E, hEo, hq'E, hEr, hEc, -, -, -⟩ := exists_small_piece hc₁ hq'K₁ hr₄
  -- the piece minus `K_{c₁}` lies in `V`
  obtain ⟨v, hvE, hvV⟩ : (E ∩ V).Nonempty :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hq'fr) E (hEo.mem_nhds hq'E)
  have hEV : E \ filledJulia c₁ ⊆ V := by
    have hsub := hEc.subset_connectedComponentIn
      (show v ∈ E \ filledJulia c₁ from ⟨hvE, (hVsub hvV).1⟩)
      (show E \ filledJulia c₁ ⊆ (filledJulia c₁)ᶜ ∩ ball q ρ from
        fun y hy => ⟨hy.2, hr₄Δ (hEr hy.1)⟩)
    rwa [← connectedComponentIn_eq hvV] at hsub
  -- the Green-modulus minimum principle
  obtain ⟨r₅, hr₅, hr₅E⟩ := Metric.isOpen_iff.mp hEo q' hq'E
  have hint : interior (filledJulia c₁) = ∅ :=
    interior_filledJulia_eq_empty_of_not_mem_mandelbrot hc₁
  have hdense : ball q' r₅ ⊆ closure (ball q' r₅ ∩ (filledJulia c₁)ᶜ) :=
    density_basin_of_empty_interior (by rw [hint, inter_empty])
  have hbasin : ∃ z ∈ ball q' r₅, z ∉ filledJulia c₁ := by
    by_contra hcon
    push Not at hcon
    have hsub : ball q' r₅ ⊆ interior (filledJulia c₁) :=
      interior_maximal (fun z hz => hcon z hz) isOpen_ball
    rw [hint] at hsub
    exact hsub (mem_ball_self hr₅)
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  refine no_green_modulus_continuation_dense (g := fun y => w k y / C) hr₅ ?_ hq'K₁ hdense ?_
    hbasin
  · intro y hy
    exact (hwAn k y (hr₄Δ (hEr (hr₅E hy)))).div_const
  · intro y hy hyK
    have hyV : y ∈ V := hEV ⟨hr₅E hy, hyK⟩
    rw [norm_div, hmod y hyV, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    field_simp

/-- **Nguyen's Question 6.2, both-disconnected case.**  For distinct `c₁, c₂ ∉ M` the Böttcher
coordinates are algebraically independent over `ℂ(z)`: no nonzero `P ∈ ℂ(z)[W][Y]` has
`P(φ_{c₁}, φ_{c₂}) = 0`. -/
theorem noRelation_phiMero_of_disconnected
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) (hne : c₁ ≠ c₂)
    (hc₁ : c₁ ∉ mandelbrot) (hc₂ : c₂ ∉ mandelbrot) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  obtain ⟨x, hx⟩ := exists_point_filledJulia_symmDiff hne
  rcases hx with ⟨hxK, hxoff⟩ | ⟨hxK, hxoff⟩
  · exact noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      (phiMero_transcendental_of_disconnected hUo hUc hUne hUinf hc₂ hU₂)
      (hno_of_disconnected_of_mem_filledJulia_not_mem hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hc₁ hc₂
        hxK hxoff)
  · exact noRelation_symm (noRelation_phiMero_of_no_function_relation hUo hUc hUne hUinf c₂ c₁
      hU₂ hU₁ (phiMero_transcendental_of_disconnected hUo hUc hUne hUinf hc₁ hU₁)
      (hno_of_disconnected_of_mem_filledJulia_not_mem hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁ hc₂ hc₁
        hxK hxoff))

/-- **Nguyen's Question 6.2 for all nonexceptional quadratic parameters.**  For `c₁ ≠ c₂` with
`c₁, c₂ ∉ {0, -2}`, the Böttcher coordinates `φ_{c₁}, φ_{c₂}` of `z² + c₁` and `z² + c₂` are
algebraically independent over `ℂ(z)`. -/
theorem noRelation_phiMero_of_ne
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) (hne : c₁ ≠ c₂)
    (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  by_cases h₁ : c₁ ∈ mandelbrot <;> by_cases h₂ : c₂ ∈ mandelbrot
  · exact noRelation_phiMero_of_mem_mandelbrot hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne
      h₁ hc₁0 hc₁2 h₂ hc₂0 hc₂2
  · exact noRelation_phiMero_of_mem_mandelbrot_of_disconnected hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      h₁ hc₁0 hc₁2 h₂
  · exact noRelation_phiMero_of_disconnected_of_mem_mandelbrot hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
      h₁ h₂ hc₂0 hc₂2
  · exact noRelation_phiMero_of_disconnected hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne h₁ h₂

end Bottcher
