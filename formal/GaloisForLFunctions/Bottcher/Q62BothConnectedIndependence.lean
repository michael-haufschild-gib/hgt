/-
# Nguyen's Question 6.2 for two connected nonexceptional parameters

For `c₁ ≠ c₂` in `M ∖ {0, -2}` the Böttcher coordinates `φ_{c₁}, φ_{c₂}` are algebraically
independent over `ℂ(z)`.

Suppose `∑ᵢ Qᵢ(z, φ_{c₂})·φ_{c₁}ⁱ = 0` near `∞`, with `x ∈ K_{c₁} ∖ K_{c₂}` (after swapping the
parameters if necessary).

* The relation, pushed through the global Böttcher branches, holds on the component `W` of
  `K_{c₁}ᶜ ∩ K_{c₂}ᶜ` containing the far field, and `W` accumulates at a point `p` of `∂K_{c₁}` off
  `K_{c₂}`.
* In a ball around `p` inside the `c₂`-basin, a component `V₀` of `K_{c₁}ᶜ ∩ ball` lying in `W` has
  a frontier without isolated points (a Julia point isolated in that frontier would be an isolated
  point of the connected `K_{c₁}`), so the frontier avoids the discrete locus where the squarefree
  relation degenerates.  At such a point `q` the fibre is separable and its roots are `N` analytic
  branches on a small disc.
* On a component `V` of `K_{c₁}ᶜ ∩ disc` inside `V₀`, `φ_{c₁}` equals one branch `w_k`, which is not
  constant; a frontier point `q'` of `V` where `w_k' ≠ 0` exists by the same perfectness argument.
* At `q'`, the branch `w_k` continues `φ_{c₁}` from the access region `V`, contradicting the natural
  boundary (`false_of_continuation_on_open_approach`).

No capacity theory, no smooth-piece rigidity and no hole-free access is used: holes of
`K_{c₁}ᶜ ∩ K_{c₂}ᶜ` are irrelevant because only one access region is needed.
-/
import GaloisForLFunctions.Bottcher.Q62ApproachNaturalBoundary
import GaloisForLFunctions.Bottcher.RelativeRigidityCountableAvoidance
import GaloisForLFunctions.Bottcher.RelativeRigidityCapstone
import GaloisForLFunctions.Bottcher.ConnectedTranscendenceUnconditional
import GaloisForLFunctions.Bottcher.PairComponentPropagation
import GaloisForLFunctions.Bottcher.CylinderUnivalence
import GaloisForLFunctions.Bottcher.FilledJuliaConnected
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-! ### Frontiers of components of an open set minus a closed set -/

section ComponentFrontier

variable {K D : Set ℂ} {z : ℂ}

/-- Inside `D`, the frontier of a component of `Kᶜ ∩ D` lies in `K`. -/
theorem frontier_connectedComponentIn_inter_subset (hK : IsClosed K) (hD : IsOpen D) :
    frontier (connectedComponentIn (Kᶜ ∩ D) z) ∩ D ⊆ K := by
  rintro y ⟨hyfr, hyD⟩
  by_contra hyK
  have hPo : IsOpen (Kᶜ ∩ D) := hK.isOpen_compl.inter hD
  have hyV : y ∈ connectedComponentIn (Kᶜ ∩ D) z :=
    mem_connectedComponentIn_of_mem_closure_of_isOpen hPo (frontier_subset_closure hyfr) ⟨hyK, hyD⟩
  have hVo : IsOpen (connectedComponentIn (Kᶜ ∩ D) z) := hPo.connectedComponentIn
  rw [hVo.frontier_eq] at hyfr
  exact hyfr.2 hyV

/-- A preconnected `D` meeting `K` sees the frontier of every component of `Kᶜ ∩ D`. -/
theorem frontier_connectedComponentIn_inter_nonempty (hK : IsClosed K) (hD : IsOpen D)
    (hDc : IsPreconnected D) (hz : z ∈ Kᶜ ∩ D) (hKD : (K ∩ D).Nonempty) :
    (frontier (connectedComponentIn (Kᶜ ∩ D) z) ∩ D).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  set V := connectedComponentIn (Kᶜ ∩ D) z
  have hPo : IsOpen (Kᶜ ∩ D) := hK.isOpen_compl.inter hD
  have hVo : IsOpen V := hPo.connectedComponentIn
  have hsub : D ⊆ V := subset_of_isPreconnected_of_inter_frontier_empty_of_inter_nonempty hDc hVo
    ⟨z, hz.2, mem_connectedComponentIn hz⟩ (by rw [inter_comm]; exact hne)
  obtain ⟨y, hyK, hyD⟩ := hKD
  exact (connectedComponentIn_subset _ _ (hsub hyD)).1 hyK

/-- A punctured annulus around `y` is preconnected. -/
theorem isPreconnected_annulus_at (y : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsPreconnected {w : ℂ | r < dist w y ∧ dist w y < R} := by
  have h := (isConnected_annulus hr hrR).isPreconnected.image (fun t => t + y)
    (continuous_add_const y).continuousOn
  convert h using 1
  ext w
  simp only [mem_setOf_eq, mem_image, dist_eq_norm]
  constructor
  · intro hw
    exact ⟨w - y, hw, by ring⟩
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

/-- **The frontier of a component has no isolated points** when `K` has none. -/
theorem frontier_connectedComponentIn_inter_no_isolated (hK : IsClosed K) (hD : IsOpen D)
    (hKperf : ∀ y ∈ K, ∀ ε > 0, ∃ y' ∈ K, y' ≠ y ∧ y' ∈ ball y ε) :
    ∀ y ∈ frontier (connectedComponentIn (Kᶜ ∩ D) z) ∩ D, ∀ ρ : ℝ, 0 < ρ →
      ∃ y' ∈ frontier (connectedComponentIn (Kᶜ ∩ D) z) ∩ D, y' ≠ y ∧ y' ∈ ball y ρ := by
  intro y hy ρ hρ
  set V := connectedComponentIn (Kᶜ ∩ D) z with hVdef
  have hPo : IsOpen (Kᶜ ∩ D) := hK.isOpen_compl.inter hD
  have hVo : IsOpen V := hPo.connectedComponentIn
  have hVK : V ⊆ Kᶜ := fun w hw => (connectedComponentIn_subset _ _ hw).1
  have hyK : y ∈ K := frontier_connectedComponentIn_inter_subset hK hD hy
  by_contra hcon
  push Not at hcon
  obtain ⟨r', hr', hr'D⟩ := Metric.isOpen_iff.mp hD y hy.2
  set R := min ρ r' with hRdef
  have hR : 0 < R := lt_min hρ hr'
  -- a point of `V` close to `y`
  obtain ⟨v, hvV, hvball⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hy.1) R hR
  have hvne : v ≠ y := fun h => hVK hvV (h ▸ hyK)
  have hvpos : 0 < dist v y := dist_pos.mpr hvne
  have hvR : dist v y < R := by rw [dist_comm]; exact hvball
  -- every other point of the small ball lies in `V`
  have hball : ∀ w ∈ ball y R, w ≠ y → w ∈ V := by
    intro w hw hwne
    have hwpos : 0 < dist w y := dist_pos.mpr hwne
    set t := min (dist w y) (dist v y) / 2 with htdef
    have ht : 0 < t := by positivity
    have htw : t < dist w y := by
      have := min_le_left (dist w y) (dist v y); rw [htdef]; linarith
    have htv : t < dist v y := by
      have := min_le_right (dist w y) (dist v y); rw [htdef]; linarith
    have htR : t < R := lt_trans htv hvR
    set A := {w' : ℂ | t < dist w' y ∧ dist w' y < R}
    have hApre : IsPreconnected A := isPreconnected_annulus_at y ht htR
    have hAV : (A ∩ V).Nonempty := ⟨v, ⟨htv, hvR⟩, hvV⟩
    have hAfr : A ∩ frontier V = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro w' ⟨⟨hw't, hw'R⟩, hw'fr⟩
      have hw'D : w' ∈ D := hr'D (lt_of_lt_of_le hw'R (min_le_right _ _))
      have hw'ne : w' ≠ y := by
        intro h; rw [h, dist_self] at hw't; linarith
      have := hcon w' ⟨hw'fr, hw'D⟩ hw'ne
      exact this (lt_of_lt_of_le hw'R (min_le_left _ _))
    exact subset_of_isPreconnected_of_inter_frontier_empty_of_inter_nonempty hApre hVo hAV hAfr
      ⟨htw, hw⟩
  obtain ⟨y', hy'K, hy'ne, hy'ball⟩ := hKperf y hyK R hR
  exact hVK (hball y' hy'ball hy'ne) hy'K

end ComponentFrontier

/-! ### Analytic branches of a separable fibre -/

/-- On an open set where every fibre is separable, the continuous root branches are analytic. -/
theorem analyticAt_branch_of_separable {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    {w : Fin N → ℂ → ℂ} {D : Set ℂ} (hDo : IsOpen D)
    (ha : ∀ z ∈ D, ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z)
    (hsep : ∀ z ∈ D, (fibrePoly a s z).Separable)
    (hwc : ∀ k, ContinuousOn (w k) D)
    (hwrel : ∀ k, ∀ z ∈ D, ∑ i ∈ s, a i z * (w k z) ^ i = 0) :
    ∀ k, ∀ z ∈ D, AnalyticAt ℂ (w k) z := by
  intro k z hz
  have hroot : ∑ i ∈ s, a i z * (w k z) ^ i = 0 := hwrel k z hz
  have hrootQ : (fibrePoly a s z).eval (w k z) = 0 := by rw [eval_fibrePoly]; exact hroot
  have hd : (fibrePoly a s z).derivative.eval (w k z) ≠ 0 :=
    eval_derivative_ne_zero_of_separable (hsep z hz) hrootQ
  have hpart := relation_hasDerivAt_w_analytic a s z (w k z)
  obtain ⟨g, hgAt, hgz, hgrel⟩ := exists_analyticAt_branch_analytic (ha z hz) hroot hpart hd
  have hnhds : 𝓝[D] z = 𝓝 z := nhdsWithin_eq_nhds.mpr (hDo.mem_nhds hz)
  have hwlim : Tendsto (w k) (𝓝[D] z) (𝓝 (w k z)) := (hwc k z hz).tendsto
  have hrelw : ∀ᶠ y in 𝓝[D] z, ∑ i ∈ s, a i y * (w k y) ^ i = 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy using hwrel k y hy
  have heq : ∀ᶠ y in 𝓝[D] z, g y = w k y :=
    branch_unique_within_analytic (fun i hi => (ha z hz i hi).continuousAt) hpart hd
      hgAt.continuousAt hgz hwlim (hgrel.filter_mono nhdsWithin_le_nhds) hrelw
  rw [hnhds] at heq
  exact hgAt.congr heq

/-! ### The connected Böttcher package -/

/-- For connected `c`, the global Böttcher branch with its modulus, its inverse and the even disk
model. -/
theorem exists_connected_bottcher_package (c : ℂ) (hcM : c ∈ mandelbrot) :
    ∃ (h β ψ : ℂ → ℂ),
      DifferentiableOn ℂ h (ball 0 1) ∧
      (∀ t ∈ ball (0:ℂ) 1, h (-t) = h t) ∧
      (∀ t ∈ ball (0:ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ)) ∧
      h 0 = 1 ∧
      (∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t)) ∧
      AnalyticOnNhd ℂ β (filledJulia c)ᶜ ∧
      (∀ z ∈ escapeOpen c, β z = bottcherCoord c z) ∧
      (∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) ∧
      AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖} ∧
      (∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z) ∧
      (∀ w : ℂ, 1 < ‖w‖ → ψ w ∈ (filledJulia c)ᶜ) ∧
      (∀ w : ℂ, 1 < ‖w‖ → β (ψ w) = w) := by
  obtain ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc, hψan, hψmem, hβψ, hψβ⟩ :=
    exists_full_disk_model_of_mem_mandelbrot c hcM
  obtain ⟨β₁, _ψ₁, hβ₁an, hβ₁esc, hβ₁mod, -⟩ :=
    exists_global_branch_with_inverse_of_mem_mandelbrot c hcM
  obtain ⟨zstar, hzstar⟩ : (escapeOpen c).Nonempty := ⟨_, deepPoint_mem_escapeOpen c⟩
  have hzstarbasin : zstar ∈ (filledJulia c)ᶜ := escapeOpen_subset_compl_filledJulia c hzstar
  have hev : β =ᶠ[𝓝 zstar] β₁ := by
    filter_upwards [(isOpen_escapeOpen c).mem_nhds hzstar] with z hz
    rw [hβesc z hz, hβ₁esc z hz]
  have hββ₁ : Set.EqOn β β₁ (filledJulia c)ᶜ :=
    hβan.eqOn_of_preconnected_of_eventuallyEq hβ₁an (isPreconnected_compl_filledJulia c)
      hzstarbasin hev
  exact ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc,
    fun z hz => by rw [hββ₁ hz]; exact hβ₁mod z hz, hψan, hψβ, hψmem, hβψ⟩

/-! ### The both-connected pair -/

variable {U : Set ℂ}

/-- Points of a filled Julia set are not isolated, in metric form. -/
theorem filledJulia_no_isolated {c : ℂ} (hcM : c ∈ mandelbrot) :
    ∀ y ∈ filledJulia c, ∀ ε > 0, ∃ y' ∈ filledJulia c, y' ≠ y ∧ y' ∈ ball y ε := by
  intro y hy ε hε
  have hperf := perfect_filledJulia_of_preconnected_nontrivial (isPreconnected_filledJulia hcM)
    (filledJulia_nontrivial c)
  obtain ⟨y', ⟨hy'ball, hy'K⟩, hy'ne⟩ :=
    accPt_iff_nhds.mp (hperf.acc y hy) (ball y ε) (ball_mem_nhds y hε)
  exact ⟨y', hy'K, hy'ne, hy'ball⟩

/-- The far-field component of the common basin is unbounded. -/
theorem not_isBounded_commonComponent {c₁ c₂ u : ℂ}
    (hu : u ∈ escapeOpen c₁ ∩ escapeOpen c₂) :
    ¬ Bornology.IsBounded
      (connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u) := by
  set E := escapeOpen c₁ ∩ escapeOpen c₂
  have hED : E ⊆ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ := fun z hz =>
    ⟨escapeOpen_subset_compl_filledJulia c₁ hz.1, escapeOpen_subset_compl_filledJulia c₂ hz.2⟩
  have hEW : E ⊆ connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u :=
    (isConnected_escapeOpen_inter c₁ c₂).isPreconnected.subset_connectedComponentIn hu hED
  intro hbdd
  rw [isBounded_iff_forall_norm_le] at hbdd
  obtain ⟨R, hR⟩ := hbdd
  set M : ℝ := max (max 2 ‖c₁‖) (max 2 ‖c₂‖) with hMdef
  have hM2 : (2 : ℝ) ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  set t : ℂ := ((M + |R| + 1 : ℝ) : ℂ) with htdef
  have htnorm : ‖t‖ = M + |R| + 1 := by
    rw [htdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have htE : t ∈ E := by
    refine ⟨?_, ?_⟩
    · show max 2 ‖c₁‖ < ‖t‖
      rw [htnorm]
      have := le_max_left (max 2 ‖c₁‖) (max 2 ‖c₂‖)
      linarith [abs_nonneg R]
    · show max 2 ‖c₂‖ < ‖t‖
      rw [htnorm]
      have := le_max_right (max 2 ‖c₁‖) (max 2 ‖c₂‖)
      linarith [abs_nonneg R]
  have := hR t (hEW htE)
  rw [htnorm] at this
  linarith [le_abs_self R]

/-- **The local natural-boundary step.**  Let `c ∈ M ∖ {0,-2}` with its connected Böttcher package,
`p ∈ K_c`, and `a` a coefficient family analytic on `ball p r₀` whose top coefficient is nonzero and
whose fibre is separable off the discrete zero set of an analytic `b`.  Then the Böttcher branch `β`
does not satisfy `∑ aᵢ βⁱ = 0` on a component `V₀` of `K_cᶜ ∩ ball p r₀`.

The frontier of `V₀` has no isolated points, so it contains a good point `q`; near `q` the roots of
the relation are `N` analytic branches, `β` is one of them on a component `V` of `K_cᶜ ∩ disc`, and
at a frontier point of `V` where that branch has nonzero derivative it continues `β` from the access
region `V`, against the natural boundary. -/
theorem false_of_relation_on_ball_component {c p z₀ : ℂ} {r₀ : ℝ} {β ψ h : ℂ → ℂ}
    {a : ℕ → ℂ → ℂ} {b : ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hcM : c ∈ mandelbrot) (hc0 : c ≠ 0) (hc2 : c ≠ -2)
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hhe : ∀ t ∈ ball (0:ℂ) 1, h (-t) = h t)
    (hfe : ∀ t ∈ ball (0:ℂ) 1, h (t ^ (2 : ℕ)) = (h t) ^ (2 : ℕ) + c * t ^ (2 : ℕ))
    (hh0 : h 0 = 1)
    (hbridge : ∀ t : ℂ, t ≠ 0 → ‖t‖ < 1 → h t = t * ψ (1 / t))
    (hβan : AnalyticOnNhd ℂ β (filledJulia c)ᶜ)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hψan : AnalyticOnNhd ℂ ψ {w : ℂ | 1 < ‖w‖})
    (hψβ : ∀ z ∈ (filledJulia c)ᶜ, ψ (β z) = z)
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (haAn : ∀ i, AnalyticOnNhd ℂ (a i) (ball p r₀))
    (hbAn : AnalyticOnNhd ℂ b (ball p r₀))
    (hBdisc : IsDiscrete ({z | b z = 0} ∩ ball p r₀))
    (hBgood : ∀ w ∈ ball p r₀, b w ≠ 0 → a N w ≠ 0 ∧ (fibrePoly a s w).Separable)
    (hpK : p ∈ filledJulia c) (hz₀ : z₀ ∈ (filledJulia c)ᶜ ∩ ball p r₀)
    (hrel : ∀ z ∈ connectedComponentIn ((filledJulia c)ᶜ ∩ ball p r₀) z₀,
      ∑ i ∈ s, a i z * (β z) ^ i = 0) :
    False := by
  have hr₀ : 0 < r₀ := pos_of_mem_ball hz₀.2
  have hK : IsClosed (filledJulia c) := isClosed_filledJulia c
  have hKperf := filledJulia_no_isolated hcM
  set V₀ := connectedComponentIn ((filledJulia c)ᶜ ∩ ball p r₀) z₀ with hV₀def
  -- a nondegenerate Julia point on the frontier of `V₀`
  have hS₀ne := frontier_connectedComponentIn_inter_nonempty hK isOpen_ball
    (convex_ball p r₀).isPreconnected hz₀ ⟨p, hpK, mem_ball_self hr₀⟩
  have hS₀acc := frontier_connectedComponentIn_inter_no_isolated (z := z₀) (D := ball p r₀) hK
    isOpen_ball hKperf
  obtain ⟨q, hqS₀, hqgood⟩ := not_subset_iff_exists_mem_notMem.mp
    (not_subset_discrete_of_no_isolated hS₀ne hS₀acc hBdisc)
  have hqball : q ∈ ball p r₀ := hqS₀.2
  have hbq : b q ≠ 0 := fun h0 => hqgood ⟨h0, hqball⟩
  obtain ⟨hleadq, hsepq⟩ := hBgood q hqball hbq
  -- a disc of good points around `q`
  have hbcont : ContinuousAt b q := (hbAn q hqball).continuousAt
  obtain ⟨r₁, hr₁, hr₁b⟩ := Metric.eventually_nhds_iff.mp (hbcont.eventually_ne hbq)
  obtain ⟨r₃, hr₃, hr₃sub⟩ := Metric.isOpen_iff.mp isOpen_ball q hqball
  have haq : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) q := fun i _ => (haAn i q hqball).contDiffAt
  obtain ⟨r₂, w, hr₂, hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 haq hleadq hsepq
  set ρ : ℝ := min (min r₁ r₂) r₃ with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hr₁ hr₂) hr₃
  have hΔ₁ : ball q ρ ⊆ ball q r₁ := ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))
  have hΔ₂ : ball q ρ ⊆ ball q r₂ :=
    ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))
  have hΔ₃ : ball q ρ ⊆ ball p r₀ := (ball_subset_ball (min_le_right _ _)).trans hr₃sub
  have hΔgood : ∀ z ∈ ball q ρ, (fibrePoly a s z).Separable := fun z hz =>
    (hBgood z (hΔ₃ hz) (hr₁b (hΔ₁ hz))).2
  have hwAn : ∀ k, ∀ z ∈ ball q ρ, AnalyticAt ℂ (w k) z :=
    analyticAt_branch_of_separable isOpen_ball
      (fun z hz i _ => (haAn i z (hΔ₃ hz)).contDiffAt) hΔgood
      (fun k => (hwc k).mono hΔ₂) (fun k z hz => hwrel k z (hΔ₂ hz))
  -- `β` is one branch on a component of `K_cᶜ ∩ disc` inside `V₀`
  obtain ⟨z₁, hz₁V₀, hz₁q⟩ := Metric.mem_closure_iff.mp (frontier_subset_closure hqS₀.1) ρ hρ
  have hz₁ball : z₁ ∈ ball q ρ := by rw [mem_ball, dist_comm]; exact hz₁q
  have hz₁K : z₁ ∈ (filledJulia c)ᶜ := (connectedComponentIn_subset _ _ hz₁V₀).1
  set V := connectedComponentIn ((filledJulia c)ᶜ ∩ ball q ρ) z₁ with hVdef
  have hVsub : V ⊆ (filledJulia c)ᶜ ∩ ball q ρ := connectedComponentIn_subset _ _
  have hVV₀ : V ⊆ V₀ := by
    have hsub : V ⊆ connectedComponentIn ((filledJulia c)ᶜ ∩ ball p r₀) z₁ :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn ⟨hz₁K, hz₁ball⟩)
        (fun z hz => ⟨(hVsub hz).1, hΔ₃ (hVsub hz).2⟩)
    rwa [← connectedComponentIn_eq hz₁V₀] at hsub
  have hVo : IsOpen V := (hK.isOpen_compl.inter isOpen_ball).connectedComponentIn
  obtain ⟨k, hk⟩ := eqOn_branch_of_relation_analytic hN1 w β isPreconnected_connectedComponentIn
    (fun k => (hwc k).mono fun z hz => hΔ₂ (hVsub hz).2)
    (fun z hz => (hβan z (hVsub hz).1).continuousAt.continuousWithinAt)
    (fun z hz => hwsep z (hΔ₂ (hVsub hz).2)) (fun z hz => hwdeg z (hΔ₂ (hVsub hz).2))
    (fun k z hz => hwrel k z (hΔ₂ (hVsub hz).2))
    (fun z hz => hrel z (hVV₀ hz)) (mem_connectedComponentIn ⟨hz₁K, hz₁ball⟩)
  -- the branch is not constant: `β` is injective
  have hβinj : ∀ z ∈ (filledJulia c)ᶜ, ∀ z' ∈ (filledJulia c)ᶜ, β z = β z' → z = z' :=
    fun z hz z' hz' hzz => by rw [← hψβ z hz, ← hψβ z' hz', hzz]
  have hwAnΔ : AnalyticOnNhd ℂ (w k) (ball q ρ) := fun z hz => hwAn k z hz
  obtain ⟨z₂, hz₂V, hz₂d⟩ : ∃ z₂ ∈ V, deriv (w k) z₂ ≠ 0 := by
    by_contra hall
    push Not at hall
    have hz₁V : z₁ ∈ V := mem_connectedComponentIn ⟨hz₁K, hz₁ball⟩
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hVo z₁ hz₁V
    have hconst : ∀ y ∈ ball z₁ ε, w k y = w k z₁ := fun y hy =>
      (isOpen_ball).is_const_of_deriv_eq_zero (convex_ball z₁ ε).isPreconnected
        (fun t ht => (hwAn k t (hVsub (hεV ht)).2).differentiableAt.differentiableWithinAt)
        (fun t ht => hall t (hεV ht)) hy (mem_ball_self hε)
    set y := z₁ + (ε / 2 : ℝ)
    have hy : y ∈ ball z₁ ε := by
      rw [mem_ball, dist_eq_norm, show y - z₁ = ((ε / 2 : ℝ) : ℂ) by simp [y],
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hyne : y ≠ z₁ := by
      intro hyz
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by rw [← sub_eq_zero.mpr hyz]; simp [y]
      have : ε / 2 = 0 := by exact_mod_cast this
      linarith
    apply hyne
    refine hβinj y (hVsub (hεV hy)).1 z₁ hz₁K ?_
    rw [hk (hεV hy), hk hz₁V, hconst y hy]
  have hdAn : AnalyticOnNhd ℂ (deriv (w k)) (ball q ρ) := hwAnΔ.deriv
  have hΔc : IsConnected (ball q ρ) := ⟨⟨q, mem_ball_self hρ⟩, (convex_ball q ρ).isPreconnected⟩
  have hDdisc : IsDiscrete ({z | deriv (w k) z = 0} ∩ ball q ρ) := by
    have hcod := hdAn.preimage_zero_mem_codiscreteWithin hz₂d (hVsub hz₂V).2 hΔc
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | deriv (w k) z = 0} : Set ℂ)ᶜ = deriv (w k) ⁻¹' {0}ᶜ := by ext z; simp
    rw [hset]; exact hcod
  -- a Julia point on the frontier of `V` where the branch is a local biholomorphism
  have hqK : q ∈ filledJulia c := frontier_connectedComponentIn_inter_subset hK isOpen_ball hqS₀
  have hSne := frontier_connectedComponentIn_inter_nonempty hK isOpen_ball
    (convex_ball q ρ).isPreconnected ⟨hz₁K, hz₁ball⟩ ⟨q, hqK, mem_ball_self hρ⟩
  have hSacc := frontier_connectedComponentIn_inter_no_isolated (z := z₁) (D := ball q ρ) hK
    isOpen_ball hKperf
  obtain ⟨q', hq'S, hq'good⟩ := not_subset_iff_exists_mem_notMem.mp
    (not_subset_discrete_of_no_isolated hSne hSacc hDdisc)
  have hq'Δ : q' ∈ ball q ρ := hq'S.2
  have hq'd : deriv (w k) q' ≠ 0 := fun h0 => hq'good ⟨h0, hq'Δ⟩
  have hq'K : q' ∈ filledJulia c := frontier_connectedComponentIn_inter_subset hK isOpen_ball hq'S
  have hq'cl : q' ∈ closure V := frontier_subset_closure hq'S.1
  have hq'fr : q' ∈ frontier (filledJulia c) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hq'K, closure_mono (fun z hz => (hVsub hz).1) hq'cl⟩
  exact false_of_continuation_on_open_approach hc0 hc2 hq'fr (hwAn k q' hq'Δ) hq'd hVo
    (fun z hz => (hVsub hz).1) hq'cl (fun z hz => (hk hz).symm) hβmod hψan hψβ hhd hhe hfe hh0
    hbridge

/-- **No bivariate relation for two connected nonexceptional parameters**, in the orientation where
some point of `K_{c₁}` lies off `K_{c₂}`. -/
theorem hno_of_connected_of_mem_filledJulia_not_mem
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2)
    {x : ℂ} (hxK : x ∈ filledJulia c₁) (hxoff : x ∉ filledJulia c₂) :
    ∀ (Q : ℕ → Polynomial (Polynomial ℂ)) (s : Finset ℕ),
      (∃ i ∈ s, (Q i).eval₂ (polyToAnalytic U) (phiAnalytic c₂ hU₂) ≠ 0) →
      ¬ Set.EqOn (fun z => ∑ i ∈ s,
          ((Q i).eval₂ (Polynomial.evalRingHom z) (bottcherCoord c₂ z))
            * (bottcherCoord c₁ z) ^ i) 0 U := by
  intro Q s hnt hEqOn
  have hG := phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf hc₂M hc₂0 hc₂2 hU₂
  -- the two global branches
  obtain ⟨h, β, ψ, hhd, hhe, hfe, hh0, hbridge, hβan, hβesc, hβmod, hψan, hψβ, -, -⟩ :=
    exists_connected_bottcher_package c₁ hc₁M
  obtain ⟨γ, -, hγan, hγesc, -⟩ := exists_global_branch_with_inverse_of_mem_mandelbrot c₂ hc₂M
  have hγmatch : ∀ z ∈ U, γ z = bottcherCoord c₂ z := fun z hz => hγesc z (hU₂ hz)
  -- the squarefree relation and its degeneracy locus
  obtain ⟨Q', s', N, B, _hnt', hEqOn', hsupp, hN, hN1, hB0, hBgood⟩ :=
    primitiveSqfreeBad_of_sparse_relation hUo hUc hUne hUinf c₁ c₂ hU₂ hG γ Q s hnt hEqOn
  set a : ℕ → ℂ → ℂ := fun i z => (Q' i).eval₂ (Polynomial.evalRingHom z) (γ z) with hadef
  set b : ℂ → ℂ := fun z => B.eval₂ (Polynomial.evalRingHom z) (γ z) with hbdef
  have haAn : ∀ i, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ := fun i =>
    analyticOnNhd_eval₂_of_analyticOnNhd hγan (Q' i)
  have hbAn : AnalyticOnNhd ℂ b (filledJulia c₂)ᶜ := analyticOnNhd_eval₂_of_analyticOnNhd hγan B
  obtain ⟨wstar, -, hwoff, hbw⟩ :=
    exists_mem_compl_filledJulia_gamma_ne_zero_of_bivariate_ne_zero_transcendental
      hUo hUc hUne hUinf c₂ hU₂ hG γ hγmatch hB0
  have hK₂c : IsConnected (filledJulia c₂)ᶜ := ⟨⟨wstar, hwoff⟩, isPreconnected_compl_filledJulia c₂⟩
  have hBdisc : IsDiscrete ({z | b z = 0} ∩ (filledJulia c₂)ᶜ) := by
    have hcod := hbAn.preimage_zero_mem_codiscreteWithin hbw hwoff hK₂c
    apply isDiscrete_of_codiscreteWithin
    have hset : ({z | b z = 0} : Set ℂ)ᶜ = b ⁻¹' {0}ᶜ := by ext z; simp
    rw [hset]; exact hcod
  -- the relation on the far-field component of the common basin
  obtain ⟨u, huU⟩ := hUne
  have huE : u ∈ escapeOpen c₁ ∩ escapeOpen c₂ := ⟨hU₁ huU, hU₂ huU⟩
  have hu : u ∈ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ :=
    ⟨escapeOpen_subset_compl_filledJulia c₁ huE.1, escapeOpen_subset_compl_filledJulia c₂ huE.2⟩
  set W := connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) u with hWdef
  have hWsub : W ⊆ (filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ := connectedComponentIn_subset _ _
  have hrelW : ∀ q ∈ W, ∑ i ∈ s', a i q * (β q) ^ i = 0 := by
    intro q hq
    exact pair_relation_at_escape_point hβan hβesc hγan hγesc hUo ⟨u, huU⟩ hU₁ hU₂ Q' s' hEqOn'
      (V := W) hq isPreconnected_connectedComponentIn (not_isBounded_commonComponent huE)
      (fun z hz => by rw [compl_union]; exact hWsub hz)
  -- a Julia point of `c₁` in the closure of `W`, off `K_{c₂}`
  obtain ⟨p, hpfr, hpoff, hpcl⟩ :=
    exists_frontier_off_other_in_closure_common_component hu hxK hxoff
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp (isClosed_filledJulia c₂).isOpen_compl p hpoff
  obtain ⟨z₀, hz₀W, hz₀p⟩ := Metric.mem_closure_iff.mp hpcl r₀ hr₀
  have hz₀ball : z₀ ∈ ball p r₀ := by rw [mem_ball, dist_comm]; exact hz₀p
  have hz₀K₁ : z₀ ∈ (filledJulia c₁)ᶜ := (hWsub hz₀W).1
  have hV₀W : connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀ ⊆ W := by
    have hsub : connectedComponentIn ((filledJulia c₁)ᶜ ∩ ball p r₀) z₀ ⊆
        connectedComponentIn ((filledJulia c₁)ᶜ ∩ (filledJulia c₂)ᶜ) z₀ :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn ⟨hz₀K₁, hz₀ball⟩)
        (fun z hz => ⟨(connectedComponentIn_subset _ _ hz).1,
          hr₀sub (connectedComponentIn_subset _ _ hz).2⟩)
    rwa [← connectedComponentIn_eq hz₀W] at hsub
  exact false_of_relation_on_ball_component hc₁M hc₁0 hc₁2 hhd hhe hfe hh0 hbridge hβan hβmod
    hψan hψβ hsupp hN hN1 (fun i => (haAn i).mono hr₀sub) (hbAn.mono hr₀sub)
    (hBdisc.mono (inter_subset_inter_right _ hr₀sub)) (fun w _ hbw => hBgood w hbw)
    (mem_filledJulia_of_frontier hpfr) ⟨hz₀K₁, hz₀ball⟩ (fun z hz => hrelW z (hV₀W hz))

/-- **Nguyen's Question 6.2, both-connected case.**  For distinct `c₁, c₂ ∈ M ∖ {0,-2}` the Böttcher
coordinates are algebraically independent over `ℂ(z)`: no nonzero `P ∈ ℂ(z)[W][Y]` has
`P(φ_{c₁}, φ_{c₂}) = 0`.  The two orientations of the crossing point are exchanged by the symmetry
of the no-relation predicate. -/
theorem noRelation_phiMero_of_mem_mandelbrot
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (c₁ c₂ : ℂ) (hU₁ : U ⊆ escapeOpen c₁) (hU₂ : U ⊆ escapeOpen c₂) (hne : c₁ ≠ c₂)
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hc₂M : c₂ ∈ mandelbrot) (hc₂0 : c₂ ≠ 0) (hc₂2 : c₂ ≠ -2) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (phiMero c₁ hU₁) (phiMero c₂ hU₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  have hx₁ : c₁ ∉ Exceptional := by simp [Exceptional, hc₁0, hc₁2]
  have hx₂ : c₂ ∉ Exceptional := by simp [Exceptional, hc₂0, hc₂2]
  obtain ⟨x, hx⟩ := exists_point_filledJulia_symmDiff hne
  rcases hx with ⟨hxK, hxoff⟩ | ⟨hxK, hxoff⟩
  · exact q62_independence_connected_of_dynamical hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂ hne hx₁ hx₂
      (phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf hc₂M hc₂0 hc₂2 hU₂)
      (hno_of_connected_of_mem_filledJulia_not_mem hUo hUc hUne hUinf c₁ c₂ hU₁ hU₂
        hc₁M hc₁0 hc₁2 hc₂M hc₂0 hc₂2 hxK hxoff)
  · exact noRelation_symm (q62_independence_connected_of_dynamical hUo hUc hUne hUinf c₂ c₁
      hU₂ hU₁ hne.symm hx₂ hx₁
      (phiMero_transcendental_of_mem_mandelbrot hUo hUc hUne hUinf hc₁M hc₁0 hc₁2 hU₁)
      (hno_of_connected_of_mem_filledJulia_not_mem hUo hUc hUne hUinf c₂ c₁ hU₂ hU₁
        hc₂M hc₂0 hc₂2 hc₁M hc₁0 hc₁2 hxK hxoff))

end Bottcher
