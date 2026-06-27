/-
# Analytic-coefficient branch family and the relative dendrite obstruction

The absolute connected-case dendrite argument (`ConnectedTranscendence`, `GlobalBasinBranch`) builds the
analytic root-branches of the fibre polynomial `P.map(eval z)` of a *polynomial*-coefficient relation,
follows the basin Böttcher branch along one of them to a simple-root boundary value, and closes the case
with the Green-modulus natural boundary. For the **relative** rigidity input the relation coefficients are
`aᵢ(z) = (Qᵢ)(z, φ_{c₂}(z))` — analytic functions, not polynomials in `z` — so the fibre is the analytic
`fibrePoly a s z = ∑_{i∈s} (aᵢ z)·Xⁱ`.

This file mirrors the entire branch-family machinery for that analytic fibre, reusing the already-general
analytic implicit-function theorem `exists_analyticAt_branch_analytic` and the coefficient-agnostic
helpers (`eval_derivative_ne_zero_of_separable`, `root_eq_of_card_branches`,
`eq_one_branch_of_valued_in_separated`, `tendsto_within_of_eqOn`, `eventually_separated`). It culminates in
`false_of_global_basin_branch_analytic`: the relative connected dendrite sub-case is impossible, reduced to
purely geometric inputs (a dendrite tip `z₀` with preconnected punctured basin sectors) plus a basin
Böttcher branch `β` carrying the relation and the genuine modulus on the basin sector and the generic
fibre nondegeneracy at `z₀` (full degree + separable). Unlike the absolute case, the relation and modulus
are taken on the basin sector directly (not spread from the far field), since the relative coefficients are
analytic only near `z₀`, where `φ_{c₂}` continues — not on the whole basin of `c₁`.
-/
import GaloisForLFunctions.Bottcher.RelativeNaturalBoundary
import GaloisForLFunctions.Bottcher.ConnectedTranscendence
import GaloisForLFunctions.Bottcher.BranchContinuation
import GaloisForLFunctions.Bottcher.CoverConstruction

open Polynomial Filter Topology Set Metric

namespace Bottcher

/-- The fibre polynomial `∑_{i∈s} aᵢ(z)·X^i ∈ ℂ[X]` of an analytic-coefficient relation at `z`. -/
noncomputable def fibrePoly (a : ℕ → ℂ → ℂ) (s : Finset ℕ) (z : ℂ) : Polynomial ℂ :=
  ∑ i ∈ s, Polynomial.C (a i z) * Polynomial.X ^ i

/-- Evaluating the fibre polynomial recovers the relation value `∑ aᵢ(z)·wⁱ`. -/
theorem eval_fibrePoly (a : ℕ → ℂ → ℂ) (s : Finset ℕ) (z w : ℂ) :
    (fibrePoly a s z).eval w = ∑ i ∈ s, a i z * w ^ i := by
  rw [fibrePoly, Polynomial.eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The `j`-th coefficient of the fibre polynomial. -/
theorem coeff_fibrePoly (a : ℕ → ℂ → ℂ) (s : Finset ℕ) (z : ℂ) (j : ℕ) :
    (fibrePoly a s z).coeff j = if j ∈ s then a j z else 0 := by
  rw [fibrePoly, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq s j (fun i => a i z)]

/-- With support inside `range (N+1)`, the fibre polynomial has degree at most `N`. -/
theorem natDegree_fibrePoly_le {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (z : ℂ) :
    (fibrePoly a s z).natDegree ≤ N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_fibrePoly, if_neg]
  intro hjs
  have := hsupp hjs
  rw [Finset.mem_range] at this
  omega

/-- Where the leading coefficient `aN(z)` does not vanish, the fibre has full degree `N`. -/
theorem natDegree_fibrePoly_eq {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) {z : ℂ} (hlead : a N z ≠ 0) :
    (fibrePoly a s z).natDegree = N := by
  apply le_antisymm (natDegree_fibrePoly_le hsupp z)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [coeff_fibrePoly, if_pos hN]; exact hlead

/-- The relation's `w`-derivative is the fibre polynomial's formal derivative (analytic-coeff form). -/
theorem relation_hasDerivAt_w_analytic (a : ℕ → ℂ → ℂ) (s : Finset ℕ) (z₀ w₀ : ℂ) :
    HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i)
      ((fibrePoly a s z₀).derivative.eval w₀) w₀ := by
  have hfun : (fun w => ∑ i ∈ s, a i z₀ * w ^ i) = (fun w => (fibrePoly a s z₀).eval w) := by
    funext w; rw [eval_fibrePoly]
  rw [hfun]
  exact (fibrePoly a s z₀).hasDerivAt w₀

/-- **Analytic branch family of a separable fibre (analytic coefficients).** Mirror of
`exists_branch_family` with `(P.coeff i).aeval z` replaced by an analytic family `a i z`: on a small ball
the `N` distinct roots of the separable fibre extend to `N` pairwise-separated continuous branches, each
satisfying the relation, the fibre degree constant `= N`. Built from `exists_analyticAt_branch_analytic`
(the general analytic implicit-function theorem). -/
theorem exists_branch_family_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {z₀ : ℂ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable) :
    ∃ (r : ℝ) (w : Fin N → ℂ → ℂ), 0 < r ∧
      (∀ k, ContinuousOn (w k) (Metric.ball z₀ r)) ∧
      (∀ z ∈ Metric.ball z₀ r, ∀ k l, k ≠ l → w k z ≠ w l z) ∧
      (∀ z ∈ Metric.ball z₀ r, (fibrePoly a s z).natDegree = N) ∧
      (∀ k, ∀ z ∈ Metric.ball z₀ r, ∑ i ∈ s, a i z * (w k z) ^ i = 0) := by
  classical
  set Q₀ := fibrePoly a s z₀ with hQ₀def
  have hQ0deg : Q₀.natDegree = N := natDegree_fibrePoly_eq hsupp hN hlead
  have hQ0 : Q₀ ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hQ0deg; omega
  have hnd : Q₀.roots.Nodup := Polynomial.nodup_roots hsep
  have hcard : Fintype.card ↥(Q₀.roots.toFinset) = N := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hnd,
      IsAlgClosed.card_roots_eq_natDegree, hQ0deg]
  set e : ↥(Q₀.roots.toFinset) ≃ Fin N := Fintype.equivFinOfCardEq hcard with hedef
  set root : Fin N → ℂ := fun k => (e.symm k).val with hrootdef
  have hex : ∀ k : Fin N, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = root k ∧
      ∀ᶠ z in 𝓝 z₀, ∑ i ∈ s, a i z * (g z) ^ i = 0 := by
    intro k
    have hrk_mem : root k ∈ Q₀.roots := Multiset.mem_toFinset.mp (e.symm k).2
    have hrk_root : Q₀.eval (root k) = 0 := (Polynomial.mem_roots hQ0).mp hrk_mem
    have hroot' : ∑ i ∈ s, a i z₀ * (root k) ^ i = 0 := by
      rw [← eval_fibrePoly]; exact hrk_root
    have hpart : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i)
        (Q₀.derivative.eval (root k)) (root k) := relation_hasDerivAt_w_analytic a s z₀ (root k)
    have hd : Q₀.derivative.eval (root k) ≠ 0 := eval_derivative_ne_zero_of_separable hsep hrk_root
    exact exists_analyticAt_branch_analytic ha hroot' hpart hd
  choose g hg_an hg_val hg_rel using hex
  have hcont : ∀ k, ContinuousAt (g k) z₀ := fun k => (hg_an k).continuousAt
  have hdist : ∀ k l, k ≠ l → g k z₀ ≠ g l z₀ := by
    intro k l hkl
    rw [hg_val k, hg_val l]
    intro h
    exact hkl (e.symm.injective (Subtype.ext h))
  have hsep_ev : ∀ᶠ z in 𝓝 z₀, ∀ k l, k ≠ l → g k z ≠ g l z := eventually_separated g hcont hdist
  have hrel_ev : ∀ᶠ z in 𝓝 z₀, ∀ k, ∑ i ∈ s, a i z * (g k z) ^ i = 0 :=
    eventually_all.mpr hg_rel
  have han_ev : ∀ᶠ z in 𝓝 z₀, ∀ k, AnalyticAt ℂ (g k) z :=
    eventually_all.mpr (fun k => (hg_an k).eventually_analyticAt)
  have hdeg_ev : ∀ᶠ z in 𝓝 z₀, (fibrePoly a s z).natDegree = N := by
    have hc : ContinuousAt (a N) z₀ := (ha N hN).continuousAt
    filter_upwards [hc.eventually_ne hlead] with z hz
    exact natDegree_fibrePoly_eq hsupp hN hz
  have hall := hsep_ev.and (hrel_ev.and (han_ev.and hdeg_ev))
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨r, hr, hball⟩ := hall
  refine ⟨r, g, hr, ?_, ?_, ?_, ?_⟩
  · intro k
    have han : AnalyticOnNhd ℂ (g k) (Metric.ball z₀ r) := fun z hz =>
      (hball (Metric.mem_ball.mp hz)).2.2.1 k
    exact han.continuousOn
  · intro z hz; exact (hball (Metric.mem_ball.mp hz)).1
  · intro z hz; exact (hball (Metric.mem_ball.mp hz)).2.2.2
  · intro k z hz; exact (hball (Metric.mem_ball.mp hz)).2.1 k

/-- **β follows one analytic branch (analytic coefficients).** Mirror of `eqOn_branch_of_relation`: on a
preconnected set where the fibre has constant degree `d` with `d` separated continuous root branches, a
continuous `β` satisfying the relation coincides with a single branch `w k`. -/
theorem eqOn_branch_of_relation_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {U : Set ℂ} {d : ℕ}
    (hd1 : 1 ≤ d) (w : Fin d → ℂ → ℂ) (β : ℂ → ℂ) (hUc : IsPreconnected U)
    (hwc : ∀ k, ContinuousOn (w k) U) (hβc : ContinuousOn β U)
    (hsep : ∀ z ∈ U, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hdeg : ∀ z ∈ U, (fibrePoly a s z).natDegree = d)
    (hwroot : ∀ k, ∀ z ∈ U, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    (hβrel : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ k, Set.EqOn β (w k) U := by
  have hval : ∀ z ∈ U, ∃ k, β z = w k z := by
    intro z hz
    have hinj : Function.Injective (fun k => w k z) := by
      intro k l hkl; by_contra h; exact hsep z hz k l h hkl
    have hroots : ∀ k, (fibrePoly a s z).eval (w k z) = 0 := fun k => by
      rw [eval_fibrePoly]; exact hwroot k z hz
    have hβroot : (fibrePoly a s z).eval (β z) = 0 := by
      rw [eval_fibrePoly]; exact hβrel z hz
    obtain ⟨k, hk⟩ := root_eq_of_card_branches hd1 (hdeg z hz) (fun k => w k z) hinj hroots hβroot
    exact ⟨k, hk⟩
  exact eq_one_branch_of_valued_in_separated hUc w β hwc hβc hsep hval hz₀

/-- **Dendrite-route boundary limit (analytic coefficients).** Mirror of `dendrite_branch_limit`: `β`
follows a single branch on the preconnected basin sector `U`, so it has the boundary limit `w₀ = w k z₀`
along the basin, a *simple* root of the relation. -/
theorem dendrite_branch_limit_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {z₀ : ℂ} {r : ℝ} {c : ℂ}
    {N : ℕ} (hN1 : 1 ≤ N) (hr : 0 < r)
    (hsepf : (fibrePoly a s z₀).Separable)
    (w : Fin N → ℂ → ℂ)
    (hwc : ∀ k, ContinuousOn (w k) (Metric.ball z₀ r))
    (hwsep : ∀ z ∈ Metric.ball z₀ r, ∀ k l, k ≠ l → w k z ≠ w l z)
    (hwdeg : ∀ z ∈ Metric.ball z₀ r, (fibrePoly a s z).natDegree = N)
    (hwrel : ∀ k, ∀ z ∈ Metric.ball z₀ r, ∑ i ∈ s, a i z * (w k z) ^ i = 0)
    {U : Set ℂ} {β : ℂ → ℂ}
    (hUball : U ⊆ Metric.ball z₀ r) (hUbasin : U ⊆ (filledJulia c)ᶜ)
    (hUc : IsPreconnected U) (hUnhds : U ∈ 𝓝[(filledJulia c)ᶜ] z₀)
    (hβc : ContinuousOn β U)
    (hβrel : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ U) :
    ∃ (w₀ d : ℂ),
      (∑ i ∈ s, a i z₀ * w₀ ^ i = 0) ∧
      HasDerivAt (fun y => ∑ i ∈ s, a i z₀ * y ^ i) d w₀ ∧ d ≠ 0 ∧
      Tendsto β (𝓝[(filledJulia c)ᶜ] z₀) (𝓝 w₀) := by
  have hwcU : ∀ k, ContinuousOn (w k) U := fun k => (hwc k).mono hUball
  have hwsepU : ∀ z ∈ U, ∀ k l, k ≠ l → w k z ≠ w l z := fun z hz => hwsep z (hUball hz)
  have hwdegU : ∀ z ∈ U, (fibrePoly a s z).natDegree = N := fun z hz => hwdeg z (hUball hz)
  have hwrelU : ∀ k, ∀ z ∈ U, ∑ i ∈ s, a i z * (w k z) ^ i = 0 :=
    fun k z hz => hwrel k z (hUball hz)
  obtain ⟨k, hk⟩ := eqOn_branch_of_relation_analytic hN1 w β hUc hwcU hβc hwsepU hwdegU hwrelU hβrel hz₁
  have hwkAt : ContinuousAt (w k) z₀ := (hwc k).continuousAt (Metric.ball_mem_nhds z₀ hr)
  have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hroot : ∑ i ∈ s, a i z₀ * (w k z₀) ^ i = 0 := hwrel k z₀ hz₀ball
  have hrootQ : (fibrePoly a s z₀).eval (w k z₀) = 0 := by rw [eval_fibrePoly]; exact hroot
  have hd : (fibrePoly a s z₀).derivative.eval (w k z₀) ≠ 0 :=
    eval_derivative_ne_zero_of_separable hsepf hrootQ
  have hpart := relation_hasDerivAt_w_analytic a s z₀ (w k z₀)
  have htend : Tendsto β (𝓝[U] z₀) (𝓝 (w k z₀)) := tendsto_within_of_eqOn hwkAt hk
  have hfilt : 𝓝[U] z₀ = 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h1 : U ∩ (filledJulia c)ᶜ = U := inter_eq_left.mpr hUbasin
    rw [← h1]; exact nhdsWithin_inter_of_mem hUnhds
  rw [hfilt] at htend
  exact ⟨w k z₀, (fibrePoly a s z₀).derivative.eval (w k z₀), hroot, hpart, hd, htend⟩

/-- **The relative connected dendrite sub-case, closed by a basin branch (analytic coefficients).**
Mirror of `false_of_global_basin_branch`, but the coefficient family `a` is analytic only near `z₀`
(not on the whole basin — relative coefficients `aᵢ = (Qᵢ)(·,φ_{c₂})` carry their own forbidden set),
so the relation and modulus are taken on the basin sector `ball z₀ r ∩ Ω_c` directly rather than spread
from the far field. The separable-fibre branch family (`exists_branch_family_analytic`) +
`dendrite_branch_limit_analytic` give `β` a definite branch and a simple-root boundary limit; the analytic
natural-boundary obstruction `false_of_basin_branch_dendrite_analytic` closes it. Reduces the relative
dendrite case to: a dendrite tip `z₀` (`hempty`, `htip`), a basin Böttcher branch `β` carrying the
relation + genuine modulus on the basin sector, and generic fibre nondegeneracy (`hlead`, `hsep`). -/
theorem false_of_global_basin_branch_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ} {c z₀ : ℂ}
    {r : ℝ} (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hlead : a N z₀ ≠ 0) (hsep : (fibrePoly a s z₀).Separable)
    {β : ℂ → ℂ}
    (hr : 0 < r) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : Metric.ball z₀ r ∩ interior (filledJulia c) = ∅)
    (htip : ∀ ρ, 0 < ρ → IsPreconnected (Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ))
    (hβc : ContinuousOn β (Metric.ball z₀ r ∩ (filledJulia c)ᶜ))
    (hβrel : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβmod : ∀ z ∈ Metric.ball z₀ r ∩ (filledJulia c)ᶜ,
        ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    False := by
  -- the basin is dense at z₀ (Julia point, not interior of K_c)
  have hz₀int : z₀ ∉ interior (filledJulia c) := fun h => by
    have : z₀ ∈ Metric.ball z₀ r ∩ interior (filledJulia c) := ⟨Metric.mem_ball_self hr, h⟩
    rwa [hempty] at this
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [closure_compl]; exact hz₀int)
  -- the analytic branch family of the separable fibre at z₀
  obtain ⟨r', w, hr', hwc, hwsep, hwdeg, hwrel⟩ :=
    exists_branch_family_analytic hsupp hN hN1 ha hlead hsep
  set ρ : ℝ := min r r' with hρdef
  have hρ : 0 < ρ := lt_min hr hr'
  have hρr : ρ ≤ r := min_le_left _ _
  have hρr' : ρ ≤ r' := min_le_right _ _
  set U : Set ℂ := Metric.ball z₀ ρ ∩ (filledJulia c)ᶜ with hUdef
  have hUball : U ⊆ Metric.ball z₀ r' := fun z hz => Metric.ball_subset_ball hρr' hz.1
  have hUballr : U ⊆ Metric.ball z₀ r ∩ (filledJulia c)ᶜ :=
    fun z hz => ⟨Metric.ball_subset_ball hρr hz.1, hz.2⟩
  have hUbasin : U ⊆ (filledJulia c)ᶜ := inter_subset_right
  have hUc : IsPreconnected U := htip ρ hρ
  have hUnhds : U ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hρ)
    rwa [inter_comm] at h
  have hβcU : ContinuousOn β U := hβc.mono hUballr
  have hβrelU : ∀ z ∈ U, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    fun z hz => hβrel z (hUballr hz)
  obtain ⟨z₁, hz₁⟩ := hNeBot.nonempty_of_mem hUnhds
  obtain ⟨w₀, d, hroot, hpart, hd, htend⟩ :=
    dendrite_branch_limit_analytic hN1 hr' hsep w hwc hwsep hwdeg hwrel hUball hUbasin hUc hUnhds
      hβcU hβrelU hz₁
  -- filter forms of the relation and modulus along 𝓝[basin] z₀
  have hballbasin : Metric.ball z₀ r ∩ (filledJulia c)ᶜ ∈ 𝓝[(filledJulia c)ᶜ] z₀ := by
    have h := inter_mem_nhdsWithin ((filledJulia c)ᶜ) (Metric.ball_mem_nhds z₀ hr)
    rwa [inter_comm] at h
  have hβrel_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0 :=
    Filter.eventually_of_mem hballbasin hβrel
  have hβmod_filt : ∀ᶠ z in 𝓝[(filledJulia c)ᶜ] z₀, ‖β z‖ = Real.exp (greenFunctionDyn c z) :=
    Filter.eventually_of_mem hballbasin hβmod
  exact false_of_basin_branch_dendrite_analytic ha hr hz₀ hempty hroot hpart hd htend
    hβrel_filt hβmod_filt

/-- **The relative repelling-route obstruction (general — all connected Julia, no dendrite restriction).**
A nonzero analytic-coefficient relation with a simple root `(z₀,w₀)` at a NON-RESONANT repelling periodic
point `z₀∈J_{c₁}`, whose basin Böttcher branch `β` carries the relation and the Böttcher functional equation
`β(f^[p]z)=(βz)^{2^p}` on the basin side and is non-constant there, is impossible. The algebraic branch `g`
(`exists_analyticAt_branch_analytic`) matches `β` on the basin side (`branch_unique_within_analytic`),
inherits the functional equation across `z₀` by the identity theorem — using basin forward-invariance
(`not_mem_filledJulia_iterate`) so `f^[p]` keeps the basin neighbourhood inside the match region — and
`false_of_eventually_funEq_at_nonresonant` (the resonance finisher) closes it. Unlike
`false_of_global_basin_branch_analytic`, this needs NO empty-interior condition, so it covers the
quasicircle/hyperbolic connected parameters too; the only dynamical input is a non-resonant repelling
periodic point of `f_{c₁}` lying in `J_{c₁}∖filledJulia c₂` (where the continued coefficients are analytic).
Repelling periodic points are dense in every Julia set, so this is the route to the *full* nonexceptional
connected range. -/
theorem false_of_repelling_branch_analytic {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {c₁ : ℂ}
    {z₀ w₀ d lam : ℂ} {p : ℕ} {β : ℂ → ℂ}
    (ha : ∀ i ∈ s, ContDiffAt ℂ ⊤ (a i) z₀)
    (hroot : ∑ i ∈ s, a i z₀ * w₀ ^ i = 0)
    (hpartial : HasDerivAt (fun w => ∑ i ∈ s, a i z₀ * w ^ i) d w₀) (hd : d ≠ 0)
    (hw₀ : w₀ ≠ 0) (hz₀ : z₀ ∈ filledJulia c₁)
    (hNeBot : (𝓝[(filledJulia c₁)ᶜ] z₀).NeBot)
    (hβlim : Tendsto β (𝓝[(filledJulia c₁)ᶜ] z₀) (𝓝 w₀))
    (hβrel : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, ∑ i ∈ s, a i z * (β z) ^ i = 0)
    (hβfe : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀,
        β ((quadratic c₁)^[p] z) = (β z) ^ (2 ^ p))
    (hβne : ∃ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z ≠ w₀)
    (hFz : (quadratic c₁)^[p] z₀ = z₀)
    (hlam : HasDerivAt ((quadratic c₁)^[p]) lam z₀)
    (hres : ∀ m : ℕ, 1 ≤ m → lam ^ m ≠ ((2 ^ p : ℕ) : ℂ)) :
    False := by
  obtain ⟨g, hgAt, hgz₀, hgrel⟩ := exists_analyticAt_branch_analytic ha hroot hpartial hd
  have hacont : ∀ i ∈ s, ContinuousAt (a i) z₀ := fun i hi => (ha i hi).continuousAt
  have hmatch : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = β z :=
    branch_unique_within_analytic hacont hpartial hd hgAt.continuousAt hgz₀ hβlim
      (hgrel.filter_mono nhdsWithin_le_nhds) hβrel
  obtain ⟨O, hOopen, hz₀O, hOsub⟩ := mem_nhdsWithin.mp hmatch
  have hfpAt : ContinuousAt ((quadratic c₁)^[p]) z₀ :=
    (analyticOnNhd_quadratic_iterate c₁ p z₀ (mem_univ _)).continuousAt
  have hfpO : ∀ᶠ z in 𝓝 z₀, (quadratic c₁)^[p] z ∈ O :=
    hfpAt.eventually (hOopen.mem_nhds (by rw [hFz]; exact hz₀O))
  have hgfe_basin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀,
      g ((quadratic c₁)^[p] z) = (g z) ^ (2 ^ p) := by
    filter_upwards [hmatch, hβfe, self_mem_nhdsWithin,
      hfpO.filter_mono nhdsWithin_le_nhds] with z hgz hβz hzbasin hfpOz
    have hfpbasin : (quadratic c₁)^[p] z ∉ filledJulia c₁ := not_mem_filledJulia_iterate hzbasin p
    have hgfp : g ((quadratic c₁)^[p] z) = β ((quadratic c₁)^[p] z) := hOsub ⟨hfpOz, hfpbasin⟩
    rw [hgfp, hβz, hgz]
  set D : ℂ → ℂ := fun z => g ((quadratic c₁)^[p] z) - (g z) ^ (2 ^ p) with hDdef
  have hDAt : AnalyticAt ℂ D z₀ := by
    apply AnalyticAt.sub
    · have hg' : AnalyticAt ℂ g ((quadratic c₁)^[p] z₀) := by rw [hFz]; exact hgAt
      exact hg'.comp (analyticOnNhd_quadratic_iterate c₁ p z₀ (mem_univ _))
    · exact hgAt.pow (2 ^ p)
  have hDbasin : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, D z = 0 := by
    filter_upwards [hgfe_basin] with z hz; rw [hDdef]; simp only; rw [hz, sub_self]
  have hsub : 𝓝[(filledJulia c₁)ᶜ] z₀ ≤ 𝓝[≠] z₀ := by
    apply nhdsWithin_mono
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hx hz₀
  have hDfull : ∀ᶠ z in 𝓝 z₀, D z = 0 := by
    rcases hDAt.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact h
    · exact absurd (hDbasin.frequently.and_eventually (h.filter_mono hsub)).exists
        (fun ⟨z, hz⟩ => hz.2 hz.1)
  have heq : (fun z => g ((quadratic c₁)^[p] z)) =ᶠ[𝓝 z₀] (fun z => (g z) ^ (2 ^ p)) := by
    filter_upwards [hDfull] with z hz; rw [← sub_eq_zero]; exact hz
  have hζ0 : g z₀ ≠ 0 := by rw [hgz₀]; exact hw₀
  have hnoncon : ¬ (∀ᶠ z in 𝓝 z₀, g z = g z₀) := by
    intro hcon
    have hcon' : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, g z = w₀ := by
      filter_upwards [hcon.filter_mono nhdsWithin_le_nhds] with z hz; rw [hz, hgz₀]
    have hβw₀ : ∀ᶠ z in 𝓝[(filledJulia c₁)ᶜ] z₀, β z = w₀ := by
      filter_upwards [hmatch, hcon'] with z hgz hgw; rw [← hgz, hgw]
    exact (hβne.and_eventually hβw₀).exists.elim (fun z hz => hz.1 hz.2)
  exact false_of_eventually_funEq_at_nonresonant hgAt heq hFz hlam hζ0 hres hnoncon

end Bottcher
