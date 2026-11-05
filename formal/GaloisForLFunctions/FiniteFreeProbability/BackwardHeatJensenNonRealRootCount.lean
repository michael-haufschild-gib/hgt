import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman
import GaloisForLFunctions.HTGeometry.HurwitzClosedZeroLocus
import GaloisForLFunctions.RHTower.DeBruijnStripThreshold

/-!
# Backward heat gives the Jensen polynomials of `Ξ` unboundedly many non-real roots

For every `t > 0` and every `M`, the polynomial `e^{(t/d²)D²} J_d = J_d ⊞_d He_{d,t/d²}` has at
least `M` distinct non-real roots once `d` is large.

Mechanism. The scaled polynomials `z ↦ (e^{(t/d²)D²} J_d)(z/d)` converge locally uniformly to
`H_{−t}`, which has infinitely many non-real zeros (Newman's conjecture, proved in the corpus).
Around `M` of them choose disjoint discs off the real axis; by Hurwitz's theorem each disc
eventually contains a zero of the scaled polynomial. So the finite free deficit of a Gaussian
factor at the de Bruijn–Newman scale is not one stray pair of roots: the number of roots it pushes
off the line is unbounded, and in the scale `z = d·x` the roots leave every horizontal strip
(because the zeros of `H_{−t}` do).
-/

open Polynomial Filter Topology Complex Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

theorem analyticOnNhd_riemannHeat_neg {τ : ℝ} (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (riemannHeat (-τ)) Set.univ :=
  ((superExpKernel_mul_exp_neg_sq hτ).differentiable.differentiableOn).analyticOnNhd isOpen_univ

theorem riemannHeat_neg_zero_ne {τ : ℝ} (hτ : 0 ≤ τ) : riemannHeat (-τ) 0 ≠ 0 :=
  (superExpKernel_mul_exp_neg_sq hτ).cosTransform_zero_ne

/-- Locally uniform convergence survives passing to a strictly increasing subsequence. -/
theorem tendstoLocallyUniformly_comp_strictMono {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (h : TendstoLocallyUniformly F f atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformly (fun m => F (φ m)) f atTop := fun u hu x => by
  obtain ⟨s, hs, hev⟩ := h u hu x
  exact ⟨s, hs, hφ.tendsto_atTop.eventually hev⟩

/-- **Hurwitz step.** Every zero of `H_{−t}` attracts a zero of the scaled backward-heat Jensen
polynomial into each of its disc neighbourhoods, for all large `d`. -/
theorem eventually_exists_zero_scaledHeatJensen_mem_ball {τ : ℝ} (hτ : 0 ≤ τ) {z₀ : ℂ}
    (hz₀ : riemannHeat (-τ) z₀ = 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ d : ℕ in atTop, ∃ w ∈ ball z₀ r, scaledHeatJensen τ d w = 0 := by
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨φ, hφ, hno⟩ := Filter.extraction_of_frequently_atTop h
  have hconv := tendstoLocallyUniformly_comp_strictMono
    (tendstoLocallyUniformly_scaledHeatJensen hτ) hφ
  have hmem := GaloisForLFunctions.HTGeometry.zero_mem_closed_of_tendstoLocallyUniformly
    (S := (ball z₀ r)ᶜ) hconv
    (analyticOnNhd_riemannHeat_neg hτ)
    (Eventually.of_forall fun m => differentiable_scaledHeatJensen τ (φ m))
    isOpen_ball.isClosed_compl
    (Eventually.of_forall fun m w hw hwb => hno m ⟨w, hwb, hw⟩)
    (riemannHeat_neg_zero_ne hτ) hz₀
  exact hmem (mem_ball_self hr)

/-- **Unboundedly many non-real roots.** For every `t > 0` and `M`, all large `d` give
`e^{(t/d²)D²} J_d` at least `M` distinct non-real roots. -/
theorem eventually_le_card_nonreal_roots_heatOp_jensenPoly_XiC {τ : ℝ} (hτ : 0 < τ) (M : ℕ) :
    ∀ᶠ d : ℕ in atTop, M ≤ ((((heatOp (τ / (d : ℝ) ^ 2) d
      (jensenPoly (realTaylorCoeff XiC) d)).map (algebraMap ℝ ℂ)).roots.toFinset.filter
        fun z => z.im ≠ 0).card) := by
  classical
  obtain ⟨T, hTs, hTcard⟩ := (riemannHeat_neg_nonreal_zeros_infinite hτ).exists_subset_card_eq M
  -- a common radius: discs off the real axis and pairwise disjoint
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∀ z ∈ T, r < |z.im|) ∧ ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * r < ‖z - w‖ := by
    have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    refine (Filter.eventually_all_finset T).2 (fun z hz => ?_) |>.and
      ((Filter.eventually_all_finset T).2 fun z hz => (Filter.eventually_all_finset T).2
        fun w hw => ?_)
    · have him : 0 < |z.im| := abs_pos.2 (hTs hz).2
      exact hr0.eventually (gt_mem_nhds him)
    · by_cases hzw : z = w
      · exact Eventually.of_forall fun _ h => absurd hzw h
      · have hpos : 0 < ‖z - w‖ / 2 := by
          have := norm_pos_iff.2 (sub_ne_zero.2 hzw); positivity
        filter_upwards [hr0.eventually (gt_mem_nhds hpos)] with r hr _
        linarith
  obtain ⟨r, ⟨hrT, hrdisj⟩, hrpos⟩ := (hsmall.and self_mem_nhdsWithin).exists
  have hrpos' : 0 < r := hrpos
  have hev : ∀ᶠ d : ℕ in atTop, ∀ z ∈ T, ∃ w ∈ ball z r, scaledHeatJensen τ d w = 0 :=
    (Filter.eventually_all_finset T).2 fun z hz =>
      eventually_exists_zero_scaledHeatJensen_mem_ball hτ.le (hTs hz).1 hrpos'
  have hne : ∀ᶠ d : ℕ in atTop, scaledHeatJensen τ d 0 ≠ 0 :=
    (tendsto_scaledHeatJensen hτ.le 0).eventually_ne (riemannHeat_neg_zero_ne hτ.le)
  filter_upwards [hev, hne, eventually_gt_atTop 0] with d hd hd0 hdpos
  set P := (heatOp (τ / (d : ℝ) ^ 2) d (jensenPoly (realTaylorCoeff XiC) d)).map (algebraMap ℝ ℂ)
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hP0 : P ≠ 0 := fun h0 => hd0 (by simp [scaledHeatJensen, P, h0])
  choose! w hw hw0 using hd
  rw [← hTcard]
  refine Finset.card_le_card_of_injOn (fun z => w z / d) (fun z hz => ?_) (fun z hz z' hz' h => ?_)
  · have hroot : P.IsRoot (w z / d) := by
      have := hw0 z hz; rwa [scaledHeatJensen] at this
    have hwz := hw z hz
    rw [mem_ball, dist_eq_norm] at hwz
    have him : (w z).im ≠ 0 := by
      intro h0
      have h1 : |(w z - z).im| ≤ ‖w z - z‖ := Complex.abs_im_le_norm _
      rw [sub_im, h0, zero_sub, abs_neg] at h1
      linarith [hrT z hz]
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Multiset.mem_toFinset]
    refine ⟨(mem_roots hP0).2 hroot, ?_⟩
    rw [div_natCast_im]
    exact div_ne_zero him (by exact_mod_cast hdpos.ne')
  · have hwe : w z = w z' := by
      have := h; simp only at this; exact (div_left_inj' hdC).1 this
    by_contra hzz
    have h1 := hw z hz
    have h2 := hw z' hz'
    rw [mem_ball, dist_eq_norm] at h1 h2
    have := hrdisj z hz z' hz' hzz
    have htri : ‖z - z'‖ ≤ ‖w z - z‖ + ‖w z - z'‖ := by
      calc ‖z - z'‖ = ‖(w z - z') - (w z - z)‖ := by ring_nf
        _ ≤ ‖w z - z'‖ + ‖w z - z‖ := norm_sub_le _ _
        _ = _ := by ring
    rw [hwe] at h1 htri
    linarith


/-- **The roots leave every strip.** For every `t > 0` and `D`, all large `d` give
`e^{(t/d²)D²} J_d` a root `x` with `|Im (d x)| > D`. -/
theorem eventually_exists_deep_root_heatOp_jensenPoly_XiC {τ : ℝ} (hτ : 0 < τ) (D : ℝ) :
    ∀ᶠ d : ℕ in atTop, ∃ x : ℂ, ((heatOp (τ / (d : ℝ) ^ 2) d
      (jensenPoly (realTaylorCoeff XiC) d)).map (algebraMap ℝ ℂ)).IsRoot x ∧
        D < |((d : ℂ) * x).im| := by
  obtain ⟨z₀, hz₀, -, hdeep⟩ := exists_riemannHeat_zero_abs_im_gt_of_neg (t := -τ) (by linarith)
    (D + 1) 0
  filter_upwards [eventually_exists_zero_scaledHeatJensen_mem_ball hτ.le hz₀ one_pos,
    eventually_gt_atTop 0] with d hd hdpos
  obtain ⟨w, hw, hw0⟩ := hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hdpos.ne'
  refine ⟨w / d, by rwa [scaledHeatJensen] at hw0, ?_⟩
  rw [mul_div_cancel₀ _ hdC]
  rw [mem_ball, dist_eq_norm] at hw
  have h1 : |(w - z₀).im| ≤ ‖w - z₀‖ := Complex.abs_im_le_norm _
  rw [sub_im] at h1
  have h2 := abs_sub_abs_le_abs_sub z₀.im w.im
  rw [abs_sub_comm] at h1
  linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_le_card_nonreal_roots_heatOp_jensenPoly_XiC
#print axioms FiniteFreeProbability.eventually_exists_deep_root_heatOp_jensenPoly_XiC
