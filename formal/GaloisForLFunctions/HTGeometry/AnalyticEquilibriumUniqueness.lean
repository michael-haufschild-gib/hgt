import Mathlib

/-!
# Uniqueness at an equilibrium of an autonomous equation

A holomorphic solution of `F' = c(F)` that meets a root of `c` is constant.  The mechanism is
Gronwall, not the order of vanishing: writing `c = (X − a)·p` gives `G' = G·p(F)` for `G = F − a`, so
on a small ball the derivative is dominated by `C‖G‖`, the maximum `M` over the ball satisfies
`M ≤ ρCM`, and `ρC < 1` forces `M = 0`.  The identity theorem then propagates the vanishing to the
plane.

Equivalently: a nonconstant entire solution of `F' = c(F)` omits every root of `c`.  That is the
local half of the Briot–Bouquet no-go, and it needs no value distribution.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Gronwall vanishing for an entire function.**  If `G` vanishes at `z₀` and its derivative is
dominated by `C‖G‖` on a closed ball of radius `ρ` with `ρC < 1`, then `G` vanishes identically:
the maximum `M` on the ball satisfies `M ≤ ρ C M`, and the identity theorem propagates. -/
theorem eq_zero_of_zero_of_norm_deriv_le_on_ball {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {z₀ : ℂ} {rho C : ℝ} (hrho : 0 < rho) (hC : 0 ≤ C) (hrhoC : rho * C < 1)
    (hbd : ∀ z ∈ Metric.closedBall z₀ rho, ‖deriv G z‖ ≤ C * ‖G z‖)
    (hz₀ : G z₀ = 0) : G = 0 := by
  classical
  set K : Set ℂ := Metric.closedBall z₀ rho with hK
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hKne : K.Nonempty := ⟨z₀, Metric.mem_closedBall_self hrho.le⟩
  obtain ⟨w, hwK, hwmax⟩ := hKcompact.exists_isMaxOn hKne hG.continuous.norm.continuousOn
  set M : ℝ := ‖G w‖ with hM
  have hMmax : ∀ z ∈ K, ‖G z‖ ≤ M := fun z hz => hwmax hz
  have hM0 : 0 ≤ M := norm_nonneg _
  have hderivle : ∀ z ∈ K, ‖deriv G z‖ ≤ C * M := by
    intro z hz
    refine le_trans (hbd z hz) ?_
    exact mul_le_mul_of_nonneg_left (hMmax z hz) hC
  have hmvt : ‖G w - G z₀‖ ≤ (C * M) * ‖w - z₀‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun x _ => hG x) hderivle
      (convex_closedBall z₀ rho) (Metric.mem_closedBall_self hrho.le) hwK
  have hdist : ‖w - z₀‖ ≤ rho := by
    have := Metric.mem_closedBall.mp hwK
    rwa [dist_eq_norm] at this
  have hMle : M ≤ C * M * rho := by
    rw [hz₀, sub_zero] at hmvt
    calc M = ‖G w‖ := rfl
      _ ≤ (C * M) * ‖w - z₀‖ := hmvt
      _ ≤ (C * M) * rho := mul_le_mul_of_nonneg_left hdist (by positivity)
  have hMzero : M = 0 := by nlinarith [hMle, hM0, hrhoC, hrho, hC]
  have hdisc : ∀ z ∈ K, G z = 0 := by
    intro z hz
    have h := hMmax z hz
    rw [hMzero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hev : G =ᶠ[nhds z₀] 0 := by
    refine Metric.eventually_nhds_iff.mpr ⟨rho, hrho, fun z hz => ?_⟩
    exact hdisc z (Metric.mem_closedBall.mpr hz.le)
  have hAn : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have hall := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hev
  funext z
  exact hall (Set.mem_univ z)

/-- **A solution that meets an equilibrium is constant.**  If `F' = c(F)` and `F` takes at some point
a root `a` of `c`, then `F` is the constant `a`.  Equivalently, a nonconstant entire solution omits
every root of `c`. -/
theorem eq_const_of_root_of_deriv_eq_comp {c : Polynomial ℂ} {a : ℂ} (hca : c.eval a = 0)
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (heq : ∀ z, deriv F z = c.eval (F z))
    {z₀ : ℂ} (hz₀ : F z₀ = a) : F = fun _ => a := by
  classical
  obtain ⟨p, hp⟩ : (Polynomial.X - Polynomial.C a) ∣ c :=
    Polynomial.dvd_iff_isRoot.mpr hca
  set G : ℂ → ℂ := fun z => F z - a with hG
  have hGdiff : Differentiable ℂ G := hF.sub_const a
  have hGderiv : ∀ z, deriv G z = G z * p.eval (F z) := by
    intro z
    have hd : deriv G z = deriv F z := by
      rw [hG]
      exact deriv_sub_const a
    rw [hd, heq z, hp]
    simp [hG]
  -- bound the factor on the unit ball around `z₀`
  have hcontp : ContinuousOn (fun z => ‖p.eval (F z)‖) (Metric.closedBall z₀ 1) :=
    (continuous_norm.comp (p.continuous_aeval.comp hF.continuous)).continuousOn
  obtain ⟨u, huK, humax⟩ :=
    (isCompact_closedBall z₀ 1).exists_isMaxOn ⟨z₀, Metric.mem_closedBall_self zero_le_one⟩ hcontp
  set C : ℝ := ‖p.eval (F u)‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  set rho : ℝ := min 1 (1 / (2 * (C + 1))) with hrhodef
  have hrho0 : 0 < rho := lt_min zero_lt_one (by positivity)
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhoC : rho * C < 1 := by
    have h1 : rho ≤ 1 / (2 * (C + 1)) := min_le_right _ _
    have h2 : rho * C ≤ (1 / (2 * (C + 1))) * C := by nlinarith [hC0, hrho0]
    have h3 : (1 / (2 * (C + 1))) * C < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
      linarith
    linarith
  have hbd : ∀ z ∈ Metric.closedBall z₀ rho, ‖deriv G z‖ ≤ C * ‖G z‖ := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall z₀ 1 :=
      Metric.closedBall_subset_closedBall hrho1 hz
    have hpz : ‖p.eval (F z)‖ ≤ C := humax hz1
    rw [hGderiv z, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hpz (norm_nonneg _)
  have hGz₀ : G z₀ = 0 := by
    rw [hG]
    simp [hz₀]
  have := eq_zero_of_zero_of_norm_deriv_le_on_ball hGdiff hrho0 hC0 hrhoC hbd hGz₀
  funext z
  have hz : G z = 0 := congrFun this z
  rw [hG] at hz
  simp only at hz
  linear_combination hz

end GaloisForLFunctions.HTGeometry
