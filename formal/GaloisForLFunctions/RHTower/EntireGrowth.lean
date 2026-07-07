/-
# Generalized Liouville: an entire function of polynomial growth is a polynomial

mathlib has Liouville (bounded entire ⟹ constant) but not its polynomial-growth
generalization.  This file supplies it: if `f : ℂ → ℂ` is entire and `‖f z‖ ≤ M(‖z‖+1)^d`,
then all Taylor coefficients past degree `d` vanish and `f` equals its degree-`d` Taylor
polynomial.  The tool is the iterated Cauchy estimate
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` on spheres of radius `R → ∞`,
plus the identity theorem to kill the remainder.  This is the analytic input to the
classification of entire automorphisms of `ℂ`.
-/
import Mathlib

namespace RHTower

open Complex Metric Topology Filter Set

/-- `(R+1)^d / R^n → 0` as `R → ∞` when `d < n`: the polynomial numerator is dominated. -/
theorem tendsto_add_one_pow_div_pow {d n : ℕ} (hn : d < n) :
    Tendsto (fun R : ℝ => (R + 1) ^ d / R ^ n) atTop (𝓝 0) := by
  have hkey : Tendsto (fun R : ℝ => (2 : ℝ) ^ d * R ^ (d - n : ℤ)) atTop (𝓝 0) := by
    have : Tendsto (fun R : ℝ => R ^ (d - n : ℤ)) atTop (𝓝 0) :=
      tendsto_zpow_atTop_zero (by omega)
    simpa using this.const_mul ((2 : ℝ) ^ d)
  refine squeeze_zero' ?_ ?_ hkey
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have hle1 : R + 1 ≤ 2 * R := by nlinarith
    have h1 : (R + 1) ^ d ≤ (2 * R) ^ d := by gcongr
    have h2 : (2 * R) ^ d / R ^ n = (2 : ℝ) ^ d * R ^ (d - n : ℤ) := by
      rw [mul_pow, zpow_sub₀ hR0.ne', zpow_natCast, zpow_natCast, mul_div_assoc,
        div_eq_mul_inv]
    calc (R + 1) ^ d / R ^ n ≤ (2 * R) ^ d / R ^ n := by gcongr
      _ = (2 : ℝ) ^ d * R ^ (d - n : ℤ) := h2

/-- **Cauchy estimate at infinity kills high Taylor coefficients.**  If `f` is entire and
grows at most like `‖z‖^d`, then `iteratedDeriv n f 0 = 0` for every `n > d`. -/
theorem iteratedDeriv_eq_zero_of_polyGrowth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {M : ℝ} {d : ℕ} (hgrow : ∀ z : ℂ, ‖f z‖ ≤ M * (‖z‖ + 1) ^ d)
    {n : ℕ} (hn : d < n) :
    iteratedDeriv n f 0 = 0 := by
  have hM0 : 0 ≤ M := by
    have := hgrow 0
    simp only [norm_zero, zero_add, one_pow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have hbound : ∀ R : ℝ, 0 < R →
      ‖iteratedDeriv n f 0‖ ≤ n.factorial * (M * (R + 1) ^ d) / R ^ n := by
    intro R hR
    refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
      (hf.diffContOnCl) ?_
    intro z hz
    have hznorm : ‖z‖ = R := by
      rw [mem_sphere_iff_norm, sub_zero] at hz; exact hz
    calc ‖f z‖ ≤ M * (‖z‖ + 1) ^ d := hgrow z
      _ = M * (R + 1) ^ d := by rw [hznorm]
  have htend : Tendsto (fun R : ℝ => (n.factorial : ℝ) * (M * (R + 1) ^ d) / R ^ n)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ => (R + 1) ^ d / R ^ n) atTop (𝓝 0) :=
      tendsto_add_one_pow_div_pow hn
    have : Tendsto (fun R : ℝ => ((n.factorial : ℝ) * M) * ((R + 1) ^ d / R ^ n))
        atTop (𝓝 (((n.factorial : ℝ) * M) * 0)) := h0.const_mul _
    rw [mul_zero] at this
    refine this.congr ?_
    intro R; ring
  have hle : ‖iteratedDeriv n f 0‖ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hbound R hR
  exact norm_le_zero_iff.mp hle

/-- **All Taylor coefficients zero ⟹ the entire function is zero.**  If every iterated
derivative of an entire `g` vanishes at `0`, then `g` vanishes identically (order `⊤` at `0`
plus the identity theorem on the connected plane). -/
theorem eq_zero_of_iteratedDeriv_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ n : ℕ, iteratedDeriv n g 0 = 0) : g = 0 := by
  have hga : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hga0 : AnalyticAt ℂ g 0 := hga 0 (Set.mem_univ 0)
  have htop : analyticOrderAt g 0 = ⊤ := by
    by_contra hfin
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt g 0 := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hga0]
      intro i _
      exact h i
    rw [← hm] at hle
    have : (m + 1 : ℕ) ≤ m := by exact_mod_cast hle
    omega
  have hev : g =ᶠ[𝓝 0] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  funext z
  exact hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ 0) hev (Set.mem_univ z)

end RHTower
