import Mathlib

/-!
# Single-cell Riemann-sum error bound

The per-cell error between an integral and its left-endpoint rectangle, for a function with a linear
modulus of continuity (in particular any Lipschitz function), absent from mathlib:

`‖∫_c^{c+h} f − h·f(c)‖ ≤ K·h²/2`   whenever  `‖f(x) − f(c)‖ ≤ K·(x − c)` on `[c, c+h]`.

Summed over a uniform partition this gives the `O(h)` convergence of Riemann sums of a Lipschitz
integrand — the uniform cellwise estimate underlying the moving-window Riemann-sum tomography lemmas.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace HTGeometry

/-- **Single-cell Riemann error.**  If `‖f(x) − f(c)‖ ≤ K·(x − c)` on the cell `[c, c+h]` (`h ≥ 0`),
the integral differs from the left-endpoint rectangle `h·f(c)` by at most `K·h²/2`. -/
theorem norm_integral_sub_smul_le {f : ℝ → ℂ} {K c h : ℝ} (hh : 0 ≤ h)
    (hint : IntervalIntegrable f volume c (c + h))
    (hbound : ∀ x ∈ Set.Icc c (c + h), ‖f x - f c‖ ≤ K * (x - c)) :
    ‖(∫ x in c..(c + h), f x) - h • f c‖ ≤ K * h ^ 2 / 2 := by
  have hcle : c ≤ c + h := by linarith
  have hconst : (∫ _x in c..(c + h), f c) = h • f c := by
    rw [intervalIntegral.integral_const]; congr 1; ring
  have hnorm_int : IntervalIntegrable (fun x => ‖f x - f c‖) volume c (c + h) :=
    (hint.sub (continuous_const.intervalIntegrable _ _)).norm
  have hlin_int : IntervalIntegrable (fun x => K * (x - c)) volume c (c + h) :=
    (by fun_prop : Continuous (fun x : ℝ => K * (x - c))).intervalIntegrable _ _
  have hxc : (∫ x in c..(c + h), (x - c)) = h ^ 2 / 2 := by
    have hd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => (t - c) ^ 2 / 2) (x - c) x := by
      intro x
      have h2 := (((hasDerivAt_id x).sub_const c).pow 2).div_const 2
      convert h2 using 1
      simp only [id_eq]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous (fun x : ℝ => x - c)).intervalIntegrable _ _)]
    ring
  rw [← hconst, ← intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable _ _)]
  calc ‖∫ x in c..(c + h), (f x - f c)‖
      ≤ ∫ x in c..(c + h), ‖f x - f c‖ := intervalIntegral.norm_integral_le_integral_norm hcle
    _ ≤ ∫ x in c..(c + h), K * (x - c) :=
        intervalIntegral.integral_mono_on hcle hnorm_int hlin_int hbound
    _ = K * h ^ 2 / 2 := by rw [intervalIntegral.integral_const_mul, hxc]; ring

/-- **Uniform Riemann-sum error.**  Iterating the single-cell bound over the uniform grid
`a + k·h` (`k < N`): the left-endpoint Riemann sum differs from the integral over `[a, a+Nh]` by at
most `N·K·h²/2 = K·(b−a)·h/2`, when `f` has slope-`K` modulus of continuity on each cell. -/
theorem norm_sum_smul_sub_integral_le {f : ℝ → ℂ} {K a h : ℝ} {N : ℕ} (hh : 0 ≤ h)
    (hint : IntervalIntegrable f volume a (a + N * h))
    (hbound : ∀ k : ℕ, k < N → ∀ x ∈ Set.Icc (a + k * h) (a + k * h + h),
      ‖f x - f (a + k * h)‖ ≤ K * (x - (a + k * h))) :
    ‖(∑ k ∈ Finset.range N, h • f (a + k * h)) - ∫ x in a..(a + N * h), f x‖
      ≤ N * K * h ^ 2 / 2 := by
  set g : ℕ → ℝ := fun k => a + k * h with hg
  have hstep : ∀ k : ℕ, g (k + 1) = g k + h := by intro k; simp only [hg]; push_cast; ring
  have hcell : ∀ k, k < N → IntervalIntegrable f volume (g k) (g (k + 1)) := by
    intro k hk
    refine hint.mono_set ?_
    have hkR : (k : ℝ) ≤ N := Nat.cast_le.mpr hk.le
    have hk1R : ((k : ℝ) + 1) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
    rw [Set.uIcc_of_le (by simp only [hg]; push_cast; nlinarith [hh]),
        Set.uIcc_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) N])]
    refine Set.Icc_subset_Icc ?_ ?_
    · simp only [hg]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    · simp only [hg]; push_cast; nlinarith
  have hgrid : (∫ x in a..(a + N * h), f x)
      = ∑ k ∈ Finset.range N, ∫ x in (g k)..(g (k + 1)), f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hcell]
    simp only [hg, Nat.cast_zero, zero_mul, add_zero]
  rw [hgrid, ← Finset.sum_sub_distrib]
  calc ‖∑ k ∈ Finset.range N, (h • f (g k) - ∫ x in (g k)..(g (k + 1)), f x)‖
      ≤ ∑ k ∈ Finset.range N, ‖h • f (g k) - ∫ x in (g k)..(g (k + 1)), f x‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, K * h ^ 2 / 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hk' : k < N := Finset.mem_range.mp hk
        calc ‖h • f (g k) - ∫ x in (g k)..(g (k + 1)), f x‖
            = ‖(∫ x in (g k)..(g k + h), f x) - h • f (g k)‖ := by rw [hstep k, norm_sub_rev]
          _ ≤ K * h ^ 2 / 2 :=
              norm_integral_sub_smul_le hh (hstep k ▸ hcell k hk') (hbound k hk')
    _ = N * K * h ^ 2 / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Uniform Riemann-sum error for a Lipschitz integrand.**  The `LipschitzWith`-hypothesised form of
`norm_sum_smul_sub_integral_le`: for `f` globally `K`-Lipschitz, the left-endpoint Riemann sum over the
grid `a + k·h` differs from `∫_a^{a+Nh} f` by at most `N·K·h²/2`.  Directly composable with any
`LipschitzWith` bound (e.g. the tent window's). -/
theorem norm_sum_smul_sub_integral_le_of_lipschitzWith {f : ℝ → ℂ} {K a h : ℝ} {N : ℕ}
    (hh : 0 ≤ h) (hK : 0 ≤ K) (hint : IntervalIntegrable f volume a (a + N * h))
    (hlip : LipschitzWith K.toNNReal f) :
    ‖(∑ k ∈ Finset.range N, h • f (a + k * h)) - ∫ x in a..(a + N * h), f x‖
      ≤ N * K * h ^ 2 / 2 := by
  refine norm_sum_smul_sub_integral_le hh hint (fun k _ x hx => ?_)
  have hxc : a + k * h ≤ x := hx.1
  have hn := hlip.norm_sub_le x (a + k * h)
  rwa [Real.coe_toNNReal K hK, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hn

end HTGeometry
