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

/-- **The Laplace exponential is Lipschitz on a bounded interval.**  `x ↦ e^{-wx}` is
`(‖w‖·e^{|Re w|·T})`-Lipschitz on `[0, T]`, via its derivative bound.  This is the exponential factor's
modulus of continuity underlying the moving-window Riemann-sum estimate. -/
theorem lipschitzOnWith_cexp_neg_mul (w : ℂ) (T : ℝ) (hT : 0 ≤ T) :
    LipschitzOnWith (Real.toNNReal (‖w‖ * Real.exp (|w.re| * T)))
      (fun x : ℝ => Complex.exp (-w * (x : ℂ))) (Set.Icc 0 T) := by
  have hd : ∀ x ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (fun t : ℝ => Complex.exp (-w * (t : ℂ)))
      (-w * Complex.exp (-w * (x : ℂ))) (Set.Icc 0 T) x := by
    intro x _
    have hx1 : HasDerivAt (fun t : ℝ => -w * (t : ℂ)) (-w) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-w)
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (-w * (t : ℂ)))
        (-w * Complex.exp (-w * (x : ℂ))) x := by
      have := hx1.cexp; convert this using 1; ring
    exact h2.hasDerivWithinAt
  have hb : ∀ x ∈ Set.Icc (0 : ℝ) T,
      ‖-w * Complex.exp (-w * (x : ℂ))‖₊ ≤ Real.toNNReal (‖w‖ * Real.exp (|w.re| * T)) := by
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
    rw [norm_mul, norm_neg, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
    apply Real.exp_le_exp.mpr
    have hre : (-w * (x : ℂ)).re = -(w.re) * x := by simp [Complex.mul_re]
    rw [hre]
    nlinarith [le_abs_self w.re, neg_abs_le w.re, hx.1, hx.2, abs_nonneg w.re]
  exact Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 T) hd hb

/-- **Product of two bounded Lipschitz functions is Lipschitz** (normed-ring valued).  If `f` is
`Kf`-Lipschitz and bounded by `Mf` on `s`, and `g` is `Kg`-Lipschitz and bounded by `Mg`, then `f·g`
is `(Mf·Kg + Mg·Kf)`-Lipschitz on `s`.  Mathlib's `LipschitzOnWith.mul` only covers a
`SeminormedCommGroup` (the multiplicative *group*, which excludes a ring with a zero such as `ℂ`); this
is the normed-ring form via `‖fg(x)−fg(y)‖ ≤ ‖f x‖‖g x−g y‖ + ‖f x−f y‖‖g y‖`.  It supplies the
modulus of continuity of any windowed integrand `τ(x)·e^{-wx}` (bounded window × bounded exponential). -/
theorem lipschitzOnWith_mul_of_bound {α E : Type*} [PseudoMetricSpace α] [NormedRing E]
    {Kf Kg : NNReal} {Mf Mg : ℝ} {f g : α → E} {s : Set α}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s)
    (hMf : ∀ x ∈ s, ‖f x‖ ≤ Mf) (hMg : ∀ x ∈ s, ‖g x‖ ≤ Mg) :
    LipschitzOnWith (Real.toNNReal Mf * Kg + Real.toNNReal Mg * Kf) (fun x => f x * g x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul] at hf hg ⊢
  intro x hx y hy
  have hfx : (0 : ℝ) ≤ Mf := le_trans (norm_nonneg _) (hMf x hx)
  have hgy : (0 : ℝ) ≤ Mg := le_trans (norm_nonneg _) (hMg y hy)
  have hdf := hf x hx y hy
  have hdg := hg x hx y hy
  calc dist (f x * g x) (f y * g y)
      = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
        rw [dist_eq_norm, show f x * g x - f y * g y
          = f x * (g x - g y) + (f x - f y) * g y from by noncomm_ring]
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
        le_trans (norm_add_le _ _) (by gcongr <;> exact norm_mul_le _ _)
    _ = ‖f x‖ * dist (g x) (g y) + dist (f x) (f y) * ‖g y‖ := by
        rw [dist_eq_norm, dist_eq_norm]
    _ ≤ Mf * (Kg * dist x y) + (Kf * dist x y) * Mg :=
        add_le_add
          (mul_le_mul (hMf x hx) hdg dist_nonneg hfx)
          (mul_le_mul hdf (hMg y hy) (norm_nonneg _) (by positivity))
    _ = (Real.toNNReal Mf * Kg + Real.toNNReal Mg * Kf) * dist x y := by
        rw [Real.coe_toNNReal Mf hfx, Real.coe_toNNReal Mg hgy]; ring

/-- **`Real.log` is `1`-Lipschitz on `[1, ∞)`.**  Its derivative there is `x⁻¹ ≤ 1`.  This is the
modulus of continuity of the logarithmic change of variables `u ↦ log u` on the multiplicative window
`u ≥ 1`, feeding the moving-tent-of-log Lipschitz estimate. -/
theorem lipschitzOnWith_log_Ici_one : LipschitzOnWith 1 Real.log (Set.Ici (1 : ℝ)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ici 1) (f' := fun x => x⁻¹)
  · intro x hx
    have hx0 : x ≠ 0 := by have : (1 : ℝ) ≤ x := hx; positivity
    exact (Real.hasDerivAt_log hx0).hasDerivWithinAt
  · intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    rw [inv_le_one_iff₀]; right; exact hx1

end HTGeometry
