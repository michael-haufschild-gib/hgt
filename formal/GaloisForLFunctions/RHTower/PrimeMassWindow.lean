import GaloisForLFunctions.RHTower.PrimeMassLowerBound

/-!
# The prime mass of a multiplicative window is of order `√y`

The aperture-dependent part of the rectangular prime wall is a tent riding on the multiplicative
window `(n·e^{−2L}, n)`.  Whether the criterion is a delicate comparison or a trivially satisfied
one depends on whether that window carries mass comparable to the archimedean budget, so it is worth
knowing unconditionally that the window is **not** asymptotically negligible.

Chebyshev's two bounds suffice.  For a window `(x, y]`,

```text
∑_{x < k ≤ y} Λ(k)/√k  ≥  (ψ(y) − ψ(x))/√y ,
```

by the same termwise weighting used for the full range, and `ψ(y) − ψ(x)` is bounded below by
`(log 2)(y−1) − log(y+2) − (log 4 + 4)x`.  So once the window's multiplicative width exceeds
`(log 4 + 4)/log 2` the mass is a positive multiple of `√y`.

The threshold is an artefact of the Chebyshev constants, not of the mathematics: the true ratio is
`1`, since `ψ(y) − ψ(x) ~ y − x`.  Neither mathlib nor this corpus contains the prime number
theorem, so the sharp form is not currently formalizable — only Chebyshev-strength statements are.
-/

open Filter Finset Real

namespace RHTower

open ArithmeticFunction Chebyshev

/-- The half-weighted prime mass of the window `(x, y]`. -/
noncomputable def primeMassWindow (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊, ArithmeticFunction.vonMangoldt k / Real.sqrt k

/-- The window mass is the difference of Chebyshev functions, weighted down by `√y`. -/
theorem psi_sub_div_sqrt_le_primeMassWindow {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (Chebyshev.psi y - Chebyshev.psi x) / Real.sqrt y ≤ primeMassWindow x y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hfloor : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_le_floor hxy
  have hdiff : Chebyshev.psi y - Chebyshev.psi x
      = ∑ k ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊, ArithmeticFunction.vonMangoldt k := by
    have hdisj : Disjoint (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊) (Finset.Icc 0 ⌊x⌋₊) := by
      refine Finset.disjoint_left.mpr fun k hk hk' => ?_
      simp only [Finset.mem_Icc] at hk hk'
      omega
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, sub_eq_iff_eq_add,
      ← Finset.sum_union hdisj]
    congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc, Nat.zero_le, true_and]
    omega
  rw [hdiff, primeMassWindow, Finset.sum_div]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1.trans' (by omega)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hky : (k : ℝ) ≤ y :=
    le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2) (Nat.floor_le hy)
  have hsq : Real.sqrt k ≤ Real.sqrt y := Real.sqrt_le_sqrt hky
  have hsqpos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hkpos
  exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hsqpos hsq

/-- **Chebyshev bracket for a window.**  The prime count in `(x, y]` is at least
`(log 2)(y−1) − log(y+2) − (log 4 + 4)x`. -/
theorem chebyshev_window_lower {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (y - 1) * Real.log 2 - Real.log (y + 2) - (Real.log 4 + 4) * x
      ≤ Chebyshev.psi y - Chebyshev.psi x := by
  have hy : 0 ≤ y := le_trans hx hxy
  have h1 := Chebyshev.psi_ge' hy
  have h2 := Chebyshev.psi_le_const_mul_self hx
  linarith

/-- **The window mass is a positive multiple of `√y` once the width clears the Chebyshev ratio.**
Stated with the width as an explicit hypothesis, so it applies to the moving tent of a rectangular
window of any sufficiently large aperture. -/
theorem sqrt_le_primeMassWindow_of_wide {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy1 : 1 ≤ y)
    (hwide : (Real.log 4 + 4) * x + Real.log 2 + Real.log (y + 2) + Real.log 2 * y / 2
      ≤ Real.log 2 * y) :
    (Real.log 2 / 2) * Real.sqrt y ≤ primeMassWindow x y := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hsqrtpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy
  refine le_trans ?_ (psi_sub_div_sqrt_le_primeMassWindow hx hxy)
  rw [le_div_iff₀ hsqrtpos, mul_assoc, hsq]
  refine le_trans ?_ (chebyshev_window_lower hx hxy)
  linarith

/-- **Non-degeneracy of the moving tent.**  For a fixed multiplicative ratio `r` exceeding the
Chebyshev ratio `(log 4 + 4)/log 2`, the window `(y/r, y]` eventually carries mass at least
`(log 2 / 2)·√y`.  So the aperture-dependent part of the prime wall is genuinely of order `√n`, and
the criterion compares two quantities of the same order rather than a growing one against a
negligible one. -/
theorem eventually_sqrt_le_primeMassWindow_ratio {r : ℝ}
    (hr : (Real.log 4 + 4) / Real.log 2 < r / 2) :
    ∀ᶠ y in atTop, (Real.log 2 / 2) * Real.sqrt y ≤ primeMassWindow (y / r) y := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hrpos : (0 : ℝ) < r := by
    have : (0 : ℝ) < (Real.log 4 + 4) / Real.log 2 := by positivity
    linarith
  -- the linear slack left by the ratio absorbs the logarithm
  set slack : ℝ := Real.log 2 / 2 - (Real.log 4 + 4) / r with hslack
  have hslackpos : 0 < slack := by
    rw [hslack]
    rw [div_lt_div_iff₀ hlog2 (by linarith)] at hr
    rw [sub_pos, div_lt_div_iff₀ hrpos (by norm_num)]
    nlinarith [hr]
  have hO : (fun y : ℝ => y + 2) =O[atTop] (fun y : ℝ => y) := by
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  have hlittle : (fun y : ℝ => Real.log (y + 2)) =o[atTop] (fun y : ℝ => y) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 2 tendsto_id)).trans_isBigO hO
  have hdiv := hlittle.tendsto_div_nhds_zero
  filter_upwards [hdiv.eventually (gt_mem_nhds (show (0 : ℝ) < slack / 2 by positivity)),
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (2 * (Real.log 2 + 1) / slack + 1)] with y h1 hy1 hy2
  have hypos : (0 : ℝ) < y := by linarith
  have hlogsmall : Real.log (y + 2) < slack / 2 * y := by
    rw [div_lt_iff₀ hypos] at h1
    linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hr8 : 8 < r := by
    have h := hslackpos
    rw [hslack, sub_pos, div_lt_div_iff₀ hrpos (by norm_num)] at h
    nlinarith [hlog4, hlog2le, hrpos]
  have hxnn : (0 : ℝ) ≤ y / r := by positivity
  have hxy : y / r ≤ y := by
    rw [div_le_iff₀ hrpos]
    nlinarith [hr8, hypos]
  refine sqrt_le_primeMassWindow_of_wide hxnn hxy hy1 ?_
  have hcheb : (Real.log 4 + 4) * (y / r) = (Real.log 4 + 4) / r * y := by ring
  have hslackid : (Real.log 4 + 4) / r = Real.log 2 / 2 - slack := by
    rw [hslack]; ring
  rw [hcheb, hslackid]
  have hslack_y : 2 * (Real.log 2 + 1) ≤ slack * y := by
    have hstep : 2 * (Real.log 2 + 1) / slack ≤ y := by linarith
    rw [div_le_iff₀ hslackpos] at hstep
    nlinarith [hstep, hslackpos]
  nlinarith [hlogsmall, hslack_y, hslackpos]

end RHTower
