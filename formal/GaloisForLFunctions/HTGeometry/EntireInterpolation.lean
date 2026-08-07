import Mathlib

/-!
# Interpolation by entire functions at a discrete set of simple zeros

Let `F` be entire with simple zeros `w i`, all nonzero and escaping to infinity, and let `c i` be
arbitrary target values.  There is an entire function taking the value `c i` at `w i`.

The interpolant is the Mittag-Leffler series

```text
b z = sum over i of  c i * (z / w i) ^ N i * dslope F (w i) z / deriv F (w i),
```

whose `i`-th term is entire, vanishes at every node other than `w i`, and equals `c i` at `w i`.
The convergence exponents `N i` are chosen index by index so that the `i`-th term is dominated by a
summable majorant on the disc of radius `‖w i‖ / 2`.  On a fixed disc that domination holds for all
but finitely many `i`, so the series converges locally uniformly and its sum is entire.

* `exists_entire_interpolation` — the interpolation theorem.
-/

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Interpolation at the simple zeros of an entire function.**  Arbitrary values may be
prescribed at a family of simple zeros escaping to infinity. -/
theorem exists_entire_interpolation {ι : Type*} [Countable ι] {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) {w : ι → ℂ} (hw0 : ∀ i, w i ≠ 0) (hFw : ∀ i, F (w i) = 0)
    (hFw' : ∀ i, deriv F (w i) ≠ 0) (hinj : Function.Injective w)
    (hesc : Tendsto (fun i => ‖w i‖) cofinite atTop) (c : ι → ℂ) :
    ∃ b : ℂ → ℂ, Differentiable ℂ b ∧ ∀ i, b (w i) = c i := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  set u : ι → ℝ := fun i => (1 / 2 : ℝ) ^ e i with hu_def
  have hu : Summable u :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective he
  have hu_pos : ∀ i, 0 < u i := fun i => by positivity
  have hwpos : ∀ i, 0 < ‖w i‖ := fun i => norm_pos_iff.mpr (hw0 i)
  -- a bound for `F` on the disc of radius `‖w i‖ / 2`
  have hMex : ∀ i : ι, ∃ M : ℝ, 0 < M ∧ ∀ z : ℂ, ‖z‖ ≤ ‖w i‖ / 2 → ‖F z‖ ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (‖w i‖ / 2)).exists_bound_of_continuousOn
      hF.continuous.continuousOn
    refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun z hz => ?_⟩
    exact (hM z (mem_closedBall_zero_iff.mpr hz)).trans (le_max_left _ _)
  choose M hMpos hMbound using hMex
  set A : ι → ℝ := fun i => ‖c i‖ * (M i / (‖w i‖ / 2) / ‖deriv F (w i)‖) with hA_def
  have hAnonneg : ∀ i, 0 ≤ A i := by
    intro i
    have := (hMpos i).le
    have := (hwpos i).le
    positivity
  -- the convergence exponents
  have hNex : ∀ i : ι, ∃ N : ℕ, A i * (1 / 2 : ℝ) ^ N ≤ u i := by
    intro i
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < u i / (A i + 1) by have := hu_pos i; have := hAnonneg i; positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨N, ?_⟩
    have h1 : A i * (1 / 2 : ℝ) ^ N ≤ A i * (u i / (A i + 1)) :=
      mul_le_mul_of_nonneg_left hN.le (hAnonneg i)
    refine h1.trans ?_
    rw [mul_div_assoc', div_le_iff₀ (by have := hAnonneg i; positivity)]
    nlinarith [hu_pos i, hAnonneg i]
  choose N hNbound using hNex
  set T : ι → ℂ → ℂ := fun i z => c i * (z / w i) ^ N i * (dslope F (w i) z / deriv F (w i))
    with hT_def
  have hdslope : ∀ i, Differentiable ℂ (dslope F (w i)) := by
    intro i
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hF.differentiableOn
  have hTdiff : ∀ i, Differentiable ℂ (T i) := by
    intro i
    exact ((differentiable_const _).mul ((differentiable_id.div_const _).pow _)).mul
      ((hdslope i).div_const _)
  -- the term bound on the disc of radius `‖w i‖ / 2`
  have hbound : ∀ i, ∀ z : ℂ, ‖z‖ ≤ ‖w i‖ / 2 → ‖T i z‖ ≤ u i := by
    intro i z hz
    have hzne : z ≠ w i := by
      intro h
      rw [h] at hz
      linarith [hwpos i]
    have h1 : ‖(z / w i) ^ N i‖ ≤ (1 / 2 : ℝ) ^ N i := by
      rw [norm_pow, norm_div]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_le_div_iff₀ (hwpos i) (by norm_num : (0:ℝ) < 2)]
      linarith
    have hden : ‖w i‖ / 2 ≤ ‖z - w i‖ := by
      have h := norm_sub_norm_le (w i) z
      rw [norm_sub_rev] at h
      linarith
    have h2 : ‖dslope F (w i) z‖ ≤ M i / (‖w i‖ / 2) := by
      rw [dslope_of_ne _ hzne, slope_def_field, hFw i, sub_zero, norm_div]
      have hhalf : (0:ℝ) < ‖w i‖ / 2 := by linarith [hwpos i]
      rw [div_le_div_iff₀ (lt_of_lt_of_le hhalf hden) hhalf]
      nlinarith [hMbound i z hz, norm_nonneg (F z), (hMpos i).le, (hwpos i).le]
    have hnorm : ‖T i z‖
        = ‖c i‖ * ‖(z / w i) ^ N i‖ * (‖dslope F (w i) z‖ / ‖deriv F (w i)‖) := by
      simp [hT_def]
    refine le_trans (le_of_eq hnorm) (le_trans ?_ (hNbound i))
    have hrw : A i * (1 / 2 : ℝ) ^ N i
        = ‖c i‖ * (1 / 2 : ℝ) ^ N i * (M i / (‖w i‖ / 2) / ‖deriv F (w i)‖) := by
      rw [hA_def]; ring
    rw [hrw]
    gcongr
  -- cofinite domination on every closed disc
  have hcof : ∀ R : ℝ, ∀ᶠ i in cofinite, ∀ z ∈ closedBall (0 : ℂ) R, ‖T i z‖ ≤ u i := by
    intro R
    filter_upwards [hesc.eventually_ge_atTop (2 * R)] with i hi z hz
    exact hbound i z ((mem_closedBall_zero_iff.mp hz).trans (by linarith))
  refine ⟨fun z => ∑' i, T i z, ?_, ?_⟩
  · intro z
    have hmem : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by
      rw [mem_ball_zero_iff]; linarith
    have huc := tendstoUniformlyOn_tsum_of_cofinite_eventually hu (hcof (‖z‖ + 1))
    have hloc : TendstoLocallyUniformlyOn (fun t : Finset ι => fun z => ∑ i ∈ t, T i z)
        (fun z => ∑' i, T i z) atTop (ball (0 : ℂ) (‖z‖ + 1)) :=
      ((huc.mono ball_subset_closedBall)).tendstoLocallyUniformlyOn
    have hd : DifferentiableOn ℂ (fun z => ∑' i, T i z) (ball (0 : ℂ) (‖z‖ + 1)) :=
      hloc.differentiableOn
        (by filter_upwards with t
            exact (Differentiable.fun_sum fun i _ => hTdiff i).differentiableOn)
        isOpen_ball
    exact hd.differentiableAt (isOpen_ball.mem_nhds hmem)
  · intro j
    show ∑' i, T i (w j) = c j
    rw [tsum_eq_single j]
    · rw [hT_def]
      simp [div_self (hw0 j), dslope_same, div_self (hFw' j)]
    · intro i hij
      have hne : w i ≠ w j := fun h => hij (hinj h)
      rw [hT_def]
      simp [dslope_of_ne _ hne.symm, slope_def_field, hFw i, hFw j]
