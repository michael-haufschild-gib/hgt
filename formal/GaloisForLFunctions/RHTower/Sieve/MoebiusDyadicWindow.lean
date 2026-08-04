import GaloisForLFunctions.RHTower.Sieve.MoebiusSharpLittleO

/-!
# The Möbius sum over a dyadic window

The summatory function is `o(N)`, so a difference of two of them at comparable scales is `o` of the
scale:

    (1/y) ∑_{y < n ≤ 2y} μ(n) → 0.

This is the input the bilinear all-interval theorem is applied to: the mean of `μ` over the dyadic
block `[√x, 2√x]` vanishes, which is what makes the signed balanced-pair sum `o(h√x)`.
-/

namespace RHTower.Sieve

open ArithmeticFunction Filter Topology

/-- A half-open block is a difference of two initial segments. -/
theorem Ico_succ_succ_eq_Ioc (a b : ℕ) : Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
  ext n
  simp [Finset.mem_Ico, Finset.mem_Ioc]

/-- **The Möbius sum over a dyadic window is `o(y)`.** -/
theorem tendsto_norm_window_sum_moebius_div :
    Tendsto (fun y : ℝ =>
        ‖(∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ))
          - ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (moebius n : ℂ)‖ / y)
      atTop (𝓝 0) := by
  have hbase := tendsto_norm_sum_moebius_div
  have hdouble : Tendsto (fun y : ℝ => 2 * y) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hupper : Tendsto (fun y : ℝ =>
      2 * (‖∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ)‖ / (2 * y))
        + ‖∑ n ∈ Finset.range (⌊y⌋₊ + 1), (moebius n : ℂ)‖ / y) atTop (𝓝 0) := by
    have h1 := (hbase.comp hdouble).const_mul (2 : ℝ)
    simp only [Function.comp_apply, mul_zero] at h1
    have h2 := h1.add hbase
    simpa using h2
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have h2y : (0 : ℝ) < 2 * y := by linarith
    have htri : ‖(∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ))
          - ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (moebius n : ℂ)‖
        ≤ ‖∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ)‖
          + ‖∑ n ∈ Finset.range (⌊y⌋₊ + 1), (moebius n : ℂ)‖ := norm_sub_le _ _
    have hrw : 2 * (‖∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ)‖ / (2 * y))
        = ‖∑ n ∈ Finset.range (⌊2 * y⌋₊ + 1), (moebius n : ℂ)‖ / y := by
      field_simp
    rw [hrw, ← add_div]
    gcongr

/-- The same statement with the window written as an interval. -/
theorem tendsto_norm_sum_moebius_Ioc_div :
    Tendsto (fun y : ℝ => ‖∑ n ∈ Finset.Ioc (⌊y⌋₊) (⌊2 * y⌋₊), (moebius n : ℂ)‖ / y)
      atTop (𝓝 0) := by
  refine tendsto_norm_window_sum_moebius_div.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  have hle : ⌊y⌋₊ + 1 ≤ ⌊2 * y⌋₊ + 1 := by
    have : ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := Nat.floor_le_floor (by linarith)
    omega
  have hsub := Finset.sum_Ico_eq_sub (fun n : ℕ => (moebius n : ℂ)) hle
  rw [Ico_succ_succ_eq_Ioc] at hsub
  rw [hsub]

end RHTower.Sieve
