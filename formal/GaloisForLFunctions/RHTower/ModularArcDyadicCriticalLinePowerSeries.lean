import GaloisForLFunctions.RHTower.ModularArcDyadicLogarithmicMomentHierarchy

/-!
# All-Orders Critical-Line Taylor Polynomial Hierarchy & Real-Analytic Power-Series Convergence

This module establishes the all-orders Taylor polynomial hierarchy, global multi-moment
coercivity across the entire open critical strip `|l| < 1/2`, scale-independent geometric
`O((8|l|)^N / (1/8 − |l|))` Taylor remainder bounds, and unconditional real-analytic
power-series convergence on `|l| < 1/8` for the strip-weighted Hilbert energy
`E_k(l) = ∫_{x > 0} x^{2l} (V_k(x))² dx`, the origin–infinity energy imbalance
`Δ_k(l) = ∫_{x > 1} x^{2l} (V_k(x))² dx − ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx`, and the
one-sided sector energies `E_k^{(1, ∞)}(l)` and `E_k^{(0, 1]}(l)` of the infinite-horizon
dyadic line-model vector `V_k = arcLineInfiniteDyadicVector k ν`.

## Main Results

1. **Elementary Exponential & Hyperbolic Taylor Remainder Inequalities:**
   - `exp_sub_sum_range_le_factorial_tail_nonneg` & `abs_exp_sub_sum_range_le_factorial_tail`:
     for all `u ∈ ℝ` and `N ∈ ℕ`,
     `|exp u − ∑_{n < N} u^n / n!| ≤ exp |u| − ∑_{n < N} |u|^n / n! ≤ (|u|^N / N!) · exp |u|`.
   - `sum_range_even_pow_div_factorial_le_cosh` & `cosh_sub_sum_range_even_pow_div_factorial_le`:
     for all `u ∈ ℝ` and `M ∈ ℕ`,
     `0 ≤ cosh u − ∑_{m < M} u^{2m} / (2m)! ≤ (u^{2M} / (2M)!) · exp |u|`.
   - `sum_range_odd_abs_pow_div_factorial_le_abs_sinh` &
     `abs_sinh_sub_sum_range_odd_pow_div_factorial_le`:
     for all `u ∈ ℝ` and `M ∈ ℕ`,
     `∑_{m < M} |u|^{2m+1} / (2m+1)! ≤ |sinh u|` and
     `|sinh u − ∑_{m < M} u^{2m+1} / (2m+1)!| ≤ (|u|^{2M+1} / (2M+1)!) · exp |u|`.
   - `two_mul_abs_pow_div_factorial_le_eight_pow_mul_exp_quarter`:
     factorial-to-geometric absorption `(2|l| |v|)^N / N! ≤ (8|l|)^N · exp(|v|/4)`.

2. **One-Sided Sector Taylor Polynomials & Power Series on `(1, ∞)` and `(0, 1]`:**
   - `sum_range_pow_div_factorial_mul_moment_le_setIntegral_Ioi_one`:
     global monotone Taylor lower bound on `l ∈ [0, 1/2)`.
   - `abs_setIntegral_Ioi_one_rpow_two_mul_sq_sub_sum_range_le` &
     `abs_setIntegral_Ioc_zero_one_rpow_two_mul_sq_sub_sum_range_le`:
     scale-independent geometric `O((8|l|)^N / (1/8 − |l|))` Taylor remainder bounds on `|l| < 1/8`.
   - `tendsto_sum_range_pow_div_factorial_mul_moment_Ioi_one_atTop` &
     `tendsto_sum_range_neg_pow_div_factorial_mul_moment_Ioc_zero_one_atTop`:
     unconditional `N → ∞` power-series convergence on `|l| < 1/8`.

3. **All-Orders Even Taylor Hierarchy & Power Series for the Full Strip-Weighted Hilbert Energy `E_k(l)`:**
   - `sum_range_even_pow_div_factorial_mul_moment_le_setIntegral_Ioi` &
     `sum_range_even_pow_succ_div_factorial_mul_moment_le_excess`:
     global multi-moment coercivity across the entire open critical strip `|l| < 1/2`.
   - `sum_range_even_pow_div_factorial_mul_moment_strictMono`:
     strict monotonicity in the truncation order `M` for `l ≠ 0`.
   - `setIntegral_Ioi_rpow_two_mul_sq_sub_sum_range_even_le` &
     `tendsto_sum_range_even_pow_div_factorial_mul_moment_atTop`:
     scale-independent `O((8|l|)^{2M} / (1/8 − |l|))` remainder and `M → ∞` power-series
     convergence on `|l| < 1/8`.

4. **All-Orders Odd Taylor Hierarchy & Power Series for the Origin–Infinity Imbalance `Δ_k(l)`:**
   - `sum_range_odd_abs_pow_div_factorial_mul_moment_le_abs_imbalance`:
     global multi-moment lower bound across `|l| < 1/2`.
   - `abs_imbalance_sub_two_mul_sum_range_odd_le` &
     `tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_moment_atTop`:
     scale-independent `O((8|l|)^{2M+1} / (1/8 − |l|))` remainder and `M → ∞` power-series
     convergence on `|l| < 1/8`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

/-! ## Section 1: Elementary Exponential & Hyperbolic Taylor Remainder Inequalities -/

/-- **Non-negative exponential Taylor partial-sum lower bound:**
For every `N ∈ ℕ` and `u ≥ 0`, `∑_{n < N} u^n / n! ≤ exp u`. -/
theorem sum_range_pow_div_factorial_le_exp_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∑ n ∈ Finset.range N, u ^ n / (n.factorial : ℝ) ≤ Real.exp u :=
  Real.sum_le_exp_of_nonneg hu N

/-- **Non-negative exponential factorial Taylor remainder bound:**
For every `N ∈ ℕ` and `u ≥ 0`,
`exp u − ∑_{n < N} u^n / n! ≤ (u^N / N!) · exp u`. -/
theorem exp_sub_sum_range_le_factorial_tail_nonneg (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp u - ∑ n ∈ Finset.range N, u ^ n / (n.factorial : ℝ) ≤
      (u ^ N / (N.factorial : ℝ)) * Real.exp u := by
  have hs : Summable (fun m : ℕ => u ^ m / (m.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable u
  have hsum : (∑' m : ℕ, u ^ m / (m.factorial : ℝ)) = Real.exp u := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp u).tsum_eq
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : Real.exp u - ∑ m ∈ Finset.range N, u ^ m / (m.factorial : ℝ) =
      ∑' j : ℕ, u ^ (j + N) / ((j + N).factorial : ℝ) := by
    rw [← hsum]; linarith
  rw [htail]
  have hfac (j : ℕ) :
      (N.factorial : ℝ) * j.factorial ≤ (j + N).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _) <|
      (Nat.factorial_mul_factorial_dvd_factorial_add N j) |>.trans (by rw [Nat.add_comm])
  have hterm (j : ℕ) :
      u ^ (j + N) / ((j + N).factorial : ℝ) ≤
        (u ^ N / (N.factorial : ℝ)) * (u ^ j / (j.factorial : ℝ)) := by
    have hnum : u ^ (j + N) = u ^ N * u ^ j := by rw [Nat.add_comm, pow_add]
    rw [hnum]
    have hden : (0 : ℝ) < (N.factorial : ℝ) * j.factorial := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hinv : (((j + N).factorial : ℝ))⁻¹ ≤ (((N.factorial : ℝ) * j.factorial))⁻¹ :=
      inv_anti₀ hden (hfac j)
    calc u ^ N * u ^ j * (((j + N).factorial : ℝ))⁻¹
        ≤ u ^ N * u ^ j * (((N.factorial : ℝ) * j.factorial))⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (u ^ N * (N.factorial : ℝ)⁻¹) * (u ^ j * (j.factorial : ℝ)⁻¹) := by
          rw [mul_inv_rev]; ring
  calc (∑' j : ℕ, u ^ (j + N) / ((j + N).factorial : ℝ))
      ≤ ∑' j : ℕ, (u ^ N / (N.factorial : ℝ)) * (u ^ j / (j.factorial : ℝ)) :=
        ((summable_nat_add_iff N).2 hs).tsum_le_tsum hterm (hs.mul_left _)
    _ = (u ^ N / (N.factorial : ℝ)) * ∑' j : ℕ, u ^ j / (j.factorial : ℝ) := by
        rw [tsum_mul_left]
    _ = (u ^ N / (N.factorial : ℝ)) * Real.exp u := by rw [hsum]

/-- **Modulus domination for the real exponential Taylor remainder:**
For every `N ∈ ℕ` and `u ∈ ℝ`,
`|exp u − ∑_{n < N} u^n / n!| ≤ exp |u| − ∑_{n < N} |u|^n / n!`. -/
theorem abs_exp_sub_sum_range_le_exp_abs_sub_sum (N : ℕ) (u : ℝ) :
    |Real.exp u - ∑ n ∈ Finset.range N, u ^ n / (n.factorial : ℝ)| ≤
      Real.exp |u| - ∑ n ∈ Finset.range N, |u| ^ n / (n.factorial : ℝ) := by
  have hs : Summable (fun m : ℕ => u ^ m / (m.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable u
  have hsum : (∑' m : ℕ, u ^ m / (m.factorial : ℝ)) = Real.exp u := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp u).tsum_eq
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : Real.exp u - ∑ m ∈ Finset.range N, u ^ m / (m.factorial : ℝ) =
      ∑' j : ℕ, u ^ (j + N) / ((j + N).factorial : ℝ) := by
    rw [← hsum]; linarith
  have hs_abs : Summable (fun m : ℕ => |u| ^ m / (m.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable |u|
  have hsum_abs : (∑' m : ℕ, |u| ^ m / (m.factorial : ℝ)) = Real.exp |u| := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp |u|).tsum_eq
  have hsplit_abs := hs_abs.sum_add_tsum_nat_add N
  have htail_abs : Real.exp |u| - ∑ m ∈ Finset.range N, |u| ^ m / (m.factorial : ℝ) =
      ∑' j : ℕ, |u| ^ (j + N) / ((j + N).factorial : ℝ) := by
    rw [← hsum_abs]; linarith
  rw [htail, htail_abs, ← Real.norm_eq_abs]
  have hnorm_eq : ∀ j : ℕ,
      ‖u ^ (j + N) / ((j + N).factorial : ℝ)‖ = |u| ^ (j + N) / ((j + N).factorial : ℝ) := by
    intro j
    have hfac0 : (0 : ℝ) ≤ ((j + N).factorial : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg hfac0]
  have hnorm_sum : Summable (fun j : ℕ => ‖u ^ (j + N) / ((j + N).factorial : ℝ)‖) :=
    ((summable_nat_add_iff N).2 hs_abs).congr (fun j => (hnorm_eq j).symm)
  exact (norm_tsum_le_tsum_norm hnorm_sum).trans_eq (tsum_congr hnorm_eq)

/-- **Two-sided factorial Taylor remainder bound for `Real.exp`:**
For every `N ∈ ℕ` and `u ∈ ℝ`,
`|exp u − ∑_{n < N} u^n / n!| ≤ (|u|^N / N!) · exp |u|`. -/
theorem abs_exp_sub_sum_range_le_factorial_tail (N : ℕ) (u : ℝ) :
    |Real.exp u - ∑ n ∈ Finset.range N, u ^ n / (n.factorial : ℝ)| ≤
      (|u| ^ N / (N.factorial : ℝ)) * Real.exp |u| :=
  (abs_exp_sub_sum_range_le_exp_abs_sub_sum N u).trans
    (exp_sub_sum_range_le_factorial_tail_nonneg N (abs_nonneg u))

private theorem neg_pow_two_mul (k : ℕ) (u : ℝ) : (-u) ^ (2 * k) = u ^ (2 * k) := by
  rw [pow_mul, pow_mul, neg_sq]

private theorem neg_pow_two_mul_add_one (k : ℕ) (u : ℝ) :
    (-u) ^ (2 * k + 1) = -(u ^ (2 * k + 1)) := by
  rw [pow_succ, neg_pow_two_mul, mul_neg, ← pow_succ]

/-- **Even Taylor partial-sum symmetrization identity:**
`∑_{m < M} u^{2m} / (2m)! = ∑_{n < 2M} (u^n + (−u)^n) / (2 · n!)`. -/
theorem sum_range_even_pow_div_factorial_eq (M : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range M, u ^ (2 * m) / ((2 * m).factorial : ℝ) =
      ∑ n ∈ Finset.range (2 * M), (u ^ n + (-u) ^ n) / (2 * (n.factorial : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [neg_pow_two_mul M u, neg_pow_two_mul_add_one M u]
    ring

/-- **Odd Taylor partial-sum antisymmetrization identity:**
`∑_{m < M} u^{2m+1} / (2m+1)! = ∑_{n < 2M+1} (u^n − (−u)^n) / (2 · n!)`. -/
theorem sum_range_odd_pow_div_factorial_eq (M : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range M, u ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) =
      ∑ n ∈ Finset.range (2 * M + 1), (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2M : 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 := by omega
    rw [Finset.sum_range_succ, ih, h2M]
    nth_rw 2 [Finset.sum_range_succ]
    nth_rw 2 [Finset.sum_range_succ]
    have h1 : 2 * M + 1 + 1 = 2 * (M + 1) := by omega
    rw [h1, neg_pow_two_mul (M + 1) u, neg_pow_two_mul_add_one M u]
    ring

/-- **Global even Taylor partial-sum lower bound for `Real.cosh`:**
For every `M ∈ ℕ` and `u ∈ ℝ`,
`∑_{m < M} u^{2m} / (2m)! ≤ cosh u`. -/
theorem sum_range_even_pow_div_factorial_le_cosh (M : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range M, u ^ (2 * m) / ((2 * m).factorial : ℝ) ≤ Real.cosh u := by
  have hev_u : ∀ m : ℕ, u ^ (2 * m) = |u| ^ (2 * m) := by
    intro m; rw [pow_mul, pow_mul, sq_abs]
  have hsum_eq : ∑ m ∈ Finset.range M, u ^ (2 * m) / ((2 * m).factorial : ℝ) =
      ∑ m ∈ Finset.range M, |u| ^ (2 * m) / ((2 * m).factorial : ℝ) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hev_u m]
  rw [hsum_eq, ← Real.cosh_abs u]
  rw [sum_range_even_pow_div_factorial_eq]
  have htsum1 : (∑' n : ℕ, |u| ^ n / (n.factorial : ℝ)) = Real.exp |u| := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp |u|).tsum_eq
  have htsum2 : (∑' n : ℕ, (-|u|) ^ n / (n.factorial : ℝ)) = Real.exp (-|u|) := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (-|u|)).tsum_eq
  have hs1 : Summable (fun n : ℕ => |u| ^ n / (n.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable |u|
  have hs2 : Summable (fun n : ℕ => (-|u|) ^ n / (n.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable (-|u|)
  have hs : Summable (fun n : ℕ => (|u| ^ n + (-|u|) ^ n) / (2 * (n.factorial : ℝ))) := by
    refine ((hs1.add hs2).mul_right (1 / 2)).congr (fun n => ?_)
    ring
  have hnonneg : ∀ n : ℕ, 0 ≤ (|u| ^ n + (-|u|) ^ n) / (2 * (n.factorial : ℝ)) := by
    intro n
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [neg_pow_two_mul]; positivity
    · rw [neg_pow_two_mul_add_one, add_neg_cancel, zero_div]
  calc ∑ n ∈ Finset.range (2 * M), (|u| ^ n + (-|u|) ^ n) / (2 * (n.factorial : ℝ))
      ≤ ∑' n : ℕ, (|u| ^ n + (-|u|) ^ n) / (2 * (n.factorial : ℝ)) :=
        hs.sum_le_tsum (Finset.range (2 * M)) (fun n _ => hnonneg n)
    _ = ∑' n : ℕ, (|u| ^ n / (n.factorial : ℝ) + (-|u|) ^ n / (n.factorial : ℝ)) * (1 / 2) := by
        refine tsum_congr (fun n => by ring)
    _ = ((∑' n : ℕ, |u| ^ n / (n.factorial : ℝ)) + (∑' n : ℕ, (-|u|) ^ n / (n.factorial : ℝ))) * (1 / 2) := by
        rw [tsum_mul_right, hs1.tsum_add hs2]
    _ = Real.cosh |u| := by
        rw [htsum1, htsum2, Real.cosh_eq]
        ring

/-- **Factorial Taylor remainder bound for `Real.cosh`:**
For every `M ∈ ℕ` and `u ∈ ℝ`,
`cosh u − ∑_{m < M} u^{2m} / (2m)! ≤ (u^{2M} / (2M)!) · exp |u|`. -/
theorem cosh_sub_sum_range_even_pow_div_factorial_le (M : ℕ) (u : ℝ) :
    Real.cosh u - ∑ m ∈ Finset.range M, u ^ (2 * m) / ((2 * m).factorial : ℝ) ≤
      (u ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp |u| := by
  rw [sum_range_even_pow_div_factorial_eq, Real.cosh_eq]
  have hsum_split :
      ∑ n ∈ Finset.range (2 * M), (u ^ n + (-u) ^ n) / (2 * (n.factorial : ℝ)) =
        (∑ n ∈ Finset.range (2 * M), u ^ n / (n.factorial : ℝ)) / 2 +
          (∑ n ∈ Finset.range (2 * M), (-u) ^ n / (n.factorial : ℝ)) / 2 := by
    rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  rw [hsum_split]
  have h1 := le_of_abs_le (abs_exp_sub_sum_range_le_factorial_tail (2 * M) u)
  have h2 := le_of_abs_le (abs_exp_sub_sum_range_le_factorial_tail (2 * M) (-u))
  rw [abs_neg] at h2
  have hev : |u| ^ (2 * M) = u ^ (2 * M) := by rw [pow_mul, pow_mul, sq_abs]
  rw [hev] at h1 h2
  linarith

/-- **Odd Taylor partial-sum lower bound for `Real.sinh` on `u ≥ 0`:**
For every `M ∈ ℕ` and `u ≥ 0`,
`∑_{m < M} u^{2m+1} / (2m+1)! ≤ sinh u`. -/
theorem sum_range_odd_pow_div_factorial_le_sinh_nonneg (M : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∑ m ∈ Finset.range M, u ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤ Real.sinh u := by
  rw [sum_range_odd_pow_div_factorial_eq]
  have htsum1 : (∑' n : ℕ, u ^ n / (n.factorial : ℝ)) = Real.exp u := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp u).tsum_eq
  have htsum2 : (∑' n : ℕ, (-u) ^ n / (n.factorial : ℝ)) = Real.exp (-u) := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (-u)).tsum_eq
  have hs1 : Summable (fun n : ℕ => u ^ n / (n.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable u
  have hs2 : Summable (fun n : ℕ => (-u) ^ n / (n.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable (-u)
  have hs : Summable (fun n : ℕ => (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ))) := by
    refine ((hs1.sub hs2).mul_right (1 / 2)).congr (fun n => ?_)
    ring
  have hnonneg : ∀ n : ℕ, 0 ≤ (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ)) := by
    intro n
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [neg_pow_two_mul, sub_self, zero_div]
    · rw [neg_pow_two_mul_add_one, sub_neg_eq_add]; positivity
  calc ∑ n ∈ Finset.range (2 * M + 1), (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ))
      ≤ ∑' n : ℕ, (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ)) :=
        hs.sum_le_tsum (Finset.range (2 * M + 1)) (fun n _ => hnonneg n)
    _ = ∑' n : ℕ, (u ^ n / (n.factorial : ℝ) - (-u) ^ n / (n.factorial : ℝ)) * (1 / 2) := by
        refine tsum_congr (fun n => by ring)
    _ = ((∑' n : ℕ, u ^ n / (n.factorial : ℝ)) - (∑' n : ℕ, (-u) ^ n / (n.factorial : ℝ))) * (1 / 2) := by
        rw [tsum_mul_right, hs1.tsum_sub hs2]
    _ = Real.sinh u := by
        rw [htsum1, htsum2, Real.sinh_eq]
        ring

/-- **Global odd Taylor partial-sum lower bound for `|Real.sinh u|`:**
For every `M ∈ ℕ` and `u ∈ ℝ`,
`∑_{m < M} |u|^{2m+1} / (2m+1)! ≤ |sinh u|`. -/
theorem sum_range_odd_abs_pow_div_factorial_le_abs_sinh (M : ℕ) (u : ℝ) :
    ∑ m ∈ Finset.range M, |u| ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) ≤ |Real.sinh u| := by
  rw [Real.abs_sinh]
  exact sum_range_odd_pow_div_factorial_le_sinh_nonneg M (abs_nonneg u)

/-- **Factorial Taylor remainder bound for `Real.sinh`:**
For every `M ∈ ℕ` and `u ∈ ℝ`,
`|sinh u − ∑_{m < M} u^{2m+1} / (2m+1)!| ≤ (|u|^{2M+1} / (2M+1)!) · exp |u|`. -/
theorem abs_sinh_sub_sum_range_odd_pow_div_factorial_le (M : ℕ) (u : ℝ) :
    |Real.sinh u - ∑ m ∈ Finset.range M, u ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| ≤
      (|u| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp |u| := by
  rw [sum_range_odd_pow_div_factorial_eq, Real.sinh_eq]
  have hsum_split :
      ∑ n ∈ Finset.range (2 * M + 1), (u ^ n - (-u) ^ n) / (2 * (n.factorial : ℝ)) =
        (∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2 -
          (∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2 := by
    rw [← sub_div, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  rw [hsum_split]
  have h1 := abs_exp_sub_sum_range_le_factorial_tail (2 * M + 1) u
  have h2 := abs_exp_sub_sum_range_le_factorial_tail (2 * M + 1) (-u)
  rw [abs_neg] at h2
  have hsplit :
      (Real.exp u - Real.exp (-u)) / 2 -
          ((∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2 -
            (∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2) =
        (Real.exp u - ∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2 -
          (Real.exp (-u) - ∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2 := by
    ring
  rw [hsplit]
  calc |(Real.exp u - ∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2 -
          (Real.exp (-u) - ∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2|
      ≤ |(Real.exp u - ∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2| +
          |(Real.exp (-u) - ∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2| := by
        simpa [sub_eq_add_neg] using
          abs_add_le
            ((Real.exp u - ∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)) / 2)
            (-((Real.exp (-u) - ∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)) / 2))
    _ = |Real.exp u - ∑ n ∈ Finset.range (2 * M + 1), u ^ n / (n.factorial : ℝ)| / 2 +
          |Real.exp (-u) - ∑ n ∈ Finset.range (2 * M + 1), (-u) ^ n / (n.factorial : ℝ)| / 2 := by
        rw [abs_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (|u| ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp |u| := by linarith

/-- **Factorial-to-geometric absorption inequality (`(2|l| |v|)^N / N! ≤ (8|l|)^N · exp(|v|/4)`):**
For every `N ∈ ℕ` and `l, v ∈ ℝ`, factoring `2|l| |v| = (8|l|) · (|v|/4)` and applying
`(|v|/4)^N / N! ≤ exp(|v|/4)` absorbs the factorial growth into the `exp(|v|/4)` weight and
isolates the pure geometric factor `(8|l|)^N`. -/
theorem two_mul_abs_pow_div_factorial_le_eight_pow_mul_exp_quarter (N : ℕ) (l v : ℝ) :
    (2 * |l| * |v|) ^ N / (N.factorial : ℝ) ≤
      (8 * |l|) ^ N * Real.exp ((1 / 4 : ℝ) * |v|) := by
  have h1 := pow_le_factorial_mul_exp_nonneg (by positivity : 0 ≤ (1 / 4 : ℝ) * |v|) N
  have hfac : (0 : ℝ) < N.factorial := Nat.cast_pos.mpr (Nat.factorial_pos N)
  have hdiv : ((1 / 4 : ℝ) * |v|) ^ N / (N.factorial : ℝ) ≤ Real.exp ((1 / 4 : ℝ) * |v|) :=
    (div_le_iff₀ hfac).mpr (by linarith)
  calc (2 * |l| * |v|) ^ N / (N.factorial : ℝ)
      = (8 * |l|) ^ N * (((1 / 4 : ℝ) * |v|) ^ N / (N.factorial : ℝ)) := by
        rw [← mul_div_assoc, ← mul_pow]
        congr 2
        ring
    _ ≤ (8 * |l|) ^ N * Real.exp ((1 / 4 : ℝ) * |v|) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)

/-- **Pointwise exponential-geometric Taylor remainder envelope for `Φ_k`:**
For every `k ≥ 2`, `N ∈ ℕ`, `l ∈ ℝ`, and `v ∈ ℝ`,
`((2|l| |v|)^N / N!) · exp(2|l| |v|) · (Φ_k(v))² ≤
  680625 · (ν.real univ)² · (8|l|)^N · exp(−2(1/8 − |l|)|v|)`. -/
theorem taylor_remainder_mul_sq_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (N : ℕ) (l v : ℝ) :
    ((2 * |l| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp (2 * |l| * |v|) *
        (arcLineInfiniteDyadicProfile k ν v) ^ 2 ≤
      680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ N *
        Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
  have hpow := two_mul_abs_pow_div_factorial_le_eight_pow_mul_exp_quarter N l v
  have hsq := sq_arcLineInfiniteDyadicProfile_le_exp_half_uniform hk hν v
  calc ((2 * |l| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp (2 * |l| * |v|) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2
      ≤ ((8 * |l|) ^ N * Real.exp ((1 / 4 : ℝ) * |v|)) * Real.exp (2 * |l| * |v|) *
          (680625 * (ν.real univ) ^ 2 * Real.exp (-((1 / 2 : ℝ) * |v|))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)) hsq
          (sq_nonneg _) (by positivity)
    _ = 680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ N *
          (Real.exp ((1 / 4 : ℝ) * |v|) * Real.exp (2 * |l| * |v|) *
            Real.exp (-((1 / 2 : ℝ) * |v|))) := by ring
    _ = 680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ N *
          Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
        congr 1
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring


/-! ## Section 2: One-Sided Sector Taylor Polynomials & Power Series on `(1, ∞)` and `(0, 1]` -/

/-- **Half-line integral linearity for the `N`-term exponential Taylor polynomial:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l ∈ ℝ`, and `N ∈ ℕ`,
`∫_{v > 0} (∑_{n < N} (2lv)^n / n!) (Φ_k(v))² dv =
  ∑_{n < N} ((2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_zero_sum_range_pow_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l : ℝ) (N : ℕ) :
    (∫ v in Ioi (0 : ℝ),
        (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∑ n ∈ Finset.range N,
        ((2 * l) ^ n / (n.factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  have hfun :
      (fun v : ℝ =>
        (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => ∑ n ∈ Finset.range N,
        ((2 * l) ^ n / (n.factorial : ℝ)) *
          (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ext v
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mul_pow]
    ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    exact integral_const_mul _ _
  · intro n _
    exact (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).const_mul _

/-- **Global monotone Taylor lower bound for the infinity-sector energy `E_k^{(1, ∞)}(l)` on `l ∈ [0, 1/2)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l ∈ [0, 1/2)`, and `N ∈ ℕ`,
`∑_{n < N} ((2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv ≤ ∫_{x > 1} x^{2l} (V_k(x))² dx`. -/
theorem sum_range_pow_div_factorial_mul_moment_le_setIntegral_Ioi_one
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) (N : ℕ) :
    ∑ n ∈ Finset.range N,
        ((2 * l) ^ n / (n.factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      ∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl_abs : |l| < 1 / 2 := by rwa [abs_of_nonneg hl0]
  rw [setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    ← setIntegral_Ioi_zero_sum_range_pow_mul_sq_eq hk hν l N]
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ n ∈ Finset.range N,
          ((2 * l) ^ n / (n.factorial : ℝ)) *
            (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun n _ =>
      (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).const_mul _)
  have hInt_exp : IntegrableOn
      (fun v : ℝ => Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_abs).integrableOn
  refine setIntegral_mono_on hInt_sum hInt_exp measurableSet_Ioi (fun v hv => ?_)
  have hv0 : 0 ≤ v := le_of_lt hv
  exact mul_le_mul_of_nonneg_right
    (sum_range_pow_div_factorial_le_exp_nonneg N (by positivity : 0 ≤ 2 * l * v))
    (sq_nonneg _)

/-- **Scale-independent geometric `O((8|l|)^N / (1/8 − |l|))` Taylor remainder bound for `E_k^{(1, ∞)}(l)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/8`, and `N ∈ ℕ`,
`|∫_{x > 1} x^{2l} (V_k(x))² dx − ∑_{n < N} ((2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv| ≤
  (680625 · (ν.real univ)² / (1/8 − |l|)) · (8|l|)^N`. -/
theorem abs_setIntegral_Ioi_one_rpow_two_mul_sq_sub_sum_range_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (N : ℕ) :
    |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∑ n ∈ Finset.range N,
          ((2 * l) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
      (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ N := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 2 * (1 / 8 - |l|) := by linarith
  rw [setIntegral_Ioi_one_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    ← setIntegral_Ioi_zero_sum_range_pow_mul_sq_eq hk hν l N]
  have hInt_exp : IntegrableOn
      (fun v : ℝ => Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_half).integrableOn
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ n ∈ Finset.range N,
          ((2 * l) ^ n / (n.factorial : ℝ)) *
            (v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun n _ =>
      (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν n).const_mul _)
  rw [← integral_sub hInt_exp hInt_sum]
  set B := 680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ N
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
        (∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2)
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) =
          (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ N := by
      have hne : 1 / 8 - |l| ≠ 0 := by linarith
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; field_simp
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · rw [Real.norm_eq_abs, ← sub_mul, abs_mul,
      abs_of_nonneg (sq_nonneg (arcLineInfiniteDyadicProfile k ν v))]
    have habs_u : |2 * l * v| = 2 * |l| * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrem := abs_exp_sub_sum_range_le_factorial_tail N (2 * l * v)
    rw [habs_u] at hrem
    calc |Real.exp (2 * l * v) - ∑ n ∈ Finset.range N, (2 * l * v) ^ n / (n.factorial : ℝ)| *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2
        ≤ ((2 * |l| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp (2 * |l| * |v|) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
          mul_le_mul_of_nonneg_right hrem (sq_nonneg _)
      _ ≤ B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) :=
          taylor_remainder_mul_sq_arcLineInfiniteDyadicProfile_le hk hν N l v

/-- **Scale-independent geometric `O((8|l|)^N / (1/8 − |l|))` Taylor remainder bound for `E_k^{(0, 1]}(l)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/8`, and `N ∈ ℕ`,
`|∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx − ∑_{n < N} ((−2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv| ≤
  (680625 · (ν.real univ)² / (1/8 − |l|)) · (8|l|)^N`. -/
theorem abs_setIntegral_Ioc_zero_one_rpow_two_mul_sq_sub_sum_range_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (N : ℕ) :
    |(∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∑ n ∈ Finset.range N,
          ((-2 * l) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
      (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ N := by
  have hk1 : 1 ≤ k := by omega
  have hl_neg : |-l| < 1 / 8 := by rwa [abs_neg]
  have h1 := abs_setIntegral_Ioi_one_rpow_two_mul_sq_sub_sum_range_le hk hν hl_neg N
  rw [abs_neg] at h1
  rw [setIntegral_Ioc_zero_one_rpow_two_mul_sq_eq_setIntegral_Ioi_one_neg hk1 ν l]
  have hsum :
      ∑ n ∈ Finset.range N,
          ((-2 * l) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        ∑ n ∈ Finset.range N,
          ((2 * (-l)) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show -2 * l = 2 * (-l) by ring]
  rw [hsum]
  exact h1

/-- **Unconditional `N → ∞` real-analytic power-series convergence for `E_k^{(1, ∞)}(l)` on `|l| < 1/8`:**
For every `k ≥ 2`, symmetric finite measure `ν`, and `|l| < 1/8`,
`∑_{n < N} ((2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv → ∫_{x > 1} x^{2l} (V_k(x))² dx` as `N → ∞`. -/
theorem tendsto_sum_range_pow_div_factorial_mul_moment_Ioi_one_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          ((2 * l) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
      atTop
      (nhds (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have h8l_nonneg : 0 ≤ 8 * |l| := by positivity
  have h8l_lt : 8 * |l| < 1 := by linarith
  have hgeom : Tendsto (fun N : ℕ => (8 * |l|) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h8l_nonneg h8l_lt
  have hmaj : Tendsto
      (fun N : ℕ => (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ N)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_setIntegral_Ioi_one_rpow_two_mul_sq_sub_sum_range_le hk hν hl N

/-- **Unconditional `N → ∞` real-analytic power-series convergence for `E_k^{(0, 1]}(l)` on `|l| < 1/8`:**
For every `k ≥ 2`, symmetric finite measure `ν`, and `|l| < 1/8`,
`∑_{n < N} ((−2l)^n / n!) ∫_{v > 0} v^n (Φ_k(v))² dv → ∫_{x ∈ (0, 1]} x^{2l} (V_k(x))² dx`
as `N → ∞`. -/
theorem tendsto_sum_range_neg_pow_div_factorial_mul_moment_Ioc_zero_one_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun N : ℕ =>
        ∑ n ∈ Finset.range N,
          ((-2 * l) ^ n / (n.factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
      atTop
      (nhds (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have h8l_nonneg : 0 ≤ 8 * |l| := by positivity
  have h8l_lt : 8 * |l| < 1 := by linarith
  have hgeom : Tendsto (fun N : ℕ => (8 * |l|) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h8l_nonneg h8l_lt
  have hmaj : Tendsto
      (fun N : ℕ => (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ N)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_setIntegral_Ioc_zero_one_rpow_two_mul_sq_sub_sum_range_le hk hν hl N


/-! ## Section 3: All-Orders Even Taylor Hierarchy & Power Series for `E_k(l)` -/

/-- **Integrability of `cosh(2lv) (Φ_k(v))²` on `ℝ` across `|l| < 1/2` (`k ≥ 2`).** -/
theorem integrable_cosh_two_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    Integrable (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  have e : (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => (1 / 2 : ℝ) *
        (Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 +
          Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    funext v; rw [Real.cosh_eq, show -(2 * l * v) = 2 * (-l) * v by ring]; ring
  rw [e]
  exact ((integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).add
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hl))).const_mul _

/-- **Strict positivity of the even logarithmic energy moments `∫_ℝ v^{2M} (Φ_k(v))² dv > 0` (`k ≥ 2`).** -/
theorem integral_even_pow_mul_sq_arcLineInfiniteDyadicProfile_pos
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (M : ℕ) :
    0 < ∫ v : ℝ, v ^ (2 * M) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
  have heq : (fun v : ℝ => v ^ (2 * M) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => |v| ^ (2 * M) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    funext v; rw [pow_mul, pow_mul, sq_abs]
  rw [heq]
  exact integral_abs_pow_mul_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos (2 * M)

/-- **Full-line integral linearity for the `M`-term even Taylor polynomial:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l ∈ ℝ`, and `M ∈ ℕ`,
`∫_ℝ (∑_{m < M} (2lv)^{2m} / (2m)!) (Φ_k(v))² dv =
  ∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv`. -/
theorem integral_sum_range_even_pow_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l : ℝ) (M : ℕ) :
    (∫ v : ℝ,
        (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  have hfun :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ext v
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow]
    ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact integral_const_mul _ _
  · intro m _
    exact (integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m)).const_mul _

/-- **Global all-orders even Taylor polynomial lower bound for `E_k(l)` across `|l| < 1/2`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/2`, and `M ∈ ℕ`,
`∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv ≤ ∫_{x > 0} x^{2l} (V_k(x))² dx`. -/
theorem sum_range_even_pow_div_factorial_mul_moment_le_setIntegral_Ioi
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (M : ℕ) :
    ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    integral_exp_two_mul_sq_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl,
    ← integral_sum_range_even_pow_mul_sq_eq hk hν l M]
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m)).const_mul _)
  have hInt_cosh : Integrable
      (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    integrable_cosh_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl
  refine integral_mono hInt_sum hInt_cosh (fun v => ?_)
  exact mul_le_mul_of_nonneg_right
    (sum_range_even_pow_div_factorial_le_cosh M (2 * l * v))
    (sq_nonneg _)

/-- **Global all-orders multi-moment critical-line excess coercivity across `|l| < 1/2`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/2`, and `M ∈ ℕ`,
`∑_{m < M} ((2l)^{2(m+1)} / (2(m+1))!) ∫_ℝ v^{2(m+1)} (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`. -/
theorem sum_range_even_pow_succ_div_factorial_mul_moment_le_excess
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (M : ℕ) :
    ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * (m + 1)) / ((2 * (m + 1)).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * (m + 1)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hle := sum_range_even_pow_div_factorial_mul_moment_le_setIntegral_Ioi hk hν hl (M + 1)
  rw [Finset.sum_range_succ'] at hle
  simp only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul] at hle
  have h0 := setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν 0
  simp only [mul_zero, Real.rpow_zero, one_mul, zero_mul, Real.exp_zero] at h0
  linarith

/-- **Strict monotonicity of the even Taylor partial sums in truncation order `M` off the critical line (`l ≠ 0`):**
For every `k ≥ 2` and `l ≠ 0`, the truncation map
`M ↦ ∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv` is strictly increasing. -/
theorem sum_range_even_pow_div_factorial_mul_moment_strictMono
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν)
    (hpos : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v)
    {l : ℝ} (hl_ne : l ≠ 0) :
    StrictMono (fun M : ℕ =>
      ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)) := by
  refine strictMono_nat_of_lt_succ (fun M => ?_)
  rw [Finset.sum_range_succ, lt_add_iff_pos_right]
  have hmom_pos : 0 < ∫ v : ℝ, v ^ (2 * M) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
    integral_even_pow_mul_sq_arcLineInfiniteDyadicProfile_pos hk hν hpos M
  have hpow_pos : 0 < (2 * l) ^ (2 * M) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (mul_ne_zero two_ne_zero hl_ne)) M
  positivity

/-- **Scale-independent geometric `O((8|l|)^{2M} / (1/8 − |l|))` Taylor remainder bound for `E_k(l)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/8`, and `M ∈ ℕ`,
`0 ≤ E_k(l) − ∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv ≤
  (680625 · (ν.real univ)² / (1/8 − |l|)) · (8|l|)^{2M}`. -/
theorem setIntegral_Ioi_rpow_two_mul_sq_sub_sum_range_even_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (M : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 2 * (1 / 8 - |l|) := by linarith
  rw [setIntegral_Ioi_rpow_two_mul_sq_arcLineInfiniteDyadicVector_eq hk1 ν l,
    integral_exp_two_mul_sq_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half,
    ← integral_sum_range_even_pow_mul_sq_eq hk hν l M]
  have hInt_cosh : Integrable
      (fun v : ℝ => Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    integrable_cosh_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_half
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrable_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m)).const_mul _)
  rw [← integral_sub hInt_cosh hInt_sum]
  have hInt_env : Integrable
      (fun v : ℝ =>
        680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ (2 * M) *
          Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul _
  have hbound :
      (∫ v : ℝ,
          (Real.cosh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
            (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
              (arcLineInfiniteDyadicProfile k ν v) ^ 2)) ≤
        ∫ v : ℝ,
          680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ (2 * M) *
            Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
    refine integral_mono (hInt_cosh.sub hInt_sum) hInt_env (fun v => ?_)
    rw [← sub_mul]
    have habs_u : |2 * l * v| = 2 * |l| * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hev_u : (2 * l * v) ^ (2 * M) = (2 * |l| * |v|) ^ (2 * M) := by
      rw [← habs_u, pow_mul, pow_mul, sq_abs]
    have hrem := cosh_sub_sum_range_even_pow_div_factorial_le M (2 * l * v)
    rw [hev_u, habs_u] at hrem
    calc (Real.cosh (2 * l * v) -
            ∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2
        ≤ ((2 * |l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (2 * |l| * |v|) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 :=
          mul_le_mul_of_nonneg_right hrem (sq_nonneg _)
      _ ≤ 680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ (2 * M) *
            Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) :=
          taylor_remainder_mul_sq_arcLineInfiniteDyadicProfile_le hk hν (2 * M) l v
  refine hbound.trans_eq ?_
  rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
  have hne : 1 / 8 - |l| ≠ 0 := by linarith
  field_simp

/-- **Unconditional `M → ∞` real-analytic power-series convergence for `E_k(l)` on `|l| < 1/8`:**
For every `k ≥ 2`, symmetric finite measure `ν`, and `|l| < 1/8`,
`∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv → ∫_{x > 0} x^{2l} (V_k(x))² dx`
as `M → ∞`. -/
theorem tendsto_sum_range_even_pow_div_factorial_mul_moment_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun M : ℕ =>
        ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  have h64_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have h8l_lt : 8 * |l| < 1 := by linarith
  have h64_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have hgeom : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h64_nonneg h64_lt
    exact h.congr (fun M => by rw [pow_mul])
  have hmaj : Tendsto
      (fun M : ℕ => (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  have hnonneg : 0 ≤
      (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
    sub_nonneg.mpr (sum_range_even_pow_div_factorial_mul_moment_le_setIntegral_Ioi hk hν hl_half M)
  rw [abs_of_nonneg hnonneg]
  exact setIntegral_Ioi_rpow_two_mul_sq_sub_sum_range_even_le hk hν hl M


/-! ## Section 4: All-Orders Odd Taylor Hierarchy & Power Series for `Δ_k(l)` -/

/-- **Integrability of `2 sinh(2lv) (Φ_k(v))²` on `(0, ∞)` across `|l| < 1/2` (`k ≥ 2`).** -/
theorem integrableOn_Ioi_zero_two_mul_sinh_two_mul_sq_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) :
    IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) := by
  have e : (fun v : ℝ => 2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ =>
        Real.exp (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
          Real.exp (2 * (-l) * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 := by
    funext v; rw [Real.sinh_eq, show -(2 * l * v) = 2 * (-l) * v by ring]; ring
  rw [e]
  exact (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl).integrableOn.sub
    (integrable_exp_two_mul_sq_arcLineInfiniteDyadicProfile hk hν (by simpa using hl)).integrableOn

/-- **Half-line integral linearity for the `M`-term odd Taylor polynomial:**
For every `k ≥ 2`, symmetric finite measure `ν`, `l ∈ ℝ`, and `M ∈ ℕ`,
`∫_{v > 0} (2 · ∑_{m < M} (2lv)^{2m+1} / (2m+1)!) (Φ_k(v))² dv =
  2 · ∑_{m < M} ((2l)^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} (Φ_k(v))² dv`. -/
theorem setIntegral_Ioi_zero_two_mul_sum_range_odd_pow_mul_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l : ℝ) (M : ℕ) :
    (∫ v in Ioi (0 : ℝ),
        2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      2 * ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
  have hfun :
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => 2 *
        ((∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ext v; ring
  rw [hfun, integral_const_mul]
  congr 1
  have hfun2 :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
      fun v : ℝ => ∑ m ∈ Finset.range M,
        ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
    ext v
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mul_pow]
    ring
  rw [hfun2, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    exact integral_const_mul _ _
  · intro m _
    exact (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m + 1)).const_mul _

/-- **Global all-orders odd Taylor polynomial lower bound for `|Δ_k(l)|` across `|l| < 1/2`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/2`, and `M ∈ ℕ`,
`2 · ∑_{m < M} ((2|l|)^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} (Φ_k(v))² dv ≤ |Δ_k(l)|`. -/
theorem sum_range_odd_abs_pow_div_factorial_mul_moment_le_abs_imbalance
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (M : ℕ) :
    2 * ∑ m ∈ Finset.range M,
        ((2 * |l|) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
      |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2| := by
  have hl_abs : |(|l|)| < 1 / 2 := by rwa [abs_abs]
  rw [abs_setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hl,
    setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hl_abs,
    ← setIntegral_Ioi_zero_two_mul_sum_range_odd_pow_mul_sq_eq hk hν |l| M]
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (2 * |l| * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          2 * (∑ m ∈ Finset.range M, (2 * |l| * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          (2 * ((2 * |l|) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ))) *
            (v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m + 1)).const_mul _)
  have hInt_sinh : IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (2 * |l| * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_zero_two_mul_sinh_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_abs
  refine setIntegral_mono_on hInt_sum hInt_sinh measurableSet_Ioi (fun v hv => ?_)
  have hv0 : 0 ≤ v := le_of_lt hv
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (sum_range_odd_pow_div_factorial_le_sinh_nonneg M (by positivity : 0 ≤ 2 * |l| * v))
      (by positivity))
    (sq_nonneg _)

/-- **Scale-independent geometric `O((8|l|)^{2M+1} / (1/8 − |l|))` Taylor remainder bound for `Δ_k(l)`:**
For every `k ≥ 2`, symmetric finite measure `ν`, `|l| < 1/8`, and `M ∈ ℕ`,
`|Δ_k(l) − 2 · ∑_{m < M} ((2l)^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} (Φ_k(v))² dv| ≤
  (1361250 · (ν.real univ)² / (1/8 − |l|)) · (8|l|)^{2M+1}`. -/
theorem abs_imbalance_sub_two_mul_sum_range_odd_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (M : ℕ) :
    |((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        2 * ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
      (1361250 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 2 * (1 / 8 - |l|) := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_two_mul_sq_eq hk hν hl_half,
    ← setIntegral_Ioi_zero_two_mul_sum_range_odd_pow_mul_sq_eq hk hν l M]
  have hInt_sinh : IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)
      (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_zero_two_mul_sinh_two_mul_sq_arcLineInfiniteDyadicProfile hk hν hl_half
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2) =
        fun v : ℝ => ∑ m ∈ Finset.range M,
          (2 * ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ))) *
            (v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by
      ext v
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      (integrableOn_Ioi_zero_pow_mul_sq_arcLineInfiniteDyadicProfile hk hν (2 * m + 1)).const_mul _)
  rw [← integral_sub hInt_sinh hInt_sum]
  set B := 2 * 680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ (2 * M + 1)
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
        2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2)
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) =
          (1361250 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1) := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      have hne : 1 / 8 - |l| ≠ 0 := by linarith
      dsimp [B]
      field_simp
      ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hsub :
        2 * Real.sinh (2 * l * v) * (arcLineInfiniteDyadicProfile k ν v) ^ 2 -
          2 * (∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2 =
        2 * ((Real.sinh (2 * l * v) -
            ∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (arcLineInfiniteDyadicProfile k ν v) ^ 2) := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg (arcLineInfiniteDyadicProfile k ν v))]
    have habs_u : |2 * l * v| = 2 * |l| * |v| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrem := abs_sinh_sub_sum_range_odd_pow_div_factorial_le M (2 * l * v)
    rw [habs_u] at hrem
    have htay := taylor_remainder_mul_sq_arcLineInfiniteDyadicProfile_le hk hν (2 * M + 1) l v
    calc 2 * (|Real.sinh (2 * l * v) -
              ∑ m ∈ Finset.range M, (2 * l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)| *
            (arcLineInfiniteDyadicProfile k ν v) ^ 2)
        ≤ 2 * (((2 * |l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp (2 * |l| * |v|) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrem (sq_nonneg _)) (by positivity)
      _ ≤ 2 * (680625 * (ν.real univ) ^ 2 * (8 * |l|) ^ (2 * M + 1) *
            Real.exp (-((2 * (1 / 8 - |l|)) * |v|))) :=
          mul_le_mul_of_nonneg_left htay (by positivity)
      _ = B * Real.exp (-((2 * (1 / 8 - |l|)) * |v|)) := by
          dsimp [B]; ring

/-- **Unconditional `M → ∞` real-analytic power-series convergence for `Δ_k(l)` on `|l| < 1/8`:**
For every `k ≥ 2`, symmetric finite measure `ν`, and `|l| < 1/8`,
`2 · ∑_{m < M} ((2l)^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} (Φ_k(v))² dv → Δ_k(l)` as `M → ∞`. -/
theorem tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_moment_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun M : ℕ =>
        2 * ∑ m ∈ Finset.range M,
          ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
      atTop
      (nhds ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
        ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2)) := by
  have h64_nonneg : 0 ≤ (8 * |l|) ^ 2 := sq_nonneg _
  have h8l_lt : 8 * |l| < 1 := by linarith
  have h64_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have hgeom_even : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h64_nonneg h64_lt
    exact h.congr (fun M => by rw [pow_mul])
  have hgeom : Tendsto (fun M : ℕ => (8 * |l|) ^ (2 * M + 1)) atTop (nhds 0) := by
    have h := hgeom_even.mul_const (8 * |l|)
    rw [zero_mul] at h
    exact h.congr (fun M => (pow_succ (8 * |l|) (2 * M)).symm)
  have hmaj : Tendsto
      (fun M : ℕ => (1361250 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (1361250 * (ν.real univ) ^ 2 / (1 / 8 - |l|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun M => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_imbalance_sub_two_mul_sum_range_odd_le hk hν hl M

/-- **Master All-Orders Critical-Line Taylor Polynomial & Real-Analytic Power-Series Witness Theorem:**
There exists a non-zero finite Borel measure `ν` on `ArcParam` symmetric under `arcNeg` such
that for every integer scale `k ≥ 2`:
1. **Global All-Orders Even Taylor Lower Bound & Multi-Moment Coercivity (`|l| < 1/2`):**
   for all `|l| < 1/2` and `M ∈ ℕ`,
   `∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv ≤ E_k(l)` and
   `∑_{m < M} ((2l)^{2(m+1)} / (2(m+1))!) ∫_ℝ v^{2(m+1)} (Φ_k(v))² dv ≤ E_k(l) − E_k(0)`;
2. **Strict Monotonicity in Truncation Order off the Critical Line (`l ≠ 0`):**
   for all `l ≠ 0`, `M ↦ ∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv` is strictly
   increasing;
3. **Scale-Independent Geometric Remainder & Power-Series Convergence for `E_k(l)` (`|l| < 1/8`):**
   `0 ≤ E_k(l) − ∑_{m < M} ((2l)^{2m} / (2m)!) ∫_ℝ v^{2m} (Φ_k(v))² dv ≤
     (680625 · (ν.real univ)² / (1/8 − |l|)) · (8|l|)^{2M} → 0` as `M → ∞`;
4. **Global Odd Taylor Lower Bound, Geometric Remainder, and Power-Series Convergence for `Δ_k(l)`:**
   for all `|l| < 1/2` and `M ∈ ℕ`,
   `2 · ∑_{m < M} ((2|l|)^{2m+1} / (2m+1)!) ∫_{v > 0} v^{2m+1} (Φ_k(v))² dv ≤ |Δ_k(l)|`, and
   for `|l| < 1/8`, the odd Taylor partial sums converge to `Δ_k(l)` at geometric rate
   `O((8|l|)^{2M+1} / (1/8 − |l|))`;
5. **One-Sided Sector Geometric Remainder & Power-Series Convergence on `(1, ∞)` and `(0, 1]`:**
   for `|l| < 1/8`, the `N`-term Taylor partial sums converge to `E_k^{(1, ∞)}(l)` and
   `E_k^{(0, 1]}(l)` at geometric rate `O((8|l|)^N / (1/8 − |l|))`. -/
theorem exists_dyadic_criticalLine_powerSeries_arcWitness :
    ∃ (ν : Measure ArcParam),
      ∃ (_ : IsFiniteMeasure ν),
        ν ≠ 0 ∧
        ν.map arcNeg = ν ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 2 → ∀ M : ℕ,
          ∑ m ∈ Finset.range M,
              ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            ∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 2 → ∀ M : ℕ,
          ∑ m ∈ Finset.range M,
              ((2 * l) ^ (2 * (m + 1)) / ((2 * (m + 1)).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * (m + 1)) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ∫ x in Ioi (0 : ℝ), (arcLineInfiniteDyadicVector k ν x) ^ 2) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, l ≠ 0 →
          StrictMono (fun M : ℕ =>
            ∑ m ∈ Finset.range M,
              ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 → ∀ M : ℕ,
          (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ∑ m ∈ Finset.range M,
                ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            (680625 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun M : ℕ =>
              ∑ m ∈ Finset.range M,
                ((2 * l) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 2 → ∀ M : ℕ,
          2 * ∑ m ∈ Finset.range M,
              ((2 * |l|) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2) ≤
            |(∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2|) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 → ∀ M : ℕ,
          |((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              2 * ∑ m ∈ Finset.range M,
                ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2)| ≤
            (1361250 * (ν.real univ) ^ 2 / (1 / 8 - |l|)) * (8 * |l|) ^ (2 * M + 1)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun M : ℕ =>
              2 * ∑ m ∈ Finset.range M,
                ((2 * l) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ), v ^ (2 * m + 1) * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
            atTop
            (nhds ((∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun N : ℕ =>
              ∑ n ∈ Finset.range N,
                ((2 * l) ^ n / (n.factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
            atTop
            (nhds (∫ x in Ioi (1 : ℝ), x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun N : ℕ =>
              ∑ n ∈ Finset.range N,
                ((-2 * l) ^ n / (n.factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ), v ^ n * (arcLineInfiniteDyadicProfile k ν v) ^ 2))
            atTop
            (nhds (∫ x in Ioc (0 : ℝ) 1, x ^ (2 * l) * (arcLineInfiniteDyadicVector k ν x) ^ 2))) := by
  obtain ⟨ν, hfin, hν_ne, hν_sym, _, hpd⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν_ne, hν_sym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk l hl M
    exact sum_range_even_pow_div_factorial_mul_moment_le_setIntegral_Ioi hk hν_sym hl M
  · intro k hk l hl M
    exact sum_range_even_pow_succ_div_factorial_mul_moment_le_excess hk hν_sym hl M
  · intro k hk l hl_ne
    exact sum_range_even_pow_div_factorial_mul_moment_strictMono hk hν_sym hpd hl_ne
  · intro k hk l hl M
    exact setIntegral_Ioi_rpow_two_mul_sq_sub_sum_range_even_le hk hν_sym hl M
  · intro k hk l hl
    exact tendsto_sum_range_even_pow_div_factorial_mul_moment_atTop hk hν_sym hl
  · intro k hk l hl M
    exact sum_range_odd_abs_pow_div_factorial_mul_moment_le_abs_imbalance hk hν_sym hl M
  · intro k hk l hl M
    exact abs_imbalance_sub_two_mul_sum_range_odd_le hk hν_sym hl M
  · intro k hk l hl
    exact tendsto_two_mul_sum_range_odd_pow_div_factorial_mul_moment_atTop hk hν_sym hl
  · intro k hk l hl
    exact tendsto_sum_range_pow_div_factorial_mul_moment_Ioi_one_atTop hk hν_sym hl
  · intro k hk l hl
    exact tendsto_sum_range_neg_pow_div_factorial_mul_moment_Ioc_zero_one_atTop hk hν_sym hl

end RHTower

end
