import GaloisForLFunctions.BezoutValuationIncidence.SmoothLargeScaleRowsAndTheCancellationOfBothKernels

/-!
# The dual norm of the cross-scale functional

Fix the large-scale row `c'` and put `S' = Σ_n c'(n)/n²`. For a prime `p` its **kernel statistic** is

`Λ_p(c') = Σ_n (c'(n)/n²)(𝔅(p, n) - m_p) + Σ_n (c'(n)/n³) 𝔅₃(p, n)`,  `m_p = π²(p² - 1)/(72p²)`.

By the third-order law the cross-scale form of every row `c` on primes is

`B + m R' + β H' = (π²/72) S' Σ_p c(p)(p² - 1)/p³ + Σ_p (c(p)/p) Λ_p(c') + O(6 Σ_p |c(p)| p³ Σ_n |c'(n)|/n⁴)`.

Taking `c(p) = sign Λ_p(c')` on a prime set `S` attains the triangle inequality. Hence, up to the
fourth-order term,

`sup_{|c| ≤ 1 on S} |B + m R' + β H' - (π²/72) S' Σ_p c(p)(p² - 1)/p³| = Σ_{p ∈ S} |Λ_p(c')|/p`.

A Type-II bound for arbitrary bounded small-scale coefficients is therefore exactly a bound on the
single-modulus statistics `Σ_p |Λ_p(c')|/p`: one linear statistic of the large-scale row per small
prime, with no bilinear structure left. Smoothness of `c'` bounds each `Λ_p` (the smooth-row law), and
residue equidistribution bounds its `𝔅`-part (the discrepancy law). For arithmetic large-scale rows
the problem is the size of these statistics, which are low-frequency exponential sums
`Σ_{a} W_p(a) Σ_n (c'(n)/n²) e(an/p)`.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The kernel statistic `Λ_p(c') = Σ_n (c'(n)/n²)(𝔅(p, n) - m_p) + Σ_n (c'(n)/n³) 𝔅₃(p, n)`. -/
def kernelStatistic (N : ℕ) (c' : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, (c' n / (n : ℝ) ^ 2 * (bernoulliKernel p n - primeKernelMean p) +
    c' n / (n : ℝ) ^ 3 * cubicKernel p n)

/-- The rank-one main term `(π²/72) S' Σ_d c(d)(d² - 1)/d³`. -/
def equidistributedMain (N : ℕ) (c c' : ℕ → ℝ) : ℝ :=
  Real.pi ^ 2 / 72 * (∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2) *
    ∑ d ∈ Icc 1 N, c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3

/-- **The cross-scale form through the kernel statistics.** For every row `c` on primes,
`|B + m R' + β H' - main(c) - Σ_d (c(d)/d) Λ_d(c')| ≤ 6 Σ_d |c(d)| d³ Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_sub_kernelStatistic_le (N : ℕ) {c : ℕ → ℝ} (c' : ℕ → ℝ)
    (hc : ∀ d, c d ≠ 0 → d.Prime) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d| ≤
      6 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have hlaw := abs_rowBilinear_add_mean_add_beta_sub_third_order_le N c c'
  set S' := ∑ n ∈ Icc 1 N, c' n / (n : ℝ) ^ 2
  have hK : ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, c' n * (c d / d) *
      (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3) =
      equidistributedMain N c c' + ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d := by
    have e1 : equidistributedMain N c c' =
        ∑ d ∈ Icc 1 N, Real.pi ^ 2 / 72 * S' * (c d * ((d : ℝ) ^ 2 - 1) / (d : ℝ) ^ 3) := by
      rw [equidistributedMain]; exact mul_sum _ _ _
    rw [sum_comm, e1, ← sum_add_distrib]
    refine sum_congr rfl fun d _ => ?_
    by_cases hcd : c d = 0
    · simp [hcd]
    have hp := hc d hcd
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm : primeKernelMean d * S' = Real.pi ^ 2 * ((d : ℝ) ^ 2 - 1) / (72 * (d : ℝ) ^ 2) * S' := by
      rw [primeKernelMean]
    have hsplit : ∑ n ∈ Icc 1 N, c' n * (c d / d) *
        (bernoulliKernel d n / (n : ℝ) ^ 2 + cubicKernel d n / (n : ℝ) ^ 3) =
        c d / d * (kernelStatistic N c' d + primeKernelMean d * S') := by
      rw [kernelStatistic, show primeKernelMean d * S' =
          ∑ n ∈ Icc 1 N, primeKernelMean d * (c' n / (n : ℝ) ^ 2) from mul_sum _ _ _,
        ← sum_add_distrib, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    rw [hsplit, hm]
    field_simp
    ring
  rw [hK] at hlaw
  calc |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d|
      = |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c' -
          (equidistributedMain N c c' + ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d)| := by
        ring_nf
    _ ≤ _ := hlaw

/-- **The dual norm is attained.** For a set `S ⊆ [1, N]` of primes there is a row `c` with `|c| ≤ 1`,
supported on `S`, whose cross-scale form exceeds its main term by at least
`Σ_{p ∈ S} |Λ_p(c')|/p - 6 (Σ_{p ∈ S} p³) Σ_n |c'(n)|/n⁴`. -/
theorem exists_rowBilinear_sub_main_ge (N : ℕ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N)
    (c' : ℕ → ℝ) :
    ∃ c : ℕ → ℝ, (∀ d, |c d| ≤ 1) ∧ (∀ d, c d ≠ 0 → d ∈ S) ∧
      ∑ p ∈ S, |kernelStatistic N c' p| / p -
          6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 ≤
        rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
          rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c' := by
  classical
  set c : ℕ → ℝ := fun d => if d ∈ S then (if 0 ≤ kernelStatistic N c' d then 1 else -1) else 0
  have hcabs : ∀ d, |c d| = if d ∈ S then 1 else 0 := fun d => by
    simp only [c]; split_ifs <;> simp
  have hsupp : ∀ d, c d ≠ 0 → d ∈ S := fun d h => by
    by_contra hd; exact h (by simp [c, hd])
  have hSI : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩
  refine ⟨c, fun d => by rw [hcabs]; split_ifs <;> norm_num, hsupp, ?_⟩
  have h := abs_rowBilinear_sub_kernelStatistic_le N c' (c := c)
    (fun d hd => (hS d (hsupp d hd)).1)
  have hstat : ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d =
      ∑ p ∈ S, |kernelStatistic N c' p| / p := by
    rw [← sum_subset hSI fun d _ hd => by simp [c, hd]]
    refine sum_congr rfl fun p hp => ?_
    simp only [c, if_pos hp]
    split_ifs with h0
    · rw [abs_of_nonneg h0]; ring
    · rw [abs_of_neg (not_le.mp h0)]; ring
  have hcube : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 = ∑ p ∈ S, (p : ℝ) ^ 3 := by
    rw [← sum_subset hSI fun d _ hd => by rw [hcabs, if_neg hd, zero_mul]]
    exact sum_congr rfl fun p hp => by rw [hcabs, if_pos hp, one_mul]
  rw [hstat, hcube] at h
  have := (abs_le.mp h).1
  linarith

/-- **The two-sided bound.** For every row `c` with `|c| ≤ 1` supported on a set `S ⊆ [1, N]` of primes,
`|B + m R' + β H' - main(c)| ≤ Σ_{p ∈ S} |Λ_p(c')|/p + 6 (Σ_{p ∈ S} p³) Σ_n |c'(n)|/n⁴`. -/
theorem abs_rowBilinear_sub_main_le_dual (N : ℕ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N)
    {c : ℕ → ℝ} (c' : ℕ → ℝ) (hc1 : ∀ d, |c d| ≤ 1) (hsupp : ∀ d, c d ≠ 0 → d ∈ S) :
    |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c'| ≤
      ∑ p ∈ S, |kernelStatistic N c' p| / p +
        6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := by
  have hSI : S ⊆ Icc 1 N := fun p hp => mem_Icc.mpr ⟨(hS p hp).1.one_lt.le, (hS p hp).2⟩
  have h := abs_rowBilinear_sub_kernelStatistic_le N c' (c := c)
    (fun d hd => (hS d (hsupp d hd)).1)
  have hstat : |∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d| ≤
      ∑ p ∈ S, |kernelStatistic N c' p| / p := by
    rw [← sum_subset hSI fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    rw [abs_mul, abs_div, abs_of_pos hpR]
    calc |c p| / p * |kernelStatistic N c' p| ≤ 1 / p * |kernelStatistic N c' p| := by
          gcongr; exact hc1 p
      _ = |kernelStatistic N c' p| / p := by ring
  have hcube : ∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 3 ≤ ∑ p ∈ S, (p : ℝ) ^ 3 := by
    rw [← sum_subset hSI fun d _ hd => by
      have : c d = 0 := by by_contra h; exact hd (hsupp d h)
      simp [this]]
    exact sum_le_sum fun p _ => by
      have := hc1 p
      have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
      nlinarith [abs_nonneg (c p)]
  have hS4 : 0 ≤ ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 := sum_nonneg fun n _ => by positivity
  have h2 : |rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
        rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c' -
        ∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d| ≤
      6 * (∑ p ∈ S, (p : ℝ) ^ 3) * ∑ n ∈ Icc 1 N, |c' n| / (n : ℝ) ^ 4 :=
    h.trans (by gcongr)
  have key := abs_sub_abs_le_abs_sub (rowBilinear N c c' + rowMean N c * vonMangoldtReadout N c' +
    rowBeta N c * finiteHarmonicSum N c' - equidistributedMain N c c')
    (∑ d ∈ Icc 1 N, c d / d * kernelStatistic N c' d)
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
