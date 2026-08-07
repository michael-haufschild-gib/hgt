import GaloisForLFunctions.RHTower.EulerHellingerSewingLogRatio

/-!
# The fixed-displacement accelerated boundary

For a fixed drift `0 < c < 1/2`, the Mertens product accelerates the logarithm of the reflected
sewing cost to a linear valuation in the displacement:

```text
a_N · log L_N(c) → 2 e^(-γ) c,        a_N = ∏_{p < N} (1 - 1/p).
```

It factors as `(a_N log N) · (log L_N(c) / log N)`, the first factor being Mertens' third theorem
and the second the logarithmic growth rate of the sewing cost.
-/

open Filter Topology Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The Mertens product over `p < N`. -/
def mertensPrimeProductBelow (N : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesBelow N, (1 - ((p : ℝ))⁻¹)

/-- The last factor separating the two Mertens product conventions. -/
private def mertensLastFactor (N : ℕ) : ℝ := if N.Prime then 1 - ((N : ℝ))⁻¹ else 1

private theorem mertensLastFactor_pos (N : ℕ) : 0 < mertensLastFactor N := by
  rw [mertensLastFactor]
  split_ifs with hp
  · have hn2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp.two_le
    have : ((N : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [one_div, inv_le_inv₀ (by linarith) (by norm_num)]
      exact hn2
    linarith
  · norm_num

private theorem abs_mertensLastFactor_sub_one (N : ℕ) :
    |mertensLastFactor N - 1| ≤ 1 / (N : ℝ) := by
  rw [mertensLastFactor]
  split_ifs with hp
  · have hn2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp.two_le
    rw [show (1 : ℝ) - ((N : ℝ))⁻¹ - 1 = -((N : ℝ))⁻¹ by ring, abs_neg,
      abs_of_nonneg (by positivity), one_div]
  · rw [sub_self, abs_zero]
    positivity

private theorem tendsto_mertensLastFactor : Tendsto mertensLastFactor atTop (nhds 1) := by
  have h : Tendsto (fun N : ℕ => mertensLastFactor N - 1) atTop (nhds 0) :=
    squeeze_zero_norm (fun N => by
      rw [Real.norm_eq_abs]
      exact abs_mertensLastFactor_sub_one N)
      tendsto_one_div_atTop_nhds_zero_nat
  have h2 : Tendsto (fun N : ℕ => mertensLastFactor N - 1 + 1) atTop (nhds (0 + 1)) :=
    h.add tendsto_const_nhds
  rw [zero_add] at h2
  refine h2.congr fun N => ?_
  ring

theorem mertensPrimeProduct_eq_below_mul (N : ℕ) :
    mertensPrimeProduct N = mertensPrimeProductBelow N * mertensLastFactor N := by
  have hrange : ∀ K : ℕ,
      mertensPrimeProductBelow K = ∏ n ∈ Finset.range K, (if n.Prime then 1 - ((n : ℝ))⁻¹ else 1) := by
    intro K
    rw [mertensPrimeProductBelow, Nat.primesBelow, Finset.prod_filter]
  rw [mertensPrimeProduct,
    show Finset.Icc 0 N = Finset.range (N + 1) by ext n; simp,
    Finset.prod_range_succ, hrange, mertensLastFactor]

/-- **Mertens' third theorem for the half-open product.** -/
theorem tendsto_mertensPrimeProductBelow_mul_log :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N * Real.log N) atTop
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have hinv : Tendsto (fun N : ℕ => (mertensLastFactor N)⁻¹) atTop (nhds 1) := by
    have := tendsto_mertensLastFactor.inv₀ (by norm_num)
    rwa [inv_one] at this
  have hmul := tendsto_mertensPrimeProduct_mul_log.mul hinv
  rw [mul_one] at hmul
  refine hmul.congr fun N => ?_
  have hne : mertensLastFactor N ≠ 0 := ne_of_gt (mertensLastFactor_pos N)
  rw [mertensPrimeProduct_eq_below_mul,
    show mertensPrimeProductBelow N * mertensLastFactor N * Real.log (N : ℝ) *
        (mertensLastFactor N)⁻¹ =
      mertensPrimeProductBelow N * Real.log (N : ℝ) *
        (mertensLastFactor N * (mertensLastFactor N)⁻¹) by ring,
    mul_inv_cancel₀ hne, mul_one]

/-- **The fixed-displacement accelerated boundary.**  The Mertens product accelerates the
logarithm of the reflected sewing cost to the linear valuation `2 e^(-γ) c`. -/
theorem tendsto_mertensProduct_mul_log_logReflectedSewing {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2) :
    Tendsto (fun N : ℕ => mertensPrimeProductBelow N * Real.log (logReflectedSewingBelow c N))
      atTop (nhds (2 * Real.exp (-Real.eulerMascheroniConstant) * c)) := by
  have hmul := tendsto_mertensPrimeProductBelow_mul_log.mul
    (tendsto_log_logReflectedSewing_div_log hc0 hc)
  rw [show Real.exp (-Real.eulerMascheroniConstant) * (2 * c) =
      2 * Real.exp (-Real.eulerMascheroniConstant) * c by ring] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with N hN
  have hNr : (2 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogN
  field_simp

end

end RHTower
