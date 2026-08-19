import GaloisForLFunctions.HTGeometry.GammaStirlingTelescope

/-!
# The Taylor bound for `log (1 + u)` at every order

Mathlib supplies the quadratic bound `Complex.norm_log_one_add_sub_self_le`.  The Stirling ladder
needs one order per rung, so the bound is proved here uniformly in the order: dropping the first `n`
terms of `Complex.hasSum_taylorSeries_log` and summing the geometric tail gives

```text
‖log(1+u) − ∑_{j<n} (−1)^{j+1} u^j / j‖ ≤ 2 ‖u‖^n / n      on ‖u‖ ≤ ½.
```

(The `j = 0` summand is `−1/0 = 0` in Lean's convention, so the sum really starts at `j = 1`.)
The cubic and quartic bounds used by the first two rungs are the cases `n = 3, 4`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 1000000 in
theorem norm_log_one_add_sub_taylor_le {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.log (1 + u) - ∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ)‖
      ≤ 2 * ‖u‖ ^ n / (n : ℝ) := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hu1 : ‖u‖ < 1 := lt_of_le_of_lt hu (by norm_num)
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum := Complex.hasSum_taylorSeries_log hu1
  have hsummable : Summable (fun k : ℕ => (-1 : ℂ) ^ (k + 1) * u ^ k / (k : ℂ)) := hsum.summable
  have hsplit := hsummable.sum_add_tsum_nat_add n
  have hlog : Complex.log (1 + u) = ∑' k : ℕ, (-1 : ℂ) ^ (k + 1) * u ^ k / (k : ℂ) :=
    hsum.tsum_eq.symm
  have htail : Complex.log (1 + u) - ∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ)
      = ∑' k : ℕ, (-1 : ℂ) ^ (k + n + 1) * u ^ (k + n) / ((k + n : ℕ) : ℂ) := by
    rw [hlog, ← hsplit]
    ring
  have hbound : ∀ k : ℕ, ‖(-1 : ℂ) ^ (k + n + 1) * u ^ (k + n) / ((k + n : ℕ) : ℂ)‖
      ≤ (‖u‖ ^ n / (n : ℝ)) * ‖u‖ ^ k := by
    intro k
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
    have hcast : ((k + n : ℕ) : ℝ) = (k : ℝ) + (n : ℝ) := by push_cast; ring
    rw [hcast]
    have hden : (n : ℝ) ≤ (k : ℝ) + (n : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hnum : ‖u‖ ^ (k + n) = ‖u‖ ^ n * ‖u‖ ^ k := by
      rw [pow_add]
      ring
    rw [hnum, div_le_iff₀ (by linarith : (0 : ℝ) < (k : ℝ) + (n : ℝ))]
    have hpos : (0 : ℝ) ≤ ‖u‖ ^ n * ‖u‖ ^ k := by positivity
    have hid : ‖u‖ ^ n / (n : ℝ) * ‖u‖ ^ k * ((k : ℝ) + (n : ℝ))
        = (‖u‖ ^ n * ‖u‖ ^ k) * (((k : ℝ) + (n : ℝ)) / (n : ℝ)) := by
      field_simp
    rw [hid]
    have hratio : (1 : ℝ) ≤ ((k : ℝ) + (n : ℝ)) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      linarith
    nlinarith [hpos, hratio]
  have hgeo : Summable (fun k : ℕ => (‖u‖ ^ n / (n : ℝ)) * ‖u‖ ^ k) :=
    (summable_geometric_of_lt_one hu0 hu1).mul_left _
  have hnormsummable : Summable (fun k : ℕ =>
      ‖(-1 : ℂ) ^ (k + n + 1) * u ^ (k + n) / ((k + n : ℕ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hbound hgeo
  rw [htail]
  refine le_trans (norm_tsum_le_tsum_norm hnormsummable) ?_
  refine le_trans (hnormsummable.tsum_le_tsum hbound hgeo) ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hu0 hu1]
  have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hnn : (0 : ℝ) ≤ ‖u‖ ^ n / (n : ℝ) := by positivity
  have hid2 : 2 * ‖u‖ ^ n / (n : ℝ) = (‖u‖ ^ n / (n : ℝ)) * 2 := by ring
  rw [hid2]
  exact mul_le_mul_of_nonneg_left hinv hnn

/-- For orders at least two the constant simplifies. -/
theorem norm_log_one_add_sub_taylor_le' {u : ℂ} (hu : ‖u‖ ≤ 1 / 2) {n : ℕ} (hn : 2 ≤ n) :
    ‖Complex.log (1 + u) - ∑ j ∈ Finset.range n, (-1 : ℂ) ^ (j + 1) * u ^ j / (j : ℂ)‖
      ≤ ‖u‖ ^ n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine le_trans (norm_log_one_add_sub_taylor_le hu (by omega)) ?_
  rw [div_le_iff₀ hnpos]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [pow_nonneg (norm_nonneg u) n, hn2]

end

end GaloisForLFunctions.HTGeometry
