import GaloisForLFunctions.RHTower.WeilLogShiftSmoothEdgeBound
import GaloisForLFunctions.RHTower.WeilLogShiftLocalDecayThreshold

/-!
# Uniform exponential envelopes for the triangular recovery rows

The native overlap at column j in row n is at most (n+1-j)/j. Retaining its
smooth edge cost gives a bound uniform over the whole triangular matrix,
rather than only its diagonal.
-/

open Filter Topology Real

noncomputable section

namespace RHTower

open WeilExcess

/-- A relaxed edge bound covers all overlap scales, including the full-kernel
regime where the original reciprocal scale is below two. -/
theorem truncatedRiemannAutocorr_le_exp_edge_relaxed (L y r : ℝ)
    (hmargin : 2 * L - y ≤ 1 / r) :
    truncatedRiemannAutocorr L y ≤ exp (8 - 4 * r) * riemannAutocorr y := by
  by_cases hr : 2 ≤ r
  · exact (truncatedRiemannAutocorr_le_exp_edge L y r hr hmargin).trans
      (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith))
        (riemannAutocorr_nonneg y))
  · have he : 1 ≤ exp (8 - 4 * r) := one_le_exp_iff.mpr (by linarith only [hr])
    exact (truncatedRiemannAutocorr_le_riemannAutocorr L y).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right he (riemannAutocorr_nonneg y))

/-- Every nonzero column of a recovery row has a reciprocal overlap bound. -/
theorem weilLogShiftRecoveryCutoff_column_margin_le (n j : ℕ) (hj : 2 ≤ j) :
    2 * weilLogShiftRecoveryCutoff n - (log j - log 2) ≤
      ((n : ℝ) + 1 - j) / j := by
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  have hlog := log_le_sub_one_of_pos (div_pos hnpos hjpos)
  rw [log_div hnpos.ne' hjpos.ne'] at hlog
  calc
    _ = log ((n : ℝ) + 1) - log j := by
      simp only [weilLogShiftRecoveryCutoff, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ ((n : ℝ) + 1) / j - 1 := hlog
    _ = _ := by field_simp [hjpos.ne']

/-- A common edge factor bounds the absolute weight even where its three
kernel terms may have different signs after subtraction. -/
theorem weilLogShiftRecoveryWeight_row_edge_bound (n j : ℕ) (hj : 2 ≤ j)
    (hjn : j ≤ n) :
    |weilLogShiftRecoveryWeight n j| ≤
      2 * exp (8 - 4 * j / ((n : ℝ) + 1 - j)) *
        (pairedLogKernel (log 2) j + pairedLogKernel 0 j) := by
  let L := weilLogShiftRecoveryCutoff n
  let r : ℝ := j / ((n : ℝ) + 1 - j)
  let E := exp (8 - 4 * r)
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hgap : 0 < (n : ℝ) + 1 - j := by
    have h : (j : ℝ) ≤ n := by exact_mod_cast hjn
    linarith only [h]
  have hrecip : 1 / r = ((n : ℝ) + 1 - j) / j := by
    dsimp only [r]
    field_simp [hjpos.ne', hgap.ne']
  have hmargin : 2 * L - (log j - log 2) ≤ 1 / r := by
    rw [hrecip]
    exact weilLogShiftRecoveryCutoff_column_margin_le n j hj
  have hc : 0 ≤ log (2 : ℝ) := log_nonneg (by norm_num)
  have hm := truncatedRiemannAutocorr_le_exp_edge_relaxed L (log j - log 2) r hmargin
  have hp := truncatedRiemannAutocorr_le_exp_edge_relaxed L (log j + log 2) r
    (by linarith only [hmargin, hc])
  have h0 := truncatedRiemannAutocorr_le_exp_edge_relaxed L (log j) r
    (by linarith only [hmargin, hc])
  change _ ≤ E * _ at hm hp h0
  have hpair : 2 * riemannAutocorr (log j + log 2) +
      2 * riemannAutocorr (log j - log 2) + 4 * riemannAutocorr (log j) =
      2 * (pairedLogKernel (log 2) j + pairedLogKernel 0 j) := by
    simp only [pairedLogKernel, zero_add, zero_sub, riemannAutocorr_neg]
    rw [show log j - log 2 = -(log 2 - log j) by ring, riemannAutocorr_neg,
      add_comm (log j) (log 2)]
    ring
  have hnum : |2 * truncatedRiemannAutocorr L (log j + log 2) +
      2 * truncatedRiemannAutocorr L (log j - log 2) -
      4 * truncatedRiemannAutocorr L (log j)| ≤
      2 * E * (pairedLogKernel (log 2) j + pairedLogKernel 0 j) := by
    have hnonneg₁ := truncatedRiemannAutocorr_nonneg L (log j + log 2)
    have hnonneg₂ := truncatedRiemannAutocorr_nonneg L (log j - log 2)
    have hnonneg₀ := truncatedRiemannAutocorr_nonneg L (log j)
    have htri := abs_sub_le
      (2 * truncatedRiemannAutocorr L (log j + log 2) +
        2 * truncatedRiemannAutocorr L (log j - log 2)) 0
      (4 * truncatedRiemannAutocorr L (log j))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    rw [abs_of_nonneg (show 0 ≤ 2 * truncatedRiemannAutocorr L (log j + log 2) +
      2 * truncatedRiemannAutocorr L (log j - log 2) by positivity),
      abs_of_nonneg (show 0 ≤ 4 * truncatedRiemannAutocorr L (log j) by positivity)] at htri
    calc
      _ ≤ 2 * truncatedRiemannAutocorr L (log j + log 2) +
          2 * truncatedRiemannAutocorr L (log j - log 2) +
          4 * truncatedRiemannAutocorr L (log j) := htri
      _ ≤ E * (2 * riemannAutocorr (log j + log 2) +
          2 * riemannAutocorr (log j - log 2) + 4 * riemannAutocorr (log j)) := by
        nlinarith only [hm, hp, h0]
      _ = _ := by rw [hpair]; ring
  have hsqrt : 1 ≤ sqrt (j : ℝ) := by
    have h : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
    simpa only [sqrt_one] using sqrt_le_sqrt h
  change |(2 * truncatedRiemannAutocorr L (log j + log 2) +
    2 * truncatedRiemannAutocorr L (log j - log 2) -
    4 * truncatedRiemannAutocorr L (log j)) / sqrt j| ≤ _
  rw [abs_div, abs_of_nonneg (sqrt_nonneg _)]
  calc
    _ ≤ |2 * truncatedRiemannAutocorr L (log j + log 2) +
        2 * truncatedRiemannAutocorr L (log j - log 2) -
        4 * truncatedRiemannAutocorr L (log j)| / 1 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hsqrt
    _ ≤ 2 * E * (pairedLogKernel (log 2) j + pairedLogKernel 0 j) := by
      simpa only [div_one] using hnum
    _ = _ := by dsimp only [E, r]; congr 3; ring

/-- Any strictly sub-pi kernel rate combines with the exact reciprocal edge
loss to control every entry of every recovery row. -/
theorem exists_weilLogShiftRecoveryWeight_row_exponential_bound {a : ℝ}
    (ha0 : 0 < a) (hapi : a < π) :
    ∃ C : ℝ, 0 < C ∧ ∀ n j : ℕ, 2 ≤ j → j ≤ n →
      |weilLogShiftRecoveryWeight n j| ≤
        C * exp (-a * j - 4 * j / ((n : ℝ) + 1 - j)) := by
  have hrate : logKernelCriticalRate (log 2) = π := by
    have h := logKernelCriticalRate_log_nat (m := 2) (by omega)
    norm_num at h
    exact h
  obtain ⟨C₂, hC₂, hupper₂⟩ := exists_paired_logKernel_upper_of_lt_rate
    (y := log 2) ha0 (by rwa [hrate])
  obtain ⟨C₀, hC₀, hupper₀⟩ := exists_paired_logKernel_upper_of_lt_rate
    (y := 0) ha0 (by
      simp only [logKernelCriticalRate, abs_zero, neg_zero, exp_zero, mul_one]
      linarith only [hapi, pi_pos])
  refine ⟨2 * exp 8 * (C₂ + C₀), by positivity, fun n j hj hjn => ?_⟩
  have hpair : pairedLogKernel (log 2) j + pairedLogKernel 0 j ≤
      (C₂ + C₀) * exp (-(a * j)) := by
    have h₂ := hupper₂ j (by omega)
    have h₀ := hupper₀ j (by omega)
    change pairedLogKernel (log 2) j ≤ _ at h₂
    change pairedLogKernel 0 j ≤ _ at h₀
    nlinarith only [h₂, h₀]
  calc
    _ ≤ 2 * exp (8 - 4 * j / ((n : ℝ) + 1 - j)) *
        (pairedLogKernel (log 2) j + pairedLogKernel 0 j) :=
      weilLogShiftRecoveryWeight_row_edge_bound n j hj hjn
    _ ≤ 2 * exp (8 - 4 * j / ((n : ℝ) + 1 - j)) *
        ((C₂ + C₀) * exp (-(a * j))) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ = _ := by
      rw [show 8 - 4 * (j : ℝ) / ((n : ℝ) + 1 - j) =
        8 + -(4 * j / ((n : ℝ) + 1 - j)) by ring, exp_add,
        show -a * (j : ℝ) - 4 * j / ((n : ℝ) + 1 - j) =
          -(4 * j / ((n : ℝ) + 1 - j)) + -(a * j) by ring, exp_add]
      ring

/-- The reciprocal edge loss and accumulated earlier growth leave a uniform
exponential gap against the proposed adjacent-row rate. -/
theorem weilLogShiftRecovery_tail_exponent_gap {n j : ℝ}
    (hjn : j + 2 ≤ n) (hj : 625 ≤ j) :
    (π + 9 / 4) * n - (99 * π / 100) * j - 4 * j / (n + 1 - j) -
      (j + 1) * (n - j - 1) ≤ -n / 100 := by
  let m := n - j - 1
  have hm : 1 ≤ m := by dsimp only [m]; linarith only [hjn]
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hj0 : 0 ≤ j := by linarith only [hj]
  have hden : 0 < m + 2 := by linarith only [hm]
  have hdiv : 4 / (m + 2) * (m + 2) = 4 := div_mul_cancel₀ _ hden.ne'
  have hquad : m / 3 ≤ m + 4 / (m + 2) - 2 := by
    apply (mul_le_mul_iff_left₀ hden).mp
    have hprod : 0 ≤ m * (m - 1) := mul_nonneg hm0 (by linarith only [hm])
    nlinarith only [hdiv, hprod]
  have hcost : m / 25 ≤ m + 4 / (m + 2) - 9 / 4 - π / 100 := by
    linarith only [hquad, hm, pi_lt_four]
  have hscale := mul_le_mul_of_nonneg_left hcost hj0
  have hbeta := mul_le_mul_of_nonneg_right
    (show π + 9 / 4 ≤ 25 / 4 by linarith only [pi_lt_four])
    (show 0 ≤ m + 1 by linarith only [hm])
  have htail : (π + 9 / 4) * (m + 1) - m ≤ (25 / 2) * m := by
    nlinarith only [hbeta, hm]
  have hlarge := mul_le_mul_of_nonneg_right hj hm0
  have hnm : n = j + m + 1 := by dsimp only [m]; ring
  have hproduct : n / 2 ≤ j * m := by
    have h := mul_nonneg (show 0 ≤ j - 2 by linarith only [hj])
      (show 0 ≤ m - 1 by linarith only [hm])
    rw [hnm]
    nlinarith only [h, hj, hm]
  calc
    _ = j * (9 / 4 + π / 100 - m - 4 / (m + 2)) +
        (π + 9 / 4) * (m + 1) - m := by
      rw [show n + 1 - j = m + 2 by dsimp only [m]; ring]
      change _ - (j + 1) * m = _
      rw [hnm]
      ring
    _ ≤ -j * m / 25 + (25 / 2) * m := by nlinarith only [hscale, htail]
    _ ≤ -j * m / 50 := by nlinarith only [hlarge]
    _ ≤ -n / 100 := by linarith only [hproduct]

end RHTower
