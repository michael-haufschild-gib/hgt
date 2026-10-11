import GaloisForLFunctions.RHTower.WeilLogShiftMidpointSecondMomentBound
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeConcentration
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialLimit

/-! The edge second moment has the sharp binomial fluctuation constant one quarter. -/

open Filter Topology

namespace RHTower

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_sharp_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4| ≤
      4 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  have h := finiteWeilCanonicalMixture_midpoint_second_moment_error r k hwidth
  rw [finiteWeilCanonicalMixture_midpoint_edge_half_centered_second_moment] at h
  change |finiteWeilCanonicalEdgeCenteredSecondMoment r k + 1 / 4 - ((r + 1 : ℕ) : ℝ) / 4| ≤ _ at h
  have hid : finiteWeilCanonicalEdgeCenteredSecondMoment r k + 1 / 4 - ((r + 1 : ℕ) : ℝ) / 4 =
      finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4 := by push_cast; ring
  rwa [hid] at h

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_normalized_sharp_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeCenteredSecondMoment r k / ((r + 1 : ℕ) : ℝ) - 1 / 4| ≤
      6 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  let n : ℝ := ((r + 1 : ℕ) : ℝ)
  let S := Real.sqrt ((n + 1) / 2)
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : 1 ≤ S := by
    have hs0 := Real.sqrt_nonneg ((n + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (n + 1) / 2 by positivity)
    change 1 ≤ Real.sqrt ((n + 1) / 2)
    nlinarith only [hs0, hs2, hn1]
  have hb := finiteWeilCanonicalEdgeCenteredSecondMoment_sharp_bound r k hwidth
  change |finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4| ≤ 4 * S at hb
  have ht := abs_sub (finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4) ((1 : ℝ) / 4)
  norm_num at ht
  have hid : finiteWeilCanonicalEdgeCenteredSecondMoment r k - n / 4 =
      (finiteWeilCanonicalEdgeCenteredSecondMoment r k - (r : ℝ) / 4) - 1 / 4 := by dsimp [n]; push_cast; ring
  have hraw : |finiteWeilCanonicalEdgeCenteredSecondMoment r k - n / 4| ≤ 6 * S := by
    rw [hid]
    linarith only [ht, hb, hS]
  have hdiv : finiteWeilCanonicalEdgeCenteredSecondMoment r k / n - 1 / 4 =
      (finiteWeilCanonicalEdgeCenteredSecondMoment r k - n / 4) / n := by field_simp
  change |finiteWeilCanonicalEdgeCenteredSecondMoment r k / n - 1 / 4| ≤ 6 * (S / n)
  rw [hdiv, abs_div, abs_of_pos hn]
  calc
    _ ≤ (6 * S) / n := div_le_div_of_nonneg_right hraw hn.le
    _ = _ := by ring

theorem finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_sharp_bound (r t : ℕ) :
    |finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 4| ≤
      6 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  apply finiteWeilCanonicalEdgeCenteredSecondMoment_normalized_sharp_bound
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

theorem tendsto_finiteWeilCanonicalEdgeCenteredSecondMoment_quarter (t : ℕ → ℕ) :
    Tendsto (fun r : ℕ => finiteWeilCanonicalEdgeCenteredSecondMoment r (2 * (r + 1) ^ 2 + t r) /
      ((r + 1 : ℕ) : ℝ)) atTop (𝓝 ((1 : ℝ) / 4)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalEdgeCenteredSecondMoment_quadratic_sharp_bound r (t r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (3 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (3 : ℝ) * 2 = 6 by norm_num] using h

end RHTower
