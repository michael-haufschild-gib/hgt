import GaloisForLFunctions.HTGeometry.GammaStirlingFourthRung
import GaloisForLFunctions.HTGeometry.GammaAffineStirlingSignature

/-!
# The second signature datum of a unit-scale shift

The normal form of `finite-archimedean-gamma-product-boundary-law` has Gamma factors
`Γ(s + λ_k)^{e_k}`: every scale is `1` and the `λ_k` are shifts.  Feeding the second-rung bound
`ψ(w) = log w − 1/(2w) − 1/(12 w²) + O(|w|⁻⁴)` into `w = s + μ` and expanding in `1/s` gives

```text
ψ(s + μ) = log s + (μ − ½)/s + (−μ²/2 + μ/2 − 1/12)/s² + O(|s|⁻³).
```

Weighted by `e_k` and summed, the `1/s²` residue is
`−(∑_k e_k λ_k²)/2 + (∑_k e_k λ_k)/2 − (∑_k e_k)/12`, so the **second power sum** `∑_k e_k λ_k²` is
recovered from it once the two earlier data `∑_k e_k` and `∑_k e_k λ_k` are known.

Every remainder is exact: `1/(s+μ) = 1/s − μ/s² + μ²/(s²(s+μ))` and
`1/(s+μ)² = 1/s² − (2sμ+μ²)/(s²(s+μ)²)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_norm_digamma_shift_expansion_two_le (mu : ℂ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s : ℂ, 0 < s.re → 0 < (s + mu).re → R ≤ ‖s‖ →
      ‖Complex.digamma (s + mu) -
        (Complex.log s + (mu - 1 / 2) / s
          + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2)‖
        ≤ C / ‖s‖ ^ 3 := by
  set M : ℝ := ‖mu‖ with hMdef
  have hM0 : (0 : ℝ) ≤ M := norm_nonneg mu
  refine ⟨48 + M ^ 3 + 2 * M ^ 2 + 2 * M, max (4 * M) 4,
    by nlinarith [hM0, pow_nonneg hM0 2, pow_nonneg hM0 3],
    le_max_of_le_right (by norm_num), fun s hs hw hR => ?_⟩
  have hs4 : (4 : ℝ) ≤ ‖s‖ := le_trans (le_max_right _ _) hR
  have hsM : 4 * M ≤ ‖s‖ := le_trans (le_max_left _ _) hR
  have hnorm0 : (0 : ℝ) < ‖s‖ := by linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hnorm0
    simp at hnorm0
  set w : ℂ := s + mu with hwdef
  have hwlow : ‖s‖ / 2 ≤ ‖w‖ := by
    have h := norm_sub_le (s + mu) mu
    rw [add_sub_cancel_right] at h
    rw [hwdef]
    rw [← hMdef] at h
    linarith
  have hwpos : (0 : ℝ) < ‖w‖ := by
    have : (0 : ℝ) < ‖s‖ / 2 := by linarith
    linarith
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hwpos
    simp at hwpos
  have hw2 : (2 : ℝ) ≤ ‖w‖ := by linarith
  have hsm : s + mu ≠ 0 := by
    rw [← hwdef]
    exact hwne
  -- (1) the second-rung Stirling bound at `w`
  have hE1 : ‖Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)‖
      ≤ 48 / ‖s‖ ^ 3 := by
    have h := norm_digammaStirlingDefectTwo_le' hw hw2
    rw [digammaStirlingDefectTwo] at h
    refine le_trans h ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp4 : (‖s‖ / 2) ^ 4 ≤ ‖w‖ ^ 4 := pow_le_pow_left₀ (by linarith) hwlow 4
    nlinarith [hp4, hnorm0, hs4, pow_pos hnorm0 3, pow_pos hwpos 4]
  -- (2) the logarithm
  have hquot : w / s = 1 + mu / s := by rw [hwdef, add_div, div_self hs0]
  have hunorm : ‖mu / s‖ = M / ‖s‖ := by rw [norm_div, hMdef]
  have huhalf : ‖mu / s‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hnorm0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hE2 : ‖Complex.log w - Complex.log s - (mu / s - (mu / s) ^ 2 / 2)‖
      ≤ M ^ 3 / ‖s‖ ^ 3 := by
    have hlogsplit : Complex.log w - Complex.log s = Complex.log (1 + mu / s) := by
      rw [log_sub_log_of_re_pos hw hs, hquot]
    rw [hlogsplit]
    have hbase := norm_log_one_add_sub_taylor_le' (u := mu / s) huhalf (n := 3) (by omega)
    have hsumgen : ∀ x : ℂ, ∑ j ∈ Finset.range 3, (-1 : ℂ) ^ (j + 1) * x ^ j / (j : ℂ)
        = x - x ^ 2 / 2 := by
      intro x
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
      ring
    rw [hsumgen (mu / s)] at hbase
    refine le_trans hbase (le_of_eq ?_)
    rw [hunorm, div_pow]
  -- (3) the reciprocal
  have hE3 : ‖-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2)‖ ≤ M ^ 2 / ‖s‖ ^ 3 := by
    have hid : -(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2)
        = -(mu ^ 2 / (2 * s ^ 2 * w)) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_pow, norm_mul, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n, ← hMdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hM0 hM0) (pow_pos hnorm0 2).le)
      (by linarith : (0 : ℝ) ≤ 2 * ‖w‖ - ‖s‖)]
  -- (4) the square
  have hE4 : ‖-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2)‖ ≤ (2 * M + M ^ 2) / ‖s‖ ^ 3 := by
    have hid : -(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2)
        = (2 * s * mu + mu ^ 2) / (12 * s ^ 2 * w ^ 2) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖2 * s * mu + mu ^ 2‖ ≤ 2 * ‖s‖ * M + M ^ 2 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_pow]
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h2n, ← hMdef]
    have hden : ‖s‖ ^ 2 / 4 ≤ ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ ‖s‖ / 2) hwlow 2
      nlinarith [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hLHS : ‖2 * s * mu + mu ^ 2‖ * ‖s‖ ^ 3 ≤ (2 * ‖s‖ * M + M ^ 2) * ‖s‖ ^ 3 :=
      mul_le_mul_of_nonneg_right hnum (pow_pos hnorm0 3).le
    have hRHS : 3 * (2 * M + M ^ 2) * ‖s‖ ^ 4 ≤ (2 * M + M ^ 2) * (12 * ‖s‖ ^ 2 * ‖w‖ ^ 2) := by
      nlinarith [hden, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M + M ^ 2)
        (pow_pos hnorm0 2).le]
    have hmid : (2 * ‖s‖ * M + M ^ 2) * ‖s‖ ^ 3 ≤ 3 * (2 * M + M ^ 2) * ‖s‖ ^ 4 := by
      nlinarith [mul_nonneg (mul_nonneg hM0 hM0) (pow_pos hnorm0 3).le,
        mul_nonneg hM0 (pow_pos hnorm0 4).le, hs4, hnorm0,
        mul_nonneg (mul_nonneg hM0 hM0) (by nlinarith [hs4, pow_pos hnorm0 3] :
          (0 : ℝ) ≤ ‖s‖ ^ 4 - ‖s‖ ^ 3)]
    linarith
  -- assemble
  have hsplit : Complex.digamma w -
      (Complex.log s + (mu - 1 / 2) / s + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2)
      = (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2))
        + (Complex.log w - Complex.log s - (mu / s - (mu / s) ^ 2 / 2))
        + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2))
        + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2)) := by
    field_simp
    ring
  rw [hsplit]
  have htotal : ‖(Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2))
      + (Complex.log w - Complex.log s - (mu / s - (mu / s) ^ 2 / 2))
      + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2))
      + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2))‖
      ≤ 48 / ‖s‖ ^ 3 + M ^ 3 / ‖s‖ ^ 3 + M ^ 2 / ‖s‖ ^ 3 + (2 * M + M ^ 2) / ‖s‖ ^ 3 := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hE4
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hE1 hE2)) hE3
  refine le_trans htotal (le_of_eq ?_)
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
