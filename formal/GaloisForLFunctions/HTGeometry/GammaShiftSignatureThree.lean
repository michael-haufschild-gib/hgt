import GaloisForLFunctions.HTGeometry.GammaShiftSignatureTwo

/-!
# The third signature datum of a unit-scale shift

Feeding the fourth-rung bound `ψ(w) = log w − 1/(2w) − 1/(12 w²) + 1/(120 w⁴) + O(|w|⁻⁵)` into
`w = s + μ` and expanding one order further gives

```text
ψ(s + μ) = log s + (μ − ½)/s + (−μ²/2 + μ/2 − 1/12)/s²
             + (μ³/3 − μ²/2 + μ/6)/s³ + O(|s|⁻⁴).
```

Weighted by `e_k` and summed, the `1/s³` residue is
`(∑_k e_k λ_k³)/3 − (∑_k e_k λ_k²)/2 + (∑_k e_k λ_k)/6`, so the **third power sum** is recovered
from it and the earlier data.  With `power_expansion_eq_zero` the archimedean separation is then
unconditional for four distinct shifts.

All remainders are exact:
`1/(s+μ) = 1/s − μ/s² + μ²/s³ − μ³/(s³(s+μ))` and
`1/(s+μ)² = 1/s² − 2μ/s³ + (3sμ² + 2μ³)/(s³(s+μ)²)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_norm_digamma_shift_expansion_three_le (mu : ℂ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s : ℂ, 0 < s.re → 0 < (s + mu).re → R ≤ ‖s‖ →
      ‖Complex.digamma (s + mu) -
        (Complex.log s + (mu - 1 / 2) / s
          + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2
          + (mu ^ 3 / 3 - mu ^ 2 / 2 + mu / 6) / s ^ 3)‖
        ≤ C / ‖s‖ ^ 4 := by
  set M : ℝ := ‖mu‖ with hMdef
  have hM0 : (0 : ℝ) ≤ M := norm_nonneg mu
  refine ⟨217 + M ^ 4 + 2 * M ^ 3 + M ^ 2, max (4 * M) 4,
    by nlinarith [hM0, pow_nonneg hM0 2, pow_nonneg hM0 3, pow_nonneg hM0 4],
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
  have hE1 : ‖Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)
      - 1 / (120 * w ^ 4)‖ ≤ 216 / ‖s‖ ^ 4 := by
    have h := norm_digammaStirlingDefectFour_le hw hw2
    rw [digammaStirlingDefectFour] at h
    refine le_trans h ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp5 : (‖s‖ / 2) ^ 5 ≤ ‖w‖ ^ 5 := pow_le_pow_left₀ (by linarith) hwlow 5
    nlinarith [hp5, hnorm0, hs4, pow_pos hnorm0 4, pow_pos hwpos 5]
  have hquot : w / s = 1 + mu / s := by rw [hwdef, add_div, div_self hs0]
  have hunorm : ‖mu / s‖ = M / ‖s‖ := by rw [norm_div, hMdef]
  have huhalf : ‖mu / s‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hnorm0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hE2 : ‖Complex.log w - Complex.log s
      - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3)‖ ≤ M ^ 4 / ‖s‖ ^ 4 := by
    have hlogsplit : Complex.log w - Complex.log s = Complex.log (1 + mu / s) := by
      rw [log_sub_log_of_re_pos hw hs, hquot]
    rw [hlogsplit]
    have hbase := norm_log_one_add_sub_taylor_le' (u := mu / s) huhalf (n := 4) (by omega)
    have hsumgen : ∀ x : ℂ, ∑ j ∈ Finset.range 4, (-1 : ℂ) ^ (j + 1) * x ^ j / (j : ℂ)
        = x - x ^ 2 / 2 + x ^ 3 / 3 := by
      intro x
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      norm_num
      ring
    rw [hsumgen (mu / s)] at hbase
    refine le_trans hbase (le_of_eq ?_)
    rw [hunorm, div_pow]
  have hE3 : ‖-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)‖
      ≤ M ^ 3 / ‖s‖ ^ 4 := by
    have hid : -(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)
        = mu ^ 3 / (2 * s ^ 3 * w) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_div, norm_pow, norm_mul, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n, ← hMdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hM0 hM0) hM0)
      (pow_pos hnorm0 3).le) (by linarith : (0 : ℝ) ≤ 2 * ‖w‖ - ‖s‖)]
  have hE4 : ‖-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3)‖
      ≤ (M ^ 2 + M ^ 3) / ‖s‖ ^ 4 := by
    have hid : -(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3)
        = -((3 * s * mu ^ 2 + 2 * mu ^ 3) / (12 * s ^ 3 * w ^ 2)) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖3 * s * mu ^ 2 + 2 * mu ^ 3‖ ≤ 3 * ‖s‖ * M ^ 2 + 2 * M ^ 3 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
      have h3n : ‖(3 : ℂ)‖ = 3 := by norm_num
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h3n, h2n, ← hMdef]
    have hden : ‖s‖ ^ 2 / 4 ≤ ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ ‖s‖ / 2) hwlow 2
      nlinarith [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hLHS : ‖3 * s * mu ^ 2 + 2 * mu ^ 3‖ * ‖s‖ ^ 4
        ≤ (3 * ‖s‖ * M ^ 2 + 2 * M ^ 3) * ‖s‖ ^ 4 :=
      mul_le_mul_of_nonneg_right hnum (pow_pos hnorm0 4).le
    have hRHS : 3 * (M ^ 2 + M ^ 3) * ‖s‖ ^ 5
        ≤ (M ^ 2 + M ^ 3) * (12 * ‖s‖ ^ 3 * ‖w‖ ^ 2) := by
      nlinarith [hden, mul_nonneg (by positivity : (0 : ℝ) ≤ M ^ 2 + M ^ 3)
        (pow_pos hnorm0 3).le]
    have hmid : (3 * ‖s‖ * M ^ 2 + 2 * M ^ 3) * ‖s‖ ^ 4 ≤ 3 * (M ^ 2 + M ^ 3) * ‖s‖ ^ 5 := by
      nlinarith [mul_nonneg (mul_nonneg hM0 hM0) (pow_pos hnorm0 5).le,
        mul_nonneg (mul_nonneg (mul_nonneg hM0 hM0) hM0)
          (by nlinarith [hs4, pow_pos hnorm0 4] : (0 : ℝ) ≤ ‖s‖ ^ 5 - ‖s‖ ^ 4)]
    linarith
  have hE5 : ‖1 / (120 * w ^ 4)‖ ≤ 1 / ‖s‖ ^ 4 := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have h120 : ‖(120 : ℂ)‖ = 120 := by norm_num
    rw [h120]
    have hp4 : (‖s‖ / 2) ^ 4 ≤ ‖w‖ ^ 4 := pow_le_pow_left₀ (by linarith) hwlow 4
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hp4, pow_pos hnorm0 4]
  have hsplit : Complex.digamma w -
      (Complex.log s + (mu - 1 / 2) / s + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2
        + (mu ^ 3 / 3 - mu ^ 2 / 2 + mu / 6) / s ^ 3)
      = (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)
          - 1 / (120 * w ^ 4))
        + (Complex.log w - Complex.log s - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3))
        + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3))
        + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3))
        + 1 / (120 * w ^ 4) := by
    field_simp
    ring
  rw [hsplit]
  have htotal : ‖(Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)
        - 1 / (120 * w ^ 4))
      + (Complex.log w - Complex.log s - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3))
      + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3))
      + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3))
      + 1 / (120 * w ^ 4)‖
      ≤ 216 / ‖s‖ ^ 4 + M ^ 4 / ‖s‖ ^ 4 + M ^ 3 / ‖s‖ ^ 4 + (M ^ 2 + M ^ 3) / ‖s‖ ^ 4
        + 1 / ‖s‖ ^ 4 := by
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hE5
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add ?_ hE4
    refine le_trans (norm_add_le _ _) ?_
    refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hE1 hE2)) hE3
  refine le_trans htotal (le_of_eq ?_)
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
