import GaloisForLFunctions.HTGeometry.GammaShiftSignatureThree

/-!
# The fourth signature datum of a unit-scale shift

One order further, from the same fourth-rung Stirling bound:

```text
ψ(s + μ) = log s + (μ − ½)/s + (−μ²/2 + μ/2 − 1/12)/s² + (μ³/3 − μ²/2 + μ/6)/s³
             + (−μ⁴/4 + μ³/2 − μ²/4 + 1/120)/s⁴ + O(|s|⁻⁵).
```

Weighted by `e_k` and summed, the `1/s⁴` residue is
`−(∑ e_k λ_k⁴)/4 + (∑ e_k λ_k³)/2 − (∑ e_k λ_k²)/4 + (∑ e_k)/120`, so the **fourth power sum** is
recovered and the archimedean separation becomes unconditional for five distinct shifts.

The last remainder is handled by *factoring* rather than expanding:
`s⁴ − w⁴ = −μ (s + w)(s² + w²)`, which with `‖s‖/2 ≤ ‖w‖ ≤ (5/4)‖s‖` needs only three easy
estimates instead of a four-degree chain.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

set_option maxHeartbeats 2000000 in
theorem exists_norm_digamma_shift_expansion_four_le (mu : ℂ) :
    ∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s : ℂ, 0 < s.re → 0 < (s + mu).re → R ≤ ‖s‖ →
      ‖Complex.digamma (s + mu) -
        (Complex.log s + (mu - 1 / 2) / s
          + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2
          + (mu ^ 3 / 3 - mu ^ 2 / 2 + mu / 6) / s ^ 3
          + (-(mu ^ 4) / 4 + mu ^ 3 / 2 - mu ^ 2 / 4 + 1 / 120) / s ^ 4)‖
        ≤ C / ‖s‖ ^ 5 := by
  set M : ℝ := ‖mu‖ with hMdef
  have hM0 : (0 : ℝ) ≤ M := norm_nonneg mu
  refine ⟨864 + M ^ 5 + 2 * M ^ 4 + 2 * M ^ 3 + M, max (4 * M) 4,
    by nlinarith [hM0, pow_nonneg hM0 3, pow_nonneg hM0 4, pow_nonneg hM0 5],
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
  have hwup : ‖w‖ ≤ 5 / 4 * ‖s‖ := by
    have h := norm_add_le s mu
    rw [← hMdef] at h
    rw [hwdef]
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
      - 1 / (120 * w ^ 4)‖ ≤ 864 / ‖s‖ ^ 5 := by
    have h := norm_digammaStirlingDefectFour_le hw hw2
    rw [digammaStirlingDefectFour] at h
    refine le_trans h ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp5 : (‖s‖ / 2) ^ 5 ≤ ‖w‖ ^ 5 := pow_le_pow_left₀ (by linarith) hwlow 5
    nlinarith [hp5, hnorm0, pow_pos hnorm0 5, pow_pos hwpos 5]
  have hquot : w / s = 1 + mu / s := by rw [hwdef, add_div, div_self hs0]
  have hunorm : ‖mu / s‖ = M / ‖s‖ := by rw [norm_div, hMdef]
  have huhalf : ‖mu / s‖ ≤ 1 / 2 := by
    rw [hunorm, div_le_div_iff₀ hnorm0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hE2 : ‖Complex.log w - Complex.log s
      - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3 - (mu / s) ^ 4 / 4)‖
      ≤ M ^ 5 / ‖s‖ ^ 5 := by
    have hlogsplit : Complex.log w - Complex.log s = Complex.log (1 + mu / s) := by
      rw [log_sub_log_of_re_pos hw hs, hquot]
    rw [hlogsplit]
    have hbase := norm_log_one_add_sub_taylor_le' (u := mu / s) huhalf (n := 5) (by omega)
    have hsumgen : ∀ x : ℂ, ∑ j ∈ Finset.range 5, (-1 : ℂ) ^ (j + 1) * x ^ j / (j : ℂ)
        = x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 := by
      intro x
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
      ring
    rw [hsumgen (mu / s)] at hbase
    refine le_trans hbase (le_of_eq ?_)
    rw [hunorm, div_pow]
  have hE3 : ‖-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)
      - mu ^ 3 / (2 * s ^ 4)‖ ≤ M ^ 4 / ‖s‖ ^ 5 := by
    have hid : -(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)
        - mu ^ 3 / (2 * s ^ 4) = -(mu ^ 4 / (2 * s ^ 4 * w)) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_pow, norm_mul, norm_mul, norm_pow]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n, ← hMdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hM0 4) (pow_pos hnorm0 4).le)
      (by linarith : (0 : ℝ) ≤ 2 * ‖w‖ - ‖s‖)]
  have hE4 : ‖-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3)
      + mu ^ 2 / (4 * s ^ 4)‖ ≤ (2 * M ^ 3 + M ^ 4) / ‖s‖ ^ 5 := by
    have hid : -(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3)
        + mu ^ 2 / (4 * s ^ 4)
        = (4 * s * mu ^ 3 + 3 * mu ^ 4) / (12 * s ^ 4 * w ^ 2) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_div, norm_mul, norm_mul, norm_pow, norm_pow]
    have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
    rw [h12]
    have hnum : ‖4 * s * mu ^ 3 + 3 * mu ^ 4‖ ≤ 4 * ‖s‖ * M ^ 3 + 3 * M ^ 4 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
      have h4n : ‖(4 : ℂ)‖ = 4 := by norm_num
      have h3n : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h4n, h3n, ← hMdef]
    have hden : ‖s‖ ^ 2 / 4 ≤ ‖w‖ ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ ‖s‖ / 2) hwlow 2
      nlinarith [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hLHS : ‖4 * s * mu ^ 3 + 3 * mu ^ 4‖ * ‖s‖ ^ 5
        ≤ (4 * ‖s‖ * M ^ 3 + 3 * M ^ 4) * ‖s‖ ^ 5 :=
      mul_le_mul_of_nonneg_right hnum (pow_pos hnorm0 5).le
    have hRHS : 3 * (2 * M ^ 3 + M ^ 4) * ‖s‖ ^ 6
        ≤ (2 * M ^ 3 + M ^ 4) * (12 * ‖s‖ ^ 4 * ‖w‖ ^ 2) := by
      nlinarith [hden, mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 3 + M ^ 4)
        (pow_pos hnorm0 4).le]
    have hmid : (4 * ‖s‖ * M ^ 3 + 3 * M ^ 4) * ‖s‖ ^ 5
        ≤ 3 * (2 * M ^ 3 + M ^ 4) * ‖s‖ ^ 6 := by
      nlinarith [mul_nonneg (pow_nonneg hM0 3) (pow_pos hnorm0 6).le,
        mul_nonneg (pow_nonneg hM0 4)
          (by nlinarith [hs4, pow_pos hnorm0 5] : (0 : ℝ) ≤ ‖s‖ ^ 6 - ‖s‖ ^ 5)]
    linarith
  have hE5 : ‖1 / (120 * w ^ 4) - 1 / (120 * s ^ 4)‖ ≤ M / ‖s‖ ^ 5 := by
    have hid : 1 / (120 * w ^ 4) - 1 / (120 * s ^ 4)
        = -(mu * ((s + w) * (s ^ 2 + w ^ 2)) / (120 * s ^ 4 * w ^ 4)) := by
      rw [hwdef]
      field_simp
      ring
    rw [hid, norm_neg, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      ← hMdef]
    have h120 : ‖(120 : ℂ)‖ = 120 := by norm_num
    rw [h120]
    have hsw : ‖s + w‖ ≤ 9 / 4 * ‖s‖ := by
      refine le_trans (norm_add_le _ _) ?_
      linarith [hwup]
    have hsq : ‖s ^ 2 + w ^ 2‖ ≤ 3 * ‖s‖ ^ 2 := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_pow, norm_pow]
      nlinarith [hwup, hwpos, hnorm0]
    have hw4 : ‖s‖ ^ 4 / 16 ≤ ‖w‖ ^ 4 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ ‖s‖ / 2) hwlow 4
      nlinarith [this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hLHS : M * ‖s + w‖ * ‖s ^ 2 + w ^ 2‖ * ‖s‖ ^ 5
        ≤ M * (9 / 4 * ‖s‖) * (3 * ‖s‖ ^ 2) * ‖s‖ ^ 5 := by
      have h1 : M * ‖s + w‖ ≤ M * (9 / 4 * ‖s‖) := mul_le_mul_of_nonneg_left hsw hM0
      have hstep1 : M * ‖s + w‖ * ‖s ^ 2 + w ^ 2‖ ≤ M * (9 / 4 * ‖s‖) * (3 * ‖s‖ ^ 2) :=
        mul_le_mul h1 hsq (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right hstep1 (pow_pos hnorm0 5).le
    have hRHS : M * (9 / 4 * ‖s‖) * (3 * ‖s‖ ^ 2) * ‖s‖ ^ 5
        ≤ M * (120 * ‖s‖ ^ 4 * ‖w‖ ^ 4) := by
      have hbase : M * (120 * ‖s‖ ^ 4 * (‖s‖ ^ 4 / 16))
          ≤ M * (120 * ‖s‖ ^ 4 * ‖w‖ ^ 4) := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        nlinarith [hw4, pow_pos hnorm0 4]
      have heq : M * (9 / 4 * ‖s‖) * (3 * ‖s‖ ^ 2) * ‖s‖ ^ 5 = 27 / 4 * (M * ‖s‖ ^ 8) := by
        ring
      have heq2 : M * (120 * ‖s‖ ^ 4 * (‖s‖ ^ 4 / 16)) = 15 / 2 * (M * ‖s‖ ^ 8) := by ring
      rw [heq]
      rw [heq2] at hbase
      linarith [hbase, mul_nonneg hM0 (pow_pos hnorm0 8).le]
    linarith
  have hsplit : Complex.digamma w -
      (Complex.log s + (mu - 1 / 2) / s + (-(mu ^ 2) / 2 + mu / 2 - 1 / 12) / s ^ 2
        + (mu ^ 3 / 3 - mu ^ 2 / 2 + mu / 6) / s ^ 3
        + (-(mu ^ 4) / 4 + mu ^ 3 / 2 - mu ^ 2 / 4 + 1 / 120) / s ^ 4)
      = (Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)
          - 1 / (120 * w ^ 4))
        + (Complex.log w - Complex.log s
            - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3 - (mu / s) ^ 4 / 4))
        + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)
            - mu ^ 3 / (2 * s ^ 4))
        + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3) + mu ^ 2 / (4 * s ^ 4))
        + (1 / (120 * w ^ 4) - 1 / (120 * s ^ 4)) := by
    field_simp
    ring
  rw [hsplit]
  have htotal : ‖(Complex.digamma w - Complex.log w + 1 / (2 * w) + 1 / (12 * w ^ 2)
        - 1 / (120 * w ^ 4))
      + (Complex.log w - Complex.log s
          - (mu / s - (mu / s) ^ 2 / 2 + (mu / s) ^ 3 / 3 - (mu / s) ^ 4 / 4))
      + (-(1 / (2 * w)) + 1 / (2 * s) - mu / (2 * s ^ 2) + mu ^ 2 / (2 * s ^ 3)
          - mu ^ 3 / (2 * s ^ 4))
      + (-(1 / (12 * w ^ 2)) + 1 / (12 * s ^ 2) - mu / (6 * s ^ 3) + mu ^ 2 / (4 * s ^ 4))
      + (1 / (120 * w ^ 4) - 1 / (120 * s ^ 4))‖
      ≤ 864 / ‖s‖ ^ 5 + M ^ 5 / ‖s‖ ^ 5 + M ^ 4 / ‖s‖ ^ 5
        + (2 * M ^ 3 + M ^ 4) / ‖s‖ ^ 5 + M / ‖s‖ ^ 5 := by
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
