import GaloisForLFunctions.RHTower.ProlateDunsterComparisonBridge

/-!
# The Liouville amplitude is a half-power symbol

Dunster's exterior amplitude satisfies `A_s(x) ≤ 2^{1/4}/√x`, and its derivative

```text
A_s'(x) = A_s(x)·( P_s(x)/2 − x/(2(x² − s)) )
```

carries one extra power of `x`, because both `|P_s(x)| ≤ x/(x²−1)` and `x/(x²−s)` are `O(1/x)` on
`x ≥ 2`.  So on the exterior ray beyond the second dilation the amplitude lies in the half-power
symbol class

```text
|A| ≤ 2/√x ,      |A'| ≤ 3/(x√x) ,
```

which is exactly the first of the three numerical inputs a two-branch symbol record needs.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The amplitude is a half-power symbol on the exterior ray. -/
theorem abs_xiAmplitude_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    |xiAmplitude s x| ≤ 2 / Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hpos := xiAmplitude_pos hs0 hs1 hx
  rw [abs_of_pos hpos]
  refine (xiAmplitude_le hs0 hs1 hx).trans ?_
  have h32 : Real.sqrt (Real.sqrt 2) ≤ 2 := by
    have h2 : Real.sqrt 2 ≤ 4 := by
      rw [show (4 : ℝ) = Real.sqrt (4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    calc Real.sqrt (Real.sqrt 2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h2
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 from by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  gcongr

/-- The logarithmic factor of the amplitude derivative is `O(1/x)` beyond the second dilation. -/
theorem abs_xiAmplitude_logFactor_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |phaseLogDefect s x / 2 - x / (2 * (x ^ 2 - s))| ≤ 26 / (21 * x) := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hfar := abs_phaseLogDefect_le_far hs0 hs1 hx1
  have hbig : x / (x ^ 2 - 1) ≤ 4 / (3 * x) := by
    rw [div_le_div_iff₀ hd (by positivity)]
    nlinarith
  have hsecond : x / (2 * (x ^ 2 - s)) ≤ 4 / (7 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsecond0 : (0 : ℝ) ≤ x / (2 * (x ^ 2 - s)) := by positivity
  have hstep : |phaseLogDefect s x / 2 - x / (2 * (x ^ 2 - s))|
      ≤ |phaseLogDefect s x| / 2 + x / (2 * (x ^ 2 - s)) := by
    have h := abs_sub (phaseLogDefect s x / 2) (x / (2 * (x ^ 2 - s)))
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))] at h
    rw [abs_of_nonneg hsecond0] at h
    exact h
  have hid : 4 / (3 * x) / 2 + 4 / (7 * x) = 26 / (21 * x) := by
    field_simp
    ring
  have hhalf : |phaseLogDefect s x| / 2 ≤ 4 / (3 * x) / 2 := by
    have := le_trans hfar hbig
    linarith
  linarith [hstep, hhalf, hsecond, hid.le, hid.ge]

/-- **The amplitude derivative is a half-power symbol.** -/
theorem abs_xiAmplitudeDeriv_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |xiAmplitudeDeriv s x| ≤ 3 / (x * Real.sqrt x) := by
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hamp := abs_xiAmplitude_le hs0 hs1 hx1
  have hlog := abs_xiAmplitude_logFactor_le hs0 hs1 hx
  have hprod : |xiAmplitudeDeriv s x| ≤ (2 / Real.sqrt x) * (26 / (21 * x)) := by
    rw [xiAmplitudeDeriv, abs_mul]
    exact mul_le_mul hamp hlog (abs_nonneg _) (by positivity)
  have hval : (2 : ℝ) / Real.sqrt x * (26 / (21 * x)) = (52 / 21) / (x * Real.sqrt x) := by
    field_simp
    ring
  have hmono : (52 : ℝ) / 21 / (x * Real.sqrt x) ≤ 3 / (x * Real.sqrt x) := by
    have hden : (0 : ℝ) < x * Real.sqrt x := by positivity
    rw [div_le_div_iff₀ hden hden]
    nlinarith [hden]
  rw [hval] at hprod
  exact hprod.trans hmono

end GaloisForLFunctions.RHTower

end
