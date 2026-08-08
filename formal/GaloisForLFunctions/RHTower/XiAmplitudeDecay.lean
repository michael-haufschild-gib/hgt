import GaloisForLFunctions.RHTower.ProlateDunsterComparisonBridge

/-!
# Decay of the exterior Liouville–Green amplitude and its derivative

The corpus already proves that Dunster's amplitude obeys `A ≤ 2^{1/4} x^{-1/2}` and computes its
derivative in the logarithmic form `A' = A(D/2 - x/(2(x²-s)))`, where `D` is the phase defect, itself
already bounded by `x/(x²-1)`.

Combining those three facts gives the derivative decay `|A'| ≤ 4 x^{-3/2}`: away from the endpoint
both terms of the logarithmic derivative are `O(1/x)`, and the amplitude contributes its own
`x^{-1/2}`.  Together with the amplitude bound this is the pair of estimates that an exterior
oscillatory integration by parts consumes.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem sqrt_sqrt_two_le_two : Real.sqrt (Real.sqrt 2) ≤ 2 := by
  have h1 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h2 : Real.sqrt (Real.sqrt 2) ^ 2 = Real.sqrt 2 := Real.sq_sqrt (Real.sqrt_nonneg 2)
  nlinarith [h2, Real.sqrt_nonneg (Real.sqrt 2), h1]

/-- The amplitude decay in the form the exterior primitive consumes. -/
theorem abs_xiAmplitude_le_four {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |xiAmplitude s x| ≤ 4 / Real.sqrt x := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hA : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx1
  have hAle : xiAmplitude s x ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x := xiAmplitude_le hs0 hs1 hx1
  rw [abs_of_pos hA]
  refine le_trans hAle ?_
  gcongr
  linarith [sqrt_sqrt_two_le_two]

/-- **The derivative decay of the exterior amplitude.**  Both terms of the logarithmic derivative
are `O(1/x)` away from the endpoint, so the derivative inherits the amplitude's `x^{-1/2}` with one
extra power. -/
theorem abs_xiAmplitudeDeriv_le {s x : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 2 ≤ x) :
    |xiAmplitudeDeriv s x| ≤ 4 / (x * Real.sqrt x) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hA : 0 < xiAmplitude s x := xiAmplitude_pos hs0 hs1 hx1
  have hAle : xiAmplitude s x ≤ Real.sqrt (Real.sqrt 2) / Real.sqrt x := xiAmplitude_le hs0 hs1 hx1
  have hA2 : xiAmplitude s x ≤ 2 / Real.sqrt x := by
    refine le_trans hAle ?_
    gcongr
    exact sqrt_sqrt_two_le_two
  have hdef := abs_phaseLogDefect_le_far hs0 hs1 hx1
  have h1 : |phaseLogDefect s x| / 2 ≤ 2 / (3 * x) := by
    have hstep : x / (x ^ 2 - 1) / 2 ≤ 2 / (3 * x) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx, hx0, hd]
    linarith [hdef, hstep]
  have h2 : |x / (2 * (x ^ 2 - s))| ≤ 4 / (7 * x) := by
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ x / (2 * (x ^ 2 - s)))]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hx, hx0, hs1, hn]
  have hbr : |phaseLogDefect s x / 2 - x / (2 * (x ^ 2 - s))| ≤ 2 / x := by
    have htri : |phaseLogDefect s x / 2 - x / (2 * (x ^ 2 - s))|
        ≤ |phaseLogDefect s x / 2| + |x / (2 * (x ^ 2 - s))| := abs_sub _ _
    have habs : |phaseLogDefect s x / 2| = |phaseLogDefect s x| / 2 := by
      rw [abs_div]
      norm_num
    have hsum : 2 / (3 * x) + 4 / (7 * x) ≤ 2 / x := by
      rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [hx0]
    rw [habs] at htri
    linarith [htri, h1, h2, hsum]
  rw [xiAmplitudeDeriv, abs_mul, abs_of_pos hA]
  have hfin : xiAmplitude s x * |phaseLogDefect s x / 2 - x / (2 * (x ^ 2 - s))|
      ≤ (2 / Real.sqrt x) * (2 / x) :=
    mul_le_mul hA2 hbr (abs_nonneg _) (by positivity)
  refine le_trans hfin (le_of_eq ?_)
  field_simp
  ring

end GaloisForLFunctions.RHTower
