import GaloisForLFunctions.RHTower.XiWardEdgeL2CrossKernel
import GaloisForLFunctions.RHTower.XiWardZeroFreeMarginPrimeLogSampling

/-!
# Margin-quantified edge energy floors and height-window clearing

Every strict-right pair `λ = a + ib` obeys `a ≤ 1/2 − m(b)` for the
zero-free margin `m`, so its edge quadratic-energy floor `4π/(a + 1/2)`
sharpens to `4π/(1 − m(b))`, strictly above the relaxed budget
`4π(1 + m(b))` because `(1−m)(1+m) < 1`.  Consequences: the total edge
quadratic energy is either `0` or strictly above `4π` (no intermediate
value), and an energy certificate at budget `4π(1 + m(T))` clears the
strict-right divisor of all pairs of height at most `T`.
-/

open Complex MeasureTheory Real

namespace RHTower

noncomputable section

/-- Margin-sharpened per-pair floor: a strict-right pair of height `b`
forces edge quadratic energy at least `4π/(1 − m(b))`. -/
theorem margin_floor_le_xiWardEdgeQuadEnergy (q : XiRightUpperZeroCopy) :
    ENNReal.ofReal (4 * π /
      (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im)) ≤
    xiWardEdgeQuadEnergy := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hm := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hmh := xiWardZeroFreeMargin_le_half (xiRightCenteredZero q.1).im
  have hM := xiRightCenteredZero_re_le_half_sub_margin q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hx1m : (xiRightCenteredZero q.1).re + 1 / 2 ≤
      1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im := by linarith
  have hkey : 4 * π /
      (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) ≤
      4 * π / ((xiRightCenteredZero q.1).re + 1 / 2) :=
    div_le_div₀ (by positivity) le_rfl hx hx1m
  exact (ENNReal.ofReal_le_ofReal hkey).trans
    (lintegral_normSq_continuedXiAntiCausalWardResponse_edge_lower q)

/-- The margin-sharpened floor strictly exceeds the margin-relaxed budget:
`4π(1 + m) < 4π/(1 − m)` for the positive margin `m`. -/
theorem fourPi_margin_budget_lt_floor (y : ℝ) :
    4 * π * (1 + xiWardZeroFreeMargin y) <
      4 * π / (1 - xiWardZeroFreeMargin y) := by
  have hm := xiWardZeroFreeMargin_pos y
  have hmh := xiWardZeroFreeMargin_le_half y
  have h1m : 0 < 1 - xiWardZeroFreeMargin y := by linarith
  rw [lt_div_iff₀ h1m]
  nlinarith [pi_pos, mul_pos hm hm, mul_pos pi_pos (mul_pos hm hm)]

/-- **Edge energy dichotomy**: the total edge quadratic energy of the
continued Ward response is either exactly `0` or strictly above `4π`.
No intermediate value is attainable. -/
theorem xiWardEdgeQuadEnergy_eq_zero_or_fourPi_lt :
    xiWardEdgeQuadEnergy = 0 ∨
      ENNReal.ofReal (4 * π) < xiWardEdgeQuadEnergy := by
  rcases isEmpty_or_nonempty XiRightUpperZeroCopy with hempty | ⟨⟨q⟩⟩
  · left
    have hzero : ∀ t : ℝ,
        continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)) =
          0 := by
      intro t
      have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
        norm_num [Complex.add_re, Complex.mul_re]
      rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
        tsum_empty]
    unfold xiWardEdgeQuadEnergy
    rw [show (fun t : ℝ => ENNReal.ofReal (Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))))
        = fun _ : ℝ => (0 : ENNReal) from funext fun t => by
      rw [hzero t]; simp]
    exact lintegral_zero
  · right
    have hm := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
    have hmh := xiWardZeroFreeMargin_le_half (xiRightCenteredZero q.1).im
    have h1m : 0 < 1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
      by linarith
    have hstrict : 4 * π < 4 * π /
        (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) := by
      rw [lt_div_iff₀ h1m]
      nlinarith [pi_pos]
    calc ENNReal.ofReal (4 * π)
        < ENNReal.ofReal (4 * π /
            (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im)) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          exact hstrict
      _ ≤ xiWardEdgeQuadEnergy := margin_floor_le_xiWardEdgeQuadEnergy q
    
/-- **Height-window clearing law**: an edge energy certificate at the
margin-relaxed budget `4π(1 + m(T))` clears the strict-right divisor of
every pair of height at most `T`. -/
theorem height_lt_abs_im_of_xiWardEdgeQuadEnergy_le {T : ℝ}
    (hlaw : xiWardEdgeQuadEnergy ≤
      ENNReal.ofReal (4 * π * (1 + xiWardZeroFreeMargin T)))
    (q : XiRightUpperZeroCopy) :
    T < |(xiRightCenteredZero q.1).im| := by
  by_contra hle
  push Not at hle
  have hT0 : 0 ≤ T := le_trans (abs_nonneg _) hle
  have hanti : xiWardZeroFreeMargin T ≤
      xiWardZeroFreeMargin (xiRightCenteredZero q.1).im := by
    apply xiWardZeroFreeMargin_anti
    rwa [abs_of_nonneg hT0]
  have hmT := xiWardZeroFreeMargin_pos T
  have hchain := (margin_floor_le_xiWardEdgeQuadEnergy q).trans hlaw
  rw [ENNReal.ofReal_le_ofReal_iff
    (by nlinarith [pi_pos] : (0 : ℝ) ≤
      4 * π * (1 + xiWardZeroFreeMargin T))] at hchain
  have hmb := xiWardZeroFreeMargin_pos (xiRightCenteredZero q.1).im
  have hmbh := xiWardZeroFreeMargin_le_half (xiRightCenteredZero q.1).im
  have h1mb : 0 < 1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im :=
    by linarith
  have h1mT : 0 < 1 - xiWardZeroFreeMargin T := by
    have := xiWardZeroFreeMargin_le_half T
    linarith
  have hTfloor : 4 * π / (1 - xiWardZeroFreeMargin T) ≤
      4 * π / (1 - xiWardZeroFreeMargin (xiRightCenteredZero q.1).im) :=
    div_le_div₀ (by positivity) le_rfl h1mb (by linarith)
  have hbudget := fourPi_margin_budget_lt_floor T
  linarith

end

end RHTower
