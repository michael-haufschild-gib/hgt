import GaloisForLFunctions.ArithmeticElectrostatics.TheLogarithmicDepthThresholdIsALimit

/-!
# Power moments do not determine logarithmic majorization

The abstract squared-depth list `(2,2)` has every real power sum bounded by
the list `(4,1/2,1/2)`. Its logarithmic threshold sum at `1/2` is
strictly larger. Thus power budgets together with decreasing cardinality
cannot recover the logarithmic threshold law.
-/

namespace GaloisForLFunctions.ArithmeticElectrostatics
noncomputable section

private theorem two_mul_le_sq_add_two_inv {x : ℝ} (hx : 0 < x) :
    2 * x ≤ x ^ 2 + 2 * x⁻¹ := by
  by_cases hle : x ≤ 2
  · have heq : (x ^ 2 + 2 * x⁻¹ - 2 * x) * x = x * (x - 1) ^ 2 + 2 - x := by
      calc
        _ = x * (x - 1) ^ 2 + 2 * (x * x⁻¹) - x := by ring
        _ = _ := by rw [mul_inv_cancel₀ hx.ne']; ring
    have hn : 0 ≤ (x ^ 2 + 2 * x⁻¹ - 2 * x) * x := by
      rw [heq]
      nlinarith only [mul_nonneg hx.le (sq_nonneg (x - 1)), hle]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right hx).mp hn)
  · have hge : 2 ≤ x := (lt_of_not_ge hle).le
    have hsq : 2 * x ≤ x ^ 2 := by
      nlinarith only [mul_nonneg hx.le (sub_nonneg.mpr hge)]
    exact hsq.trans (le_add_of_nonneg_right (mul_nonneg zero_le_two (inv_nonneg.mpr hx.le)))

/-- Every real power sum of `(2,2)` is bounded by that of `(4,1/2,1/2)`. -/
theorem equal_depths_power_moments_le_split_depths (q : ℝ) :
    2 * (2 : ℝ) ^ q ≤ (4 : ℝ) ^ q + 2 * (1 / 2 : ℝ) ^ q := by
  have hfour : (4 : ℝ) ^ q = ((2 : ℝ) ^ q) ^ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
    ring
  have hhalf : (1 / 2 : ℝ) ^ q = ((2 : ℝ) ^ q)⁻¹ := by
    rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, one_div]
  rw [hfour, hhalf]
  exact two_mul_le_sq_add_two_inv (Real.rpow_pos_of_pos (by norm_num) q)

/-- The two equal depths exceed the split list's threshold budget by exactly `log 2`. -/
theorem equal_depths_logarithmicThreshold_deficit :
    2 * logarithmicDepthThreshold (1 / 2) 2 -
      (logarithmicDepthThreshold (1 / 2) 4 + 2 * logarithmicDepthThreshold (1 / 2) (1 / 2)) =
        Real.log 2 := by
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have height : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), hfour]
    ring
  have htwo : logarithmicDepthThreshold (1 / 2) 2 = Real.log 4 := by
    norm_num [logarithmicDepthThreshold]
  have hlarge : logarithmicDepthThreshold (1 / 2) 4 = Real.log 8 := by
    norm_num [logarithmicDepthThreshold]
  have hsmall : logarithmicDepthThreshold (1 / 2) (1 / 2) = 0 :=
    logarithmicDepthThreshold_eq_zero (by norm_num) le_rfl
  rw [htwo, hlarge, hsmall, hfour, height]
  ring

/-- The same two lists reverse the logarithmic threshold comparison at `a=1/2`. -/
theorem equal_depths_logarithmicThreshold_gt_split_depths :
    logarithmicDepthThreshold (1 / 2) 4 + 2 * logarithmicDepthThreshold (1 / 2) (1 / 2) <
      2 * logarithmicDepthThreshold (1 / 2) 2 := by
  have h := equal_depths_logarithmicThreshold_deficit
  have hp := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith only [h, hp]

#print axioms equal_depths_power_moments_le_split_depths
#print axioms equal_depths_logarithmicThreshold_gt_split_depths

end
end GaloisForLFunctions.ArithmeticElectrostatics
