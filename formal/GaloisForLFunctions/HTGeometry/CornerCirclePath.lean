import GaloisForLFunctions.HTGeometry.CircleRootPaths

open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A positive circle based in the lower-left quadrant, aligned with four rectangle sides. -/
def cornerCirclePath (r : ℝ) :
    Path (circleMap 0 r (-3 * Real.pi / 4)) (circleMap 0 r (-3 * Real.pi / 4)) where
  toFun t := circleMap 0 r (-3 * Real.pi / 4 + 2 * Real.pi * (t : ℝ))
  continuous_toFun := by unfold circleMap; fun_prop
  source' := by simp
  target' := by
    change circleMap 0 r (-3 * Real.pi / 4 + 2 * Real.pi * (1 : ℝ)) = _
    simpa only [mul_one] using periodic_circleMap 0 r (-3 * Real.pi / 4)

@[simp] theorem cornerCirclePath_apply (r : ℝ) (t : I) :
    cornerCirclePath r t = circleMap 0 r (-3 * Real.pi / 4 + 2 * Real.pi * (t : ℝ)) := rfl

@[simp] theorem norm_cornerCirclePath (r : ℝ) (t : I) : ‖cornerCirclePath r t‖ = |r| :=
  norm_circleMap_zero _ _

/-- During the bottom-side quarter, the circle remains strictly below its center. -/
theorem cornerCirclePath_first_im {r : ℝ} (hr : 0 < r) (t : I) (ht : (t : ℝ) ≤ 1 / 4) :
    (cornerCirclePath r t).im < 0 := by
  rw [cornerCirclePath_apply, circleMap_zero_im]
  apply mul_neg_of_pos_of_neg hr
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]
  · have h := mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) t.property.1
    linarith [Real.pi_pos]

/-- During the right-side quarter, the circle remains strictly right of its center. -/
theorem cornerCirclePath_second_re {r : ℝ} (hr : 0 < r) (t : I)
    (ht0 : 1 / 4 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 1 / 2) :
    0 < (cornerCirclePath r t).re := by
  rw [cornerCirclePath_apply, circleMap_zero_re]
  apply mul_pos hr
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have h := mul_le_mul_of_nonneg_left ht0 (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]
  · have h := mul_le_mul_of_nonneg_left ht1 (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]

/-- During the top-side quarter, the circle remains strictly above its center. -/
theorem cornerCirclePath_third_im {r : ℝ} (hr : 0 < r) (t : I)
    (ht0 : 1 / 2 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    0 < (cornerCirclePath r t).im := by
  rw [cornerCirclePath_apply, circleMap_zero_im]
  apply mul_pos hr
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h := mul_le_mul_of_nonneg_left ht0 (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]
  · have h := mul_le_mul_of_nonneg_left ht1 (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]

/-- During the left-side quarter, the circle remains strictly left of its center. -/
theorem cornerCirclePath_fourth_re {r : ℝ} (hr : 0 < r) (t : I)
    (ht : 3 / 4 ≤ (t : ℝ)) : (cornerCirclePath r t).re < 0 := by
  rw [cornerCirclePath_apply, circleMap_zero_re]
  apply mul_neg_of_pos_of_neg hr
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]
  · have h := mul_le_mul_of_nonneg_left t.property.2 (by positivity : 0 ≤ 2 * Real.pi)
    linarith [Real.pi_pos]

end
end GaloisForLFunctions.HTGeometry
