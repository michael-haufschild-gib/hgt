import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! An overlap kernel for positive precisions, with exact separation geometry. -/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

def positivePrecisionOverlap (x y : {x : ℝ // 0 < x}) : ℝ :=
  Real.sqrt (2 * Real.sqrt (x.val * y.val) / (x.val + y.val))

theorem positivePrecisionOverlap_pos (x y : {x : ℝ // 0 < x}) :
    0 < positivePrecisionOverlap x y := by
  have hx := x.property
  have hy := y.property
  unfold positivePrecisionOverlap
  positivity

theorem positivePrecisionOverlap_fourth (x y : {x : ℝ // 0 < x}) :
    positivePrecisionOverlap x y ^ 4 = 4 * x.val * y.val / (x.val + y.val) ^ 2 := by
  have hx := x.property
  have hy := y.property
  unfold positivePrecisionOverlap
  calc
    _ = (Real.sqrt (2 * Real.sqrt (x.val * y.val) / (x.val + y.val)) ^ 2) ^ 2 := by ring
    _ = (2 * Real.sqrt (x.val * y.val) / (x.val + y.val)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]
    _ = _ := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring

theorem positivePrecisionOverlap_le_one (x y : {x : ℝ // 0 < x}) :
    positivePrecisionOverlap x y ≤ 1 := by
  apply (pow_le_pow_iff_left₀ (positivePrecisionOverlap_pos x y).le
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [positivePrecisionOverlap_fourth, one_pow]
  have hden : 0 < (x.val + y.val) ^ 2 := by positivity [x.property, y.property]
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg (x.val - y.val)]

theorem positivePrecisionOverlap_eq_one_iff (x y : {x : ℝ // 0 < x}) :
    positivePrecisionOverlap x y = 1 ↔ x.val = y.val := by
  have hx := x.property
  have hy := y.property
  have hden : (x.val + y.val) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have he : 4 * x.val * y.val / (x.val + y.val) ^ 2 = 1 := by
      rw [← positivePrecisionOverlap_fourth, h, one_pow]
    have he' := (div_eq_one_iff_eq hden).mp he
    have hs : (x.val - y.val) ^ 2 = 0 := by nlinarith
    have hz : x.val - y.val = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs
    exact sub_eq_zero.mp hz
  · intro h
    apply (pow_left_inj₀ (positivePrecisionOverlap_pos x y).le
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (4 : ℕ) ≠ 0)).mp
    rw [positivePrecisionOverlap_fourth, one_pow]
    apply (div_eq_one_iff_eq hden).mpr
    rw [h]
    ring

theorem positivePrecisionOverlap_lt_one_iff (x y : {x : ℝ // 0 < x}) :
    positivePrecisionOverlap x y < 1 ↔ x.val ≠ y.val := by
  rw [lt_iff_le_and_ne, and_iff_right (positivePrecisionOverlap_le_one x y)]
  exact not_congr (positivePrecisionOverlap_eq_one_iff x y)

theorem positivePrecisionOverlap_jeffreys (x y : {x : ℝ // 0 < x}) :
    positivePrecisionOverlap x y ^ 4 *
      (1 + ((x.val - y.val) ^ 2 / (2 * x.val * y.val)) / 2) = 1 := by
  rw [positivePrecisionOverlap_fourth]
  have hsum : x.val + y.val ≠ 0 := (add_pos x.property y.property).ne'
  field_simp [x.property.ne', y.property.ne', hsum]
  ring

end GaloisForLFunctions.HTGeometry
