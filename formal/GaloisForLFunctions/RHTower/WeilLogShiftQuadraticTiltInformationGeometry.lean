import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The information separation of subcritical quadratic tilts has one effective parameter. -/

noncomputable section

namespace RHTower

def finiteWeilQuadraticTiltEntropy (s S : {s : ℝ // s < 2}) : ℝ :=
  ((2 - S.val) / (2 - s.val) - 1 - Real.log ((2 - S.val) / (2 - s.val))) / 2

theorem finiteWeilQuadraticTiltEntropy_nonneg (s S : {s : ℝ // s < 2}) :
    0 ≤ finiteWeilQuadraticTiltEntropy s S := by
  have h := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr S.property) (sub_pos.mpr s.property))
  unfold finiteWeilQuadraticTiltEntropy
  linarith

theorem finiteWeilQuadraticTiltEntropy_eq_zero_iff (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltEntropy s S = 0 ↔ s.val = S.val := by
  have hs : 0 < 2 - s.val := sub_pos.mpr s.property
  have hS : 0 < 2 - S.val := sub_pos.mpr S.property
  constructor
  · intro h
    by_contra hne
    have hr : (2 - S.val) / (2 - s.val) ≠ 1 := by
      intro hr
      have he := (div_eq_one_iff_eq hs.ne').mp hr
      apply hne
      linarith
    have hlt := Real.log_lt_sub_one_of_pos (div_pos hS hs) hr
    unfold finiteWeilQuadraticTiltEntropy at h
    linarith
  · intro h
    unfold finiteWeilQuadraticTiltEntropy
    rw [h, div_self hS.ne']
    simp

theorem finiteWeilQuadraticTiltEntropy_pos_iff (s S : {s : ℝ // s < 2}) :
    0 < finiteWeilQuadraticTiltEntropy s S ↔ s.val ≠ S.val := by
  rw [lt_iff_le_and_ne]
  simp only [finiteWeilQuadraticTiltEntropy_nonneg, true_and, ne_eq,
    eq_comm (a := (0 : ℝ)), finiteWeilQuadraticTiltEntropy_eq_zero_iff]

theorem finiteWeilQuadraticTiltEntropy_partition_form (s S : {s : ℝ // s < 2}) :
    (s.val - S.val) / (4 - 2 * s.val) - Real.log (Real.sqrt (2 / (2 - s.val))) +
      Real.log (Real.sqrt (2 / (2 - S.val))) = finiteWeilQuadraticTiltEntropy s S := by
  have hs : 0 < 2 - s.val := sub_pos.mpr s.property
  have hS : 0 < 2 - S.val := sub_pos.mpr S.property
  have hden : 4 - 2 * s.val = 2 * (2 - s.val) := by ring
  rw [hden]
  unfold finiteWeilQuadraticTiltEntropy
  rw [Real.log_sqrt (by positivity), Real.log_sqrt (by positivity),
    Real.log_div (by norm_num) hs.ne', Real.log_div (by norm_num) hS.ne',
    Real.log_div hS.ne' hs.ne']
  field_simp [hs.ne', hS.ne']
  ring

theorem finiteWeilQuadraticTiltEntropy_swap_add (s S : {s : ℝ // s < 2}) :
    finiteWeilQuadraticTiltEntropy s S + finiteWeilQuadraticTiltEntropy S s =
      (s.val - S.val) ^ 2 / (2 * (2 - s.val) * (2 - S.val)) := by
  have hs : 2 - s.val ≠ 0 := (sub_pos.mpr s.property).ne'
  have hS : 2 - S.val ≠ 0 := (sub_pos.mpr S.property).ne'
  unfold finiteWeilQuadraticTiltEntropy
  rw [Real.log_div hS hs, Real.log_div hs hS]
  field_simp [hs, hS]
  ring

end RHTower
