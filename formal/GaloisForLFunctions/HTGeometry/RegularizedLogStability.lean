import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Stability of regularized logarithmic potentials

A positive regulator bounds the logarithmic derivative of the squared
amplitude variable. The reverse triangle inequality then controls the
potential difference directly by the complex amplitude error.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.HTGeometry

private lemma log_sub_log_le_div_lower {η u v : ℝ} (hη : 0 < η)
    (hu : η ≤ u) (hv : η ≤ v) (hvu : v ≤ u) :
    Real.log u - Real.log v ≤ (u - v) / η := by
  have hu0 := hη.trans_le hu
  have hv0 := hη.trans_le hv
  have h := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
  rw [Real.log_div hu0.ne' hv0.ne'] at h
  have he : u / v - 1 = (u - v) / v := by field_simp [hv0.ne']
  rw [he] at h
  exact h.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hvu) hη hv)

/-- A positive lower bound controls logarithmic sensitivity without a zero-free amplitude. -/
private lemma abs_log_sub_log_le_div_lower {η u v : ℝ} (hη : 0 < η)
    (hu : η ≤ u) (hv : η ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / η := by
  rcases le_total v u with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hη.trans_le hv) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_log_le_div_lower hη hu hv h
  · rw [abs_sub_comm (Real.log u), abs_sub_comm u]
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hη.trans_le hu) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_log_le_div_lower hη hv hu h

/-- Regularized logarithmic potentials are stable under complex amplitude approximation. -/
theorem half_log_normSq_stability {η : ℝ} (hη : 0 < η) (a b : ℂ) :
    |(1 / 2 : ℝ) * Real.log (Complex.normSq a + η) -
      (1 / 2 : ℝ) * Real.log (Complex.normSq b + η)| ≤
      ((‖a‖ + ‖b‖) * ‖a - b‖) / (2 * η) := by
  have hlog := abs_log_sub_log_le_div_lower hη
    (show η ≤ Complex.normSq a + η by linarith only [Complex.normSq_nonneg a])
    (show η ≤ Complex.normSq b + η by linarith only [Complex.normSq_nonneg b])
  have hnorm : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := by
    have ha := norm_add_le (a - b) b
    rw [sub_add_cancel] at ha
    have hb := norm_add_le (b - a) a
    rw [sub_add_cancel, norm_sub_rev b a] at hb
    exact abs_le.mpr ⟨by linarith only [hb], by linarith only [ha]⟩
  have hs : |(Complex.normSq a + η) - (Complex.normSq b + η)| ≤
      (‖a‖ + ‖b‖) * ‖a - b‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    rw [show (‖a‖ ^ 2 + η) - (‖b‖ ^ 2 + η) =
      (‖a‖ + ‖b‖) * (‖a‖ - ‖b‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left hnorm (by positivity)
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    (1 / 2 : ℝ) * |Real.log (Complex.normSq a + η) - Real.log (Complex.normSq b + η)| ≤
        (1 / 2 : ℝ) * (((‖a‖ + ‖b‖) * ‖a - b‖) / η) :=
      mul_le_mul_of_nonneg_left (hlog.trans (div_le_div_of_nonneg_right hs hη.le))
        (by norm_num)
    _ = _ := by field_simp [hη.ne']

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.half_log_normSq_stability
