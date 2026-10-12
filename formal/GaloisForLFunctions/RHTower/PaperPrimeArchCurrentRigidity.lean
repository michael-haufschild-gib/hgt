import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentOperator
import GaloisForLFunctions.RHTower.AnharmonicChebyshevNoetherCasimir

/-!
# Nonvanishing of every source slice and blindness of the ideal trace

The actual source has a strictly positive value at zero frequency on every admitted slice.
Consequently every full current multiplier has infinite compact-ideal cost, independently
of the unresolved signs at high frequency.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open Complex GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem current_pos_at_zero (a : Height) : 0 < current a 0 := by
  have hXi : XiC (point a 0) ≠ 0 :=
    XiC_ne_zero_of_abs_re_le_nine_halves (by rw [point_re]; norm_num)
  have hc : 1 / 2 + point a 0 * I = ((1 / 2 - (a : ℝ) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [point, sub_eq_add_neg]
  have hlog : (logDeriv XiC (point a 0)).im < 0 := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, hc]
    simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_add] using
      logDeriv_xi_ofReal_re_neg (x := 1 / 2 - (a : ℝ)) (by linarith [a.property.1])
  have h := HTGeometry.neg_two_im_deriv_mul_conj_eq XiC hXi
  change -2 * (deriv XiC (point a 0) * star (XiC (point a 0))).im = _ at h
  have hp : 0 < -Complex.normSq (XiC (point a 0)) * (logDeriv XiC (point a 0)).im :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos (Complex.normSq_pos.mpr hXi)) hlog
  dsimp only [current]
  nlinarith

theorem current_ne_zero (a : Height) : current a ≠ 0 := by
  intro h
  have hp := current_pos_at_zero a
  simp only [h, Pi.zero_apply, lt_self_iff_false] at hp

theorem operator_ne_zero (a : Height) : operator a ≠ 0 :=
  (operator_eq_zero_iff a).not.mpr (current_ne_zero a)

theorem operator_not_compact (a : Height) : ¬ IsCompactOperator (operator a) :=
  (operator_compact_iff_zero a).not.mpr (operator_ne_zero a)

/-- Every slice has the same infinite ideal weight; it cannot detect source positivity. -/
theorem operator_traceCost_top (a : Height) :
    compactOperatorTraceCost Space (operator a) = ∞ := by
  rw [operator_traceCost, if_neg (current_ne_zero a)]

theorem operator_add_compact_traceCost_top (a : Height)
    (K : compactOperatorStarAlgebra Space) :
    compactOperatorTraceCost Space (operator a + K.1) = ∞ := by
  rw [operator_traceCost_add_compact, if_neg (current_ne_zero a)]

theorem compact_correction_norm_pos (a : Height) (K : compactOperatorStarAlgebra Space) :
    0 < ‖operator a - K.1‖ :=
  (current_pos_at_zero a).trans_le
    ((le_abs_self _).trans (source_le_norm_sub_compact a 0 K))

end
end RHTower.PaperPrimeArch
