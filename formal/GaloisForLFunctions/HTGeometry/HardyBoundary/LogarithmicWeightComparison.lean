import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorStartsAtOne
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# Reference and positive logarithmic Fourier weights

The reference symbol bounds the positive logarithm and differs from it
by a bounded upper error. Their weighted square integrals therefore have
the same domain on L².
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry
open CanonicalSystemOfTheWindowTower


/-- The positive logarithm is bounded by the reference symbol at every scale at least one. -/
theorem max_log_abs_le_positiveLogarithmicSymbol {c : ℝ} (hc : 1 ≤ c) (x : ℝ) :
    max (Real.log |x|) 0 ≤ positiveLogarithmicSymbol (c * x) := by
  apply max_le ?_ ((show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_positiveLogarithmicSymbol _))
  by_cases hx : x = 0
  · subst x
    simpa only [abs_zero, Real.log_zero] using
      (show (0 : ℝ) ≤ 1 by norm_num).trans (one_le_positiveLogarithmicSymbol (c * 0))
  have habs : 0 < |x| := abs_pos.mpr hx
  have hprod : 0 ≤ (c ^ 2 - 1) * x ^ 2 :=
    mul_nonneg (by nlinarith only [hc, sq_nonneg (c - 1)]) (sq_nonneg x)
  have hsq : |x| ^ 2 ≤ 1 + (c * x) ^ 2 := by
    rw [sq_abs]
    nlinarith only [hprod]
  have hl := Real.log_le_log (sq_pos_of_pos habs) hsq
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold positiveLogarithmicSymbol
  linarith only [hl]

/-- The reference symbol differs from the positive logarithm by a bounded upper error. -/
theorem positiveLogarithmicSymbol_le_const_add_max_log (c x : ℝ) :
    positiveLogarithmicSymbol (c * x) ≤
      1 + (1 / 2 : ℝ) * Real.log (1 + c ^ 2) + max (Real.log |x|) 0 := by
  by_cases hx : |x| ≤ 1
  · have hsq : x ^ 2 ≤ 1 := by
      simpa only [← pow_two, sq_abs, one_pow] using
        mul_self_le_mul_self (abs_nonneg x) hx
    have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg c)
    have hl := Real.log_le_log (show (0 : ℝ) < 1 + (c * x) ^ 2 by positivity)
      (show 1 + (c * x) ^ 2 ≤ 1 + c ^ 2 by nlinarith only [hp])
    unfold positiveLogarithmicSymbol
    linarith only [hl, le_max_right (Real.log |x|) (0 : ℝ)]
  · have habs : 0 < |x| := lt_trans zero_lt_one (lt_of_not_ge hx)
    have hs : 1 ≤ |x| ^ 2 := by
      nlinarith only [lt_of_not_ge hx, sq_nonneg (|x| - 1)]
    have hp : 1 + (c * x) ^ 2 ≤ (1 + c ^ 2) * |x| ^ 2 := by
      rw [sq_abs] at hs ⊢
      nlinarith only [hs]
    have hl := Real.log_le_log (show (0 : ℝ) < 1 + (c * x) ^ 2 by positivity) hp
    rw [Real.log_mul (by positivity : (1 + c ^ 2 : ℝ) ≠ 0)
      (ne_of_gt (sq_pos_of_pos habs)), Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    unfold positiveLogarithmicSymbol
    linarith only [hl, le_max_left (Real.log |x|) (0 : ℝ)]

/-- On L², finite reference energy is equivalent to finite positive logarithmic moment. -/
theorem integrable_logarithmicReference_iff_positiveLog
    {c : ℝ} (hc : 1 ≤ c) (v : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ => positiveLogarithmicSymbol (c * ξ) * ‖v ξ‖ ^ 2) ↔
      Integrable (fun ξ : ℝ => max (Real.log |ξ|) 0 * ‖v ξ‖ ^ 2) := by
  have hm : Measurable (fun ξ : ℝ => max (Real.log |ξ|) 0) := by fun_prop
  have hr : Measurable (fun ξ : ℝ => positiveLogarithmicSymbol (c * ξ)) :=
    continuous_positiveLogarithmicSymbol.measurable.comp (measurable_const.mul measurable_id)
  have hv := (Lp.aestronglyMeasurable v).norm.pow 2
  constructor
  · intro hi
    apply hi.mono' (hm.aestronglyMeasurable.mul hv)
    exact Eventually.of_forall fun ξ => by
      dsimp only [Pi.mul_apply, Pi.pow_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (max_log_abs_le_positiveLogarithmicSymbol hc ξ) (sq_nonneg _)
  · intro hi
    have hsq : Integrable (fun ξ : ℝ => ‖v ξ‖ ^ 2) :=
      (Lp.memLp v).integrable_norm_pow (by norm_num)
    apply ((hsq.const_mul (1 + (1 / 2 : ℝ) * Real.log (1 + c ^ 2))).add hi).mono'
      (hr.aestronglyMeasurable.mul hv)
    exact Eventually.of_forall fun ξ => by
      dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (zero_le_one.trans (one_le_positiveLogarithmicSymbol _)) (sq_nonneg _))]
      simpa only [add_mul] using mul_le_mul_of_nonneg_right
        (positiveLogarithmicSymbol_le_const_add_max_log c ξ) (sq_nonneg ‖v ξ‖)

#print axioms max_log_abs_le_positiveLogarithmicSymbol
#print axioms positiveLogarithmicSymbol_le_const_add_max_log
#print axioms integrable_logarithmicReference_iff_positiveLog
end GaloisForLFunctions.HTGeometry

