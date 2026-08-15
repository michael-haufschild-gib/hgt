import GaloisForLFunctions.SelbergClass.ComplexRayMellinInversion

/-!
# Termwise Mellin--Barnes representation of damped multiple standard twists

This is the exact termwise part of Kaczorowski--Perelli (2026), equation
(3.4).  The damping parameter has positive real part after multiplication by
every positive multiple index power, so the complex-ray Gamma inversion applies
without a continuation hypothesis.  The separate sum--integral interchange is
deliberately not hidden here: it is the next analytic obligation.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.SelbergClass

theorem re_multipleTwistDampingParameter_mul_indexPower_pos
    {N : ℕ} (κ : Fin N → ℝ) {α X : ℝ}
    (hα : 0 < α) (hX : 0 < X) (n : Fin N → ℕ+) :
    0 < (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)).re := by
  have hpower : 0 < multipleIndexPower κ n := by
    unfold multipleIndexPower
    exact Finset.prod_pos fun i _ =>
      Real.rpow_pos_of_pos (by exact_mod_cast (n i).property) _
  simp only [multipleTwistDampingParameter, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  positivity

theorem dampedMultipleStandardTwistTerm_eq_complexMellinInvTwo_Gamma
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hα : 0 < α) (hX : 0 < X) (s : Fin N → ℂ) (n : Fin N → ℕ+) :
    dampedMultipleStandardTwistTerm a κ α X s n =
      (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
        complexMellinInvTwo Complex.Gamma
          (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) := by
  rw [complexMellinInvTwo_Gamma_eq_exp_neg
    (re_multipleTwistDampingParameter_mul_indexPower_pos κ hα hX n)]
  rw [dampedMultipleStandardTwistTerm]
  ring_nf

theorem dampedMultipleStandardTwist_eq_tsum_complexMellinInvTwo_Gamma
    {N : ℕ} (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) {α X : ℝ}
    (hα : 0 < α) (hX : 0 < X) (s : Fin N → ℂ) :
    dampedMultipleStandardTwist a κ α X s =
      ∑' n : Fin N → ℕ+,
        (∏ i, a i (n i : ℕ) * (((n i : ℕ) : ℂ) ^ (-s i))) *
          complexMellinInvTwo Complex.Gamma
            (multipleTwistDampingParameter α X * (multipleIndexPower κ n : ℂ)) := by
  unfold dampedMultipleStandardTwist
  apply tsum_congr
  intro n
  exact dampedMultipleStandardTwistTerm_eq_complexMellinInvTwo_Gamma a κ hα hX s n

end GaloisForLFunctions.SelbergClass
