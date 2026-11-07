import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail

/-!
# The upper-power reserve of the complete first atom

The signed endpoint and lower-power tail consume at most seven halves of
the upper tail above radial scale three. Half the upper tail survives,
retaining the frequency scale of its complete Gamma Mellin mass.
-/

open Real
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The complete signed density retains half its highest-power Bessel tail. -/
theorem besselFirstAtomTailDensity_ge_half_upperTail {q : ℝ} (hq : 3 ≤ q) (τ : ℝ) :
    (1 / 2 : ℝ) * besselPowerTail (7 / 2) τ q ≤ besselFirstAtomTailDensity τ q := by
  have hq1 : 1 < q := by linarith only [hq]
  have hA := besselPowerTail_add_two_lower hq1 (show (1 : ℝ) < 3 / 2 by norm_num) τ
  norm_num only [show (3 / 2 : ℝ) + 2 = 7 / 2 by norm_num] at hA
  have hB := mul_le_mul_of_nonneg_left
    (rpow_mul_besselRadialValue_le_tail hq1 (show (1 : ℝ) < 3 / 2 by norm_num) τ)
    (show 0 ≤ 6 * q by linarith only [hq])
  have hT := (besselPowerTail_pos hq1 (show (1 : ℝ) < 3 / 2 by norm_num) τ).le
  have hcoef : 12 * q + 6 ≤ (7 / 2 : ℝ) * (q ^ 2 + q + 1 / 2) := by
    nlinarith only [hq]
  have hpay := mul_le_mul_of_nonneg_right hcoef hT
  have hm : q ^ (5 / 2 : ℝ) = q * q ^ (3 / 2 : ℝ) := by
    have hh := Real.rpow_add (zero_lt_one.trans hq1) 1 (3 / 2)
    norm_num at hh
    exact hh
  rw [besselFirstAtomTailDensity, hm]
  nlinarith only [hA, hB, hpay]

#print axioms besselFirstAtomTailDensity_ge_half_upperTail

end GaloisForLFunctions.CompletedArithmeticForms
