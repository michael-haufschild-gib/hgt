import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanExceptionalJets
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanMomentJets
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanCentralOrders

/-!
# First surviving physical Narain moments

The exceptional-height count determines the first nonzero moment. The doubly exceptional fifth moment is an explicit strictly positive real quantity.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The first nonzero physical moment has index one, three or five according to the exceptional target count. -/
theorem narainMeanMoment_first_nonzero (Y Z : Height) :
    (∀ k : ℕ, k < 1 + (if Y = narainExceptionalHeight then 2 else 0) +
        (if Z = narainExceptionalHeight then 2 else 0) →
      (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity Y Z k y) = 0) ∧
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity Y Z
      (1 + (if Y = narainExceptionalHeight then 2 else 0) +
        (if Z = narainExceptionalHeight then 2 else 0)) y) ≠ 0 := by
  have ha := analyticAt_narainMellinMean_of_nonneg_re Y Z
    (u := 0) (by simp) (by norm_num)
  have ho : analyticOrderAt (narainMellinMean Y Z) 0 =
      ((1 + (if Y = narainExceptionalHeight then 2 else 0) +
        (if Z = narainExceptionalHeight then 2 else 0) : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_narainMellinMean_zero]
    split_ifs <;> norm_num
  have hjets := (_root_.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mp ho
  simpa only [integral_narainMeanMomentDensity_eq_jet] using hjets

/-- The cubic physical logarithmic moment at one exceptional target height is explicit. -/
theorem integral_narainMeanMomentDensity_one_exceptional_three (Z : Height) :
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity narainExceptionalHeight Z 3 y) =
      32 * (narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ) *
        (Z.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) *
        (2 - 4 * deriv xi 1 - Complex.log (Z.val : ℂ)) := by
  rw [integral_narainMeanMomentDensity_eq_jet, narainMellinMean_one_exceptional_third_jet]

/-- The fifth physical logarithmic moment at the doubly exceptional height is explicit. -/
theorem integral_narainMeanMomentDensity_two_exceptional_five :
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity narainExceptionalHeight narainExceptionalHeight 5 y) =
      (2560 / 3 : ℂ) * (narainExceptionalHeight.val : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) ^ 2 := by
  rw [integral_narainMeanMomentDensity_eq_jet, narainMellinMean_two_exceptional_fifth_jet]

/-- The fifth physical moment cannot vanish: the exceptional central cancellation stops there. -/
theorem integral_narainMeanMomentDensity_two_exceptional_five_ne_zero :
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity narainExceptionalHeight narainExceptionalHeight 5 y) ≠ 0 := by
  rw [integral_narainMeanMomentDensity_two_exceptional_five]
  refine mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr narainExceptionalHeight.property.ne')) (pow_ne_zero 2 ?_)
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.sub_re] at hr
  linarith only [hr, narainCentralXiCurvature_neg]

/-- The doubly exceptional fifth moment equals a real positive square expression. -/
theorem integral_narainMeanMomentDensity_two_exceptional_five_real :
    (∫ y in Ioi (0 : ℝ),
      narainMeanMomentDensity narainExceptionalHeight narainExceptionalHeight 5 y) =
      ((2560 / 3 * narainExceptionalHeight.val *
        (2 - (deriv (deriv (logDeriv xi)) (1 : ℂ)).re) ^ 2 : ℝ) : ℂ) := by
  rw [integral_narainMeanMomentDensity_two_exceptional_five, ← narainCentralXiCurvature_real]
  push_cast <;> ring

/-- The first surviving moment at the doubly exceptional height is strictly positive. -/
theorem integral_narainMeanMomentDensity_two_exceptional_five_pos :
    0 < (∫ y in Ioi (0 : ℝ),
      narainMeanMomentDensity narainExceptionalHeight narainExceptionalHeight 5 y).re := by
  rw [integral_narainMeanMomentDensity_two_exceptional_five_real, Complex.ofReal_re]
  exact mul_pos (mul_pos (by norm_num) narainExceptionalHeight.property)
    (sq_pos_of_pos (by linarith only [narainCentralXiCurvature_neg]))

#print axioms narainMeanMoment_first_nonzero
#print axioms integral_narainMeanMomentDensity_two_exceptional_five_real
#print axioms integral_narainMeanMomentDensity_two_exceptional_five_pos
#print axioms integral_narainMeanMomentDensity_one_exceptional_three
#print axioms integral_narainMeanMomentDensity_two_exceptional_five
#print axioms integral_narainMeanMomentDensity_two_exceptional_five_ne_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
