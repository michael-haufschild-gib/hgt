import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralExceptional

/-!
# Exact central orders of Narain target numerators

Oddness and the nonzero exceptional cubic jet classify filled numerator orders as one or three, and divided numerator orders as zero or two.
-/

open Complex RHTower
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Oddness removes the second central jet of every filled target numerator. -/
theorem filledNumeratorMean_second_jet_zero (Y : Height) :
    iteratedDeriv 2 (filledNumeratorMean Y) 0 = 0 := by
  have heq : (fun u : ℂ => filledNumeratorMean Y (-u)) = -filledNumeratorMean Y :=
    funext (filledNumeratorMean_neg Y)
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv 2 f 0) heq
  rw [_root_.iteratedDeriv_comp_neg, iteratedDeriv_neg] at h
  simp only [neg_zero, neg_one_sq, smul_eq_mul, one_mul] at h
  linear_combination h / 2

/-- Each filled target numerator has central order one, except for the unique cubic height. -/
theorem analyticOrderAt_filledNumeratorMean_zero (Y : Height) :
    analyticOrderAt (filledNumeratorMean Y) 0 =
      if Y = narainExceptionalHeight then 3 else 1 := by
  have ha := (differentiable_filledNumeratorMean Y).analyticAt 0
  by_cases hY : Y = narainExceptionalHeight
  · subst Y
    rw [if_pos rfl]
    apply (_root_.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mpr
    refine ⟨?_, filledNumeratorMean_exceptional_third_jet_ne_zero⟩
    intro k hk
    interval_cases k
    · exact filledNumeratorMean_zero _
    · simpa only [iteratedDeriv_one] using
        (filledNumeratorMean_deriv_zero_eq_zero_iff narainExceptionalHeight).mpr rfl
    · exact filledNumeratorMean_second_jet_zero _
  · rw [if_neg hY]
    apply (_root_.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mpr
    constructor
    · intro k hk
      have : k = 0 := by omega
      subst k
      exact filledNumeratorMean_zero Y
    · simpa only [iteratedDeriv_one] using
        mt (filledNumeratorMean_deriv_zero_eq_zero_iff Y).mp hY

/-- The entire divided numerator has central order zero or exactly two. -/
theorem analyticOrderAt_dividedFilledNumeratorMean_zero (Y : Height) :
    analyticOrderAt (dividedFilledNumeratorMean Y) 0 =
      if Y = narainExceptionalHeight then 2 else 0 := by
  have ha := (differentiable_dividedFilledNumeratorMean Y).analyticAt 0
  by_cases hY : Y = narainExceptionalHeight
  · subst Y
    rw [if_pos rfl]
    apply (_root_.analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mpr
    constructor
    · intro k hk
      interval_cases k
      · rw [iteratedDeriv_zero, ← filledNumeratorMean_first_jet_eq_divided]
        exact (filledNumeratorMean_deriv_zero_eq_zero_iff narainExceptionalHeight).mpr rfl
      · exact dividedFilledNumeratorMean_first_jet_zero _
    · intro h
      apply filledNumeratorMean_exceptional_third_jet_ne_zero
      rw [filledNumeratorMean_third_jet_eq_divided, h, mul_zero]
  · rw [if_neg hY]
    apply ha.analyticOrderAt_eq_zero.mpr
    rw [← filledNumeratorMean_first_jet_eq_divided]
    exact mt (filledNumeratorMean_deriv_zero_eq_zero_iff Y).mp hY

#print axioms analyticOrderAt_filledNumeratorMean_zero
#print axioms analyticOrderAt_dividedFilledNumeratorMean_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
