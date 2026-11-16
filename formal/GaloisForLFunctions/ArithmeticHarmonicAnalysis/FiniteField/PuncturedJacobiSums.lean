import Mathlib.NumberTheory.JacobiSum.Basic

/-!
# Punctured three-point sums

Removing the points zero and one turns the character of
`c x (1-x)^a` into a Jacobi sum. This remains valid for exponent zero:
the trivial multiplicative character still vanishes at zero.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K R : Type*} [Field K] [Fintype K] [CommRing R]
open scoped Classical

/-- Every punctured three-point monomial character sum is a Jacobi sum, including exponent zero. -/
theorem finiteField_punctured_monomial_character_sum (χ : MulChar K R) (c : K) (a : ℕ) :
    (∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x ≠ 1),
      χ (c * x * (1 - x) ^ a)) = χ c * jacobiSum χ (χ ^ a) := by
  rw [jacobiSum, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = 0
  · subst x
    simp only [ne_eq, not_true_eq_false, false_and, if_false, MulChar.map_zero, zero_mul, mul_zero]
  · by_cases hx1 : x = 1
    · subst x
      simp only [ne_eq, not_true_eq_false, and_false, if_false, sub_self, MulChar.map_zero, mul_zero]
    · have hsub : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
      have hpow : (χ ^ a) (1 - x) = χ (1 - x) ^ a :=
        MulChar.pow_apply_coe χ a (Units.mk0 (1 - x) hsub)
      rw [if_pos ⟨hx, hx1⟩, map_mul, map_mul, map_pow, hpow, mul_assoc]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
