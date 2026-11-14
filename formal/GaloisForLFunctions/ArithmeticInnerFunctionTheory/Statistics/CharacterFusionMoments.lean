import GaloisForLFunctions.ArithmeticInnerFunctionTheory.Statistics.CharacterMoments

/-!
# Triple character moments and the triangle rule

Clebsch–Gordan multiplication and Sato–Tate orthogonality turn the third
mixed moment into a multiplicity. It is one precisely when the three degrees
form a triangle and their sum is even, and zero otherwise.
-/

open MeasureTheory Finset
open GaloisForLFunctions.CompletedArithmeticForms (cosSum)

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-- The third mixed moment is the `SU(2)` triangle-and-parity multiplicity. -/
theorem integral_cosSum_triple (a b c : ℕ) :
    ∫ θ, cosSum θ a * cosSum θ b * cosSum θ c ∂satoTate =
      if c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c ∧ (a + b + c) % 2 = 0
        then 1 else 0 := by
  have hpoint (θ : ℝ) : cosSum θ a * cosSum θ b * cosSum θ c =
      ∑ r ∈ range (min a b + 1), cosSum θ (a + b - 2 * r) * cosSum θ c := by
    rw [← sum_mul, cosSum_mul_cosSum]
  simp_rw [hpoint]
  rw [integral_finsetSum _ fun r _ => integrable_cosSum_mul (a + b - 2 * r) c]
  simp_rw [integral_cosSum_mul_cosSum]
  by_cases h : c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c ∧ (a + b + c) % 2 = 0
  · rw [if_pos h, sum_eq_single ((a + b - c) / 2)]
    · exact if_pos (by omega)
    · intro r hr hne
      have hr' := mem_range.mp hr
      exact if_neg (by omega)
    · intro hr
      exact False.elim (hr (mem_range.mpr (by omega)))
  · rw [if_neg h]
    apply sum_eq_zero
    intro r hr
    have hr' := mem_range.mp hr
    exact if_neg (by omega)

#print axioms integral_cosSum_triple

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
