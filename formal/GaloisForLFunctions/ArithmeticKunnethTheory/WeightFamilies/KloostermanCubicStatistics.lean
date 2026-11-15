import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanThirdMoment
import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanProbabilityLaw

/-!
# Cubic biases of empirical Kloosterman laws

The complete variance-one law has an explicit third moment. For the punctured
family with the Sato–Tate normalization `K/√p`, subtracting twice the first moment
leaves the exact third symmetric-power bias. Its numerator is never zero.
-/

open Finset MeasureTheory

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

private instance primeFieldFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

/-- Exact skewness of the already standardized complete empirical law. -/
theorem integral_primeKloostermanLaw_cube (p : Nat.Primes) :
    ∫ x, x ^ 3 ∂primeKloostermanLaw p =
      (((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) * p.val + 2) /
        Real.sqrt ((p.val : ℝ) - 1) ^ 3 := by
  have hp : (p.val : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  rw [integral_primeKloostermanLaw]
  simp only [standardizedKloostermanTrace, div_pow, ← sum_div,
    sum_primeKloostermanTrace_cube, smul_eq_mul]
  field_simp

/-- The square-root normalization used by the Sato–Tate law on `[-2,2]`. -/
def satoTateKloostermanTrace (p : Nat.Primes) (a : ZMod p.val) : ℝ :=
  primeKloostermanTrace p a / Real.sqrt (p.val : ℝ)

/-- The third symmetric-power polynomial in the trace normalization. -/
def cubicTraceCharacter (x : ℝ) : ℝ := x ^ 3 - 2 * x

/-- The singular parameter correction survives cancellation of the linear term. -/
theorem sum_primeKloosterman_cubic_character (p : Nat.Primes) :
    ∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      cubicTraceCharacter (satoTateKloostermanTrace p a) =
        (((cubicCyclotomicRoots (F := ZMod p.val)).card - 1 : ℝ) *
          (p.val : ℝ) ^ 2 + 1) / ((p.val : ℝ) * Real.sqrt (p.val : ℝ)) := by
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have hs : Real.sqrt (p.val : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs2 := Real.sq_sqrt hp.le
  have hs3 : Real.sqrt (p.val : ℝ) ^ 3 = (p.val : ℝ) * Real.sqrt (p.val : ℝ) := by
    rw [pow_succ, hs2]
  simp only [cubicTraceCharacter, satoTateKloostermanTrace, div_pow]
  rw [sum_sub_distrib, ← sum_div, ← mul_sum, ← sum_div,
    sum_primeKloostermanTrace_cube_ne_zero, sum_primeKloostermanTrace_ne_zero]
  rw [hs3]
  field_simp
  ring

/-- A nonzero third-character bias distinguishes every punctured law from Sato–Tate. -/
theorem sum_primeKloosterman_cubic_character_ne_zero (p : Nat.Primes) :
    (∑ a ∈ (univ : Finset (ZMod p.val)).erase 0,
      cubicTraceCharacter (satoTateKloostermanTrace p a)) ≠ 0 := by
  have hp : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  rw [sum_primeKloosterman_cubic_character]
  apply div_ne_zero
  · rw [cubicCyclotomicRoots_card]
    split_ifs <;> push_cast <;> nlinarith only [hp, sq_nonneg (p.val : ℝ)]
  · exact mul_ne_zero (by linarith only [hp])
      (ne_of_gt (Real.sqrt_pos.mpr (by linarith only [hp])))

#print axioms integral_primeKloostermanLaw_cube
#print axioms sum_primeKloosterman_cubic_character
#print axioms sum_primeKloosterman_cubic_character_ne_zero

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
