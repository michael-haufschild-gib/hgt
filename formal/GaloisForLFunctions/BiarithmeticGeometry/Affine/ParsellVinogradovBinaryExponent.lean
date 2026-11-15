import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearMinors

/-!
# The binary overlap exponent as a binomial sum

Summing the optimal homogeneous-block powers gives exactly
`Σ_{0 ≤ j < (k+1)/2} choose(k+1-2j,2)`. For positive `k`, this is the
proposed exponent `B₂,ₖ`. Both expressions satisfy the same two-step
recurrence: adjoining the next two degrees adds `choose(k+3,2)`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov

/-- Sum of the sharp homogeneous-block powers for degrees one through `k`. -/
def binaryExponent (k : ℕ) : ℕ := ∑ d ∈ Finset.range k, (d + 2) ^ 2 / 4

private def binaryBinomialSum (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2

private theorem adjacent_quarter_squares (k : ℕ) :
    (k + 2) ^ 2 / 4 + (k + 3) ^ 2 / 4 = (k + 3).choose 2 := by
  rw [Nat.choose_two_right, show k + 3 - 1 = k + 2 by omega]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r ≤ 1 ∧ k = 2 * q + r := by
    refine ⟨k / 2, k % 2, ?_, ?_⟩ <;> omega
  have hr' : r = 0 ∨ r = 1 := by omega
  rcases hr' with rfl | rfl
  · simp only [Nat.add_zero]
    have ha : (2 * q + 2) ^ 2 = 4 * (q ^ 2 + 2 * q + 1) := by ring
    have hb : (2 * q + 3) ^ 2 = 4 * (q ^ 2 + 3 * q + 2) + 1 := by ring
    have hc : (2 * q + 3) * (2 * q + 2) = 2 * (2 * q ^ 2 + 5 * q + 3) := by ring
    rw [ha, hb, hc]
    omega
  · have ha : (2 * q + 1 + 2) ^ 2 = 4 * (q ^ 2 + 3 * q + 2) + 1 := by ring
    have hb : (2 * q + 1 + 3) ^ 2 = 4 * (q ^ 2 + 4 * q + 4) := by ring
    have hc : (2 * q + 1 + 3) * (2 * q + 1 + 2) =
        2 * (2 * q ^ 2 + 7 * q + 6) := by ring
    rw [ha, hb, hc]
    omega

/-- Adding two consecutive degrees contributes one binomial coefficient. -/
theorem binaryExponent_two_step (k : ℕ) :
    binaryExponent (k + 2) = binaryExponent k + (k + 3).choose 2 := by
  rw [binaryExponent, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [add_assoc, adjacent_quarter_squares]
  rfl

private theorem binaryBinomialSum_two_step (k : ℕ) :
    binaryBinomialSum (k + 2) = binaryBinomialSum k + (k + 3).choose 2 := by
  rw [binaryBinomialSum, show (k + 2 + 1) / 2 = (k + 1) / 2 + 1 by omega,
    Finset.sum_range_succ']
  have hterm (j : ℕ) : (k + 2 + 1 - 2 * (j + 1)).choose 2 =
      (k + 1 - 2 * j).choose 2 := by
    congr 1
    omega
  simp only [hterm, Nat.mul_zero, Nat.sub_zero]
  rfl

/-- The sum of the homogeneous sharp exponents equals the proposed binary binomial sum. -/
theorem binaryExponent_eq_binomial_sum (k : ℕ) :
    binaryExponent k = ∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2 := by
  change binaryExponent k = binaryBinomialSum k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h0 : k = 0
    · subst k
      norm_num [binaryExponent, binaryBinomialSum]
    by_cases h1 : k = 1
    · subst k
      norm_num [binaryExponent, binaryBinomialSum]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
    rw [binaryExponent_two_step, binaryBinomialSum_two_step, ih n (by omega)]

/-- For positive degree, the sum has precisely the upper index in the proposed exponent. -/
theorem binaryExponent_eq_paper_sum (k : ℕ) (hk : 0 < k) :
    binaryExponent k = ∑ j ∈ Finset.range ((k - 1) / 2 + 1), (k + 1 - 2 * j).choose 2 := by
  rw [binaryExponent_eq_binomial_sum, show (k + 1) / 2 = (k - 1) / 2 + 1 by omega]

#print axioms binaryExponent_two_step
#print axioms binaryExponent_eq_binomial_sum
#print axioms binaryExponent_eq_paper_sum

end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
