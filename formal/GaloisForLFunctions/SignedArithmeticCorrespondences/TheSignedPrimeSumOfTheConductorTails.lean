import GaloisForLFunctions.SignedArithmeticCorrespondences.TheIntegralRangeOfTheMixedQuotientCells

/-!
# Abel summation on both conductor divisors

A price accumulated from its local increments pairs with the quotient
cells exactly as the increments pair with multiplicative tails. For the
Chebyshev error the increments are the centered von Mangoldt weights.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

/-- Both directed incidences of the actual conductors at multiplication k. -/
def twoSidedMultiple (N k : ℕ) (a b : ℕ → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 N, ((upperDivisor N a i:ℝ)*upperDivisor N b (k*i) +
    (upperDivisor N b i:ℝ)*upperDivisor N a (k*i))

/-- Discrete summation by parts at arbitrary signed prices. The zero
quotient contributes nothing because its accumulated price is zero. -/
theorem quotient_price_by_increments (N : ℕ) (a b : ℕ → ℤ) (p : ℕ → ℝ) :
    (∑ k ∈ range (N+1), twoSidedCoefficient N a b k*(∑ q ∈ Icc 1 k, p q)) =
      ∑ q ∈ Icc 1 N, twoSidedMultiple N q a b*p q := by
  have hp (k : ℕ) (hk : k∈range (N+1)) : ∑ q ∈ Icc 1 k, p q =
      ∑ q ∈ Icc 1 N, if q≤k then p q else 0 := by
    rw [← sum_filter]
    congr 1
    ext j
    simp only [mem_filter,mem_Icc]
    have := mem_range.mp hk
    omega
  rw [sum_congr rfl (fun k hk => congrArg (fun t => twoSidedCoefficient N a b k*t) (hp k hk))]
  simp only [mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  refine sum_congr rfl fun q _ => ?_
  have hs : (range (N+1)).filter (fun k => q≤k)=Icc q N := by
    ext j
    simp only [mem_filter,mem_range,mem_Icc]
    omega
  rw [← sum_filter,hs,← sum_mul]
  exact congrArg (fun t => t*p q) (twoSidedCoefficient_tail N q a b)

/-- The signed finite part admits a local prime-sum comparison with no
positive quotient variation. The real jet and both fractional boundaries
have the same normalization as in Weil's full form. -/
theorem interleaved_centered_prime_sum (N : ℕ) (a b : ℕ → ℤ) :
    interleavedFinitePart N a b =
      -(∑ q ∈ Icc 1 N, twoSidedMultiple N q a b*(Λ q-1))-
        (∫ x in (0:ℝ)..1, mixedJetSection N a b x)/2 := by
  have he (k : ℕ) : psiRemainder k=∑ q ∈ Icc 1 k, (Λ q-1) := by
    simp [psiRemainder,chebyshevPsi,sum_sub_distrib,Nat.card_Icc]
  simp only [interleaved_finite_part,he,quotient_price_by_increments]

#print axioms quotient_price_by_increments
#print axioms interleaved_centered_prime_sum
end GaloisForLFunctions.SignedArithmeticCorrespondences
