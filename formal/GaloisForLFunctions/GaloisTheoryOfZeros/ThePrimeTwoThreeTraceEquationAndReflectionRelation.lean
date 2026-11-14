import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeReflectionKernelOfTheZeros

/-!
# A finite equation and reflection relation at primes two and three

The mixed prime value `2^ρ / 3^ρ` satisfies a monic equation over the
complete trace field, with every multiplicity in the paired height fibre.
At an individual zero, the two reflection discriminants have a concrete
product square root in its pair field. At least one of the two reflection
differences is nonzero, since these two prime coordinates separate exponents.
-/

noncomputable section
open Complex Polynomial RHTower
open scoped BigOperators

namespace GaloisForLFunctions.GaloisTheoryOfZeros

private def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def primeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

local notation "p₂" => primeTwo
local notation "p₃" => primeThree
local notation "E" => primeTraceExtension

private theorem primeRelationValue_two_three (z : ℂ) :
    primeRelationValue z (Finsupp.single p₂ 1 + Finsupp.single p₃ (-1)) =
      Complex.exp (z * (Real.log 2 : ℂ)) / Complex.exp (z * (Real.log 3 : ℂ)) := by
  rw [primeRelationValue_add, primeRelationValue_single, primeRelationValue_single]
  change Complex.exp (z * (Real.log 2 : ℂ)) ^ (1 : ℤ) *
    Complex.exp (z * (Real.log 3 : ℂ)) ^ (-1 : ℤ) = _
  rw [zpow_one, zpow_neg_one, div_eq_mul_inv]

/-- The trace equation for the specified mixed prime monomial `2^ρ / 3^ρ`. -/
def primeTwoThreeRatioEquation (t : ℝ) : primeTraceField[X] :=
  primeTracePolynomial t (Finsupp.single p₂ 1 + Finsupp.single p₃ (-1))

theorem primeTwoThreeRatioEquation_monic (t : ℝ) : (primeTwoThreeRatioEquation t).Monic :=
  primeTracePolynomial_monic t _

/-- Exact factorization over the paired ordinate fibre, retaining analytic multiplicities. -/
theorem primeTwoThreeRatioEquation_map (t : ℝ) :
    (primeTwoThreeRatioEquation t).map (algebraMap primeTraceField ℂ) =
      ∏ i : PrimeTraceCopies t,
        (X - C (Complex.exp (((primeTraceCopy t i).1 : ℂ) * (Real.log 2 : ℂ)) /
          Complex.exp (((primeTraceCopy t i).1 : ℂ) * (Real.log 3 : ℂ)))) := by
  rw [primeTwoThreeRatioEquation, primeTracePolynomial_map_eq_prod]
  simp_rw [primeRelationValue_two_three]

/-- The finite trace equation has exactly the actual mixed-prime roots in that fibre. -/
theorem primeTwoThreeRatioEquation_rootSet (t : ℝ) (z : ℂ) :
    z ∈ (primeTwoThreeRatioEquation t).rootSet ℂ ↔
      ∃ i : PrimeTraceCopies t,
        Complex.exp (((primeTraceCopy t i).1 : ℂ) * (Real.log 2 : ℂ)) /
          Complex.exp (((primeTraceCopy t i).1 : ℂ) * (Real.log 3 : ℂ)) = z := by
  rw [primeTwoThreeRatioEquation, primeTracePolynomial_rootSet]
  simp_rw [primeRelationValue_two_three]

/-- A square root of the product of the two reflection discriminants, in the pair field itself. -/
def primeTwoThreeReflectionSquareRoot (ρ : XiDivisorSupport) : primePairField ρ :=
  ⟨primeReflectionDifference p₂ ρ * primeReflectionDifference p₃ ρ,
    primeReflectionDifference_product_mem_pair p₂ p₃ ρ⟩

/-- The explicit two-prime reflection-radicand relation, including zero radicands. -/
theorem primeTwoThreeReflectionSquareRoot_sq (ρ : XiDivisorSupport) :
    (primeTwoThreeReflectionSquareRoot ρ : E) ^ 2 =
      (primeResiduePairValue p₂ ρ ^ 2 - 8) * (primeResiduePairValue p₃ ρ ^ 2 - 12) := by
  change (primeReflectionDifference p₂ ρ * primeReflectionDifference p₃ ρ) ^ 2 = _
  rw [mul_pow, primeReflectionDifference_sq, primeReflectionDifference_sq]
  norm_num [primeTwo, primeThree]

/-- The two specified reflection differences cannot both vanish at an actual zero. -/
theorem primeTwoThreeReflectionDifference_nonzero (ρ : XiDivisorSupport) :
    primeReflectionDifference p₂ ρ ≠ 0 ∨ primeReflectionDifference p₃ ρ ≠ 0 := by
  by_contra h
  push Not at h
  have h2 := sub_eq_zero.mp h.1
  have h3 := sub_eq_zero.mp h.2
  have he : (ρ : ℂ) = (xiZeroReflectEquiv ρ : ℂ) := by
    apply two_prime_exponential_injective Nat.prime_two Nat.prime_three (by norm_num)
    apply Prod.ext
    · simpa only [primeResidueValue_coe, primeTwo] using congrArg (fun x : E => (x : ℂ)) h2
    · simpa only [primeResidueValue_coe, primeThree] using congrArg (fun x : E => (x : ℂ)) h3
  have hi := congrArg Complex.im he
  rw [xiZeroReflectEquiv_apply] at hi
  simp only [Complex.sub_im, Complex.one_im] at hi
  exact xi_divisor_support_im_ne_zero ρ (by linarith only [hi])

#print axioms primeTwoThreeRatioEquation_monic
#print axioms primeTwoThreeRatioEquation_map
#print axioms primeTwoThreeRatioEquation_rootSet
#print axioms primeTwoThreeReflectionSquareRoot_sq
#print axioms primeTwoThreeReflectionDifference_nonzero

end GaloisForLFunctions.GaloisTheoryOfZeros
