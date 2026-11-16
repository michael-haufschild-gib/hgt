import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Degrees of reduced rational quotient coordinates

Coprimality forces the canonical numerator and denominator of a
polynomial quotient to have exactly the original degrees. The rational
function-field degree theorem then gives the maximum of those degrees.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable {K : Type*} [Field K]

/-- A reduced polynomial quotient has canonical numerator and denominator of the same degrees. -/
theorem rationalCoprimeQuotient_degrees
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) :
    (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q).num.natDegree = P.natDegree ∧
    (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q).denom.natDegree = Q.natDegree := by
  let f := algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q
  have hf : f ≠ 0 := div_ne_zero (RatFunc.algebraMap_ne_zero hP) (RatFunc.algebraMap_ne_zero hQ)
  have he : f.num * Q = P * f.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  have hPn : P ∣ f.num := hcop.dvd_of_dvd_mul_right (by rw [he]; exact dvd_mul_right _ _)
  have hQd : Q ∣ f.denom := hcop.symm.dvd_of_dvd_mul_left (by rw [← he]; exact dvd_mul_left _ _)
  constructor
  · exact le_antisymm (Polynomial.natDegree_le_of_dvd (RatFunc.num_div_dvd P hQ) hP)
      (Polynomial.natDegree_le_of_dvd hPn (RatFunc.num_ne_zero hf))
  · exact le_antisymm (Polynomial.natDegree_le_of_dvd (RatFunc.denom_div_dvd P Q) hQ)
      (Polynomial.natDegree_le_of_dvd hQd (RatFunc.denom_ne_zero f))

/-- The index of a reduced rational quotient coordinate is the larger of its two polynomial degrees. -/
theorem rationalCoprimeQuotientSubfield_finrank
    (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) :
    Module.finrank K⟮algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q⟯
      (RatFunc K) = max P.natDegree Q.natDegree := by
  obtain ⟨hnum, hden⟩ := rationalCoprimeQuotient_degrees P Q hP hQ hcop
  rw [RatFunc.finrank_eq_max_natDegree, hnum, hden]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
