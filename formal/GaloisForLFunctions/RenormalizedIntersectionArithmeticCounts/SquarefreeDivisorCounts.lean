import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Squarefree divisor counts from finite sets of places

Residue degrees define actual finite sets of squarefree divisors. The
coefficient of the inverse Euler product equals the number with even
support minus the number with odd support, without an assumed arithmetic
cancellation identity.
-/

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset PowerSeries
variable {ι : Type*} [DecidableEq ι]

/-- Squarefree divisors of prescribed weighted degree in an actual finite set of places. -/
def squarefreeDegreeSubsets (S : Finset ι) (d : ι → ℕ) (n : ℕ) : Finset (Finset ι) :=
  S.powerset.filter fun T => ∑ v ∈ T, d v = n

/-- Even-support squarefree divisors; the definition is a literal finite set count. -/
def evenSquarefreeDivisorCount (S : Finset ι) (d : ι → ℕ) (n : ℕ) : ℕ :=
  ((squarefreeDegreeSubsets S d n).filter fun T => Even T.card).card

/-- Odd-support squarefree divisors; no signed arithmetic function enters the definition. -/
def oddSquarefreeDivisorCount (S : Finset ι) (d : ι → ℕ) (n : ℕ) : ℕ :=
  ((squarefreeDegreeSubsets S d n).filter fun T => ¬Even T.card).card

/-- Finite inverse Euler products expand into weighted squarefree divisors. -/
theorem squarefreeEuler_expansion (S : Finset ι) (d : ι → ℕ) :
    (∏ v ∈ S, (1 - (X : PowerSeries ℂ) ^ d v)) =
      ∑ T ∈ S.powerset, C ((-1 : ℂ) ^ T.card) * X ^ (∑ v ∈ T, d v) := by
  rw [show (∏ v ∈ S, (1 - (X : PowerSeries ℂ) ^ d v)) =
      ∏ v ∈ S, (-X ^ d v + 1) by
    apply prod_congr rfl
    intro v _
    ring]
  rw [prod_add]
  apply sum_congr rfl
  intro T _
  simp only [prod_const_one, mul_one, prod_neg, prod_pow_eq_pow_sum,
    map_pow, map_neg, map_one]

/-- The coefficient is the difference of the two independently defined finite counts. -/
theorem coeff_squarefreeEuler_eq_counts (S : Finset ι) (d : ι → ℕ) (n : ℕ) :
    coeff n (∏ v ∈ S, (1 - (X : PowerSeries ℂ) ^ d v)) =
      (evenSquarefreeDivisorCount S d n : ℂ) - oddSquarefreeDivisorCount S d n := by
  rw [squarefreeEuler_expansion, map_sum]
  simp_rw [coeff_C_mul, coeff_X_pow]
  have he : (∑ T ∈ S.powerset,
      (-1 : ℂ) ^ T.card * if n = ∑ v ∈ T, d v then 1 else 0) =
      ∑ T ∈ squarefreeDegreeSubsets S d n, (-1 : ℂ) ^ T.card := by
    rw [squarefreeDegreeSubsets, sum_filter]
    apply sum_congr rfl
    intro T _
    by_cases h : ∑ v ∈ T, d v = n
    · simp only [h, if_true, mul_one]
    · simp only [h, Ne.symm h, if_false, mul_zero]
  rw [he]
  simp only [neg_one_pow_eq_ite, sum_ite, sum_const, nsmul_eq_mul, mul_one, mul_neg,
    evenSquarefreeDivisorCount, oddSquarefreeDivisorCount, sub_eq_add_neg]

#print axioms squarefreeEuler_expansion
#print axioms coeff_squarefreeEuler_eq_counts
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
