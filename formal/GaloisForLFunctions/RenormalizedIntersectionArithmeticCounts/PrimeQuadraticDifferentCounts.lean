import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeQuadraticDiscriminant
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.ThickenedArithmeticIntersections
import GaloisForLFunctions.HTGeometry.SingularIntegralCokernel

/-!
# Different intersections of the prime-quadratic family

The finite-place object is the actual ring `ℤ[X]/(F_n,F_n')`. Its cardinality
is the absolute discriminant when finite, and zero exactly when the ring is
infinite. Prime-local order multiplicities and the archimedean discriminant
height belong to this same integral equation.
-/

noncomputable section
open Polynomial ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HTGeometry

/-- The resultant counts the actual intersection also in the nonproper case. -/
theorem arithmeticIntersectionCount_eq_resultant_all {P Q : ℤ[X]} (hP : P.Monic) :
    arithmeticIntersectionCount P Q = (P.resultant Q).natAbs := by
  rw [arithmeticIntersectionCount,
    ← Nat.card_congr (intersectionRelationQuotientEquiv hP).toEquiv,
    LinearMap.card_quotient_range_eq_natAbs_det_all, intersectionRelationMap_det]

/-- A zero resultant gives an infinite ring, rather than an empty intersection. -/
theorem arithmeticIntersectionRing_infinite {P Q : ℤ[X]} (hP : P.Monic)
    (h : P.resultant Q = 0) : Infinite (ArithmeticIntersectionRing P Q) := by
  letI := LinearMap.infinite_quotient_range_of_det_eq_zero (intersectionRelationMap P Q)
    (by rw [intersectionRelationMap_det, h])
  exact Infinite.of_injective (intersectionRelationQuotientEquiv hP)
    (intersectionRelationQuotientEquiv hP).injective

/-- The different quotient of a monic integral equation has absolute discriminant cardinality. -/
theorem monicDifferent_count {P : ℤ[X]} (hP : P.Monic) :
    arithmeticIntersectionCount P P.derivative = P.discr.natAbs := by
  rw [arithmeticIntersectionCount_eq_resultant_all hP, monic_resultant_derivative hP,
    Int.natAbs_mul, Int.natAbs_pow]
  simp only [Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]

/-- The same polynomial defines the orientation cover and the finite-place different. -/
abbrev PrimeQuadraticDifferent (n : ℕ) :=
  ArithmeticIntersectionRing (primeQuadraticPolynomial n) (primeQuadraticPolynomial n).derivative

/-- An actual arithmetic count, including zero as the convention for an infinite ring. -/
def primeQuadraticDifferentCount (n : ℕ) : ℕ := Nat.card (PrimeQuadraticDifferent n)

/-- The count is derived from the independent integral equation. -/
theorem primeQuadraticDifferentCount_discr (n : ℕ) :
    primeQuadraticDifferentCount n = (primeQuadraticPolynomial n).discr.natAbs :=
  monicDifferent_count (primeQuadraticPolynomial_monic n)

/-- The finite-place count retains the exact fourth power of every cross-factor difference. -/
theorem primeQuadraticDifferentCount_eq {n : ℕ} (hn : n ≠ 0) :
    primeQuadraticDifferentCount n =
      4 ^ n.primeFactorsList.length * n * (primeQuadraticVandermonde n).natAbs ^ 4 := by
  rw [primeQuadraticDifferentCount_discr, primeQuadraticPolynomial_discr hn]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast]
  rfl

private theorem primeQuadraticDifferent_resultant_ne_zero {n : ℕ} (hs : Squarefree n) :
    (primeQuadraticPolynomial n).resultant (primeQuadraticPolynomial n).derivative ≠ 0 := by
  rw [monic_resultant_derivative (primeQuadraticPolynomial_monic n)]
  exact mul_ne_zero (pow_ne_zero _ (by decide : (-1 : ℤ) ≠ 0))
    ((primeQuadraticPolynomial_discr_ne_zero hs.ne_zero).mpr hs)

/-- Squarefree conductors give proper finite different intersections. -/
theorem primeQuadraticDifferent_finite {n : ℕ} (hs : Squarefree n) :
    Finite (PrimeQuadraticDifferent n) :=
  arithmeticIntersectionRing_finite (primeQuadraticPolynomial_monic n)
    (primeQuadraticDifferent_resultant_ne_zero hs)

/-- Repeated prime factors give infinite different quotients. -/
theorem primeQuadraticDifferent_infinite {n : ℕ} (hn : n ≠ 0) (hs : ¬ Squarefree n) :
    Infinite (PrimeQuadraticDifferent n) := by
  apply arithmeticIntersectionRing_infinite (primeQuadraticPolynomial_monic n)
  have hd : (primeQuadraticPolynomial n).discr = 0 := by
    by_contra h
    exact hs ((primeQuadraticPolynomial_discr_ne_zero hn).mp h)
  rw [monic_resultant_derivative (primeQuadraticPolynomial_monic n), hd, mul_zero]

/-- Finite-place multiplicities sum to the archimedean absolute discriminant of the same equation. -/
theorem primeQuadraticDifferent_productFormula {n : ℕ} (hs : Squarefree n) :
    0 < primeQuadraticDifferentCount n ∧
    (primeQuadraticDifferentCount n).factorization.sum (fun p k => (k : ℝ) * Real.log p) =
      Real.log |((primeQuadraticPolynomial n).discr : ℝ)| := by
  have h := arithmeticIntersectionHeight_prime_sum (primeQuadraticPolynomial_monic n)
    (primeQuadraticDifferent_resultant_ne_zero hs)
  refine ⟨h.1, ?_⟩
  change (arithmeticIntersectionCount (primeQuadraticPolynomial n)
    (primeQuadraticPolynomial n).derivative).factorization.sum
      (fun p k => (k : ℝ) * Real.log p) = _
  rw [← h.2, arithmeticIntersectionHeight, monicDifferent_count (primeQuadraticPolynomial_monic n)]
  simp only [Nat.cast_natAbs, Int.cast_abs]

/-- Conductor multiplication is literal multiplication of the integral defining equations. -/
theorem primeQuadraticPolynomial_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeQuadraticPolynomial (m * n) = primeQuadraticPolynomial m * primeQuadraticPolynomial n := by
  have h := ((Nat.perm_primeFactorsList_mul hm hn).map
    (fun p : ℕ => arithmeticQuadratic (p : ℤ))).prod_eq
  simpa only [primeQuadraticPolynomial, quadraticFactorProduct, List.map_map,
    Function.comp_def, List.map_append, List.prod_append] using h

/-- Different counts have an exact cross-intersection correction under conductor multiplication. -/
theorem primeQuadraticDifferentCount_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    primeQuadraticDifferentCount (m * n) =
      primeQuadraticDifferentCount m * primeQuadraticDifferentCount n *
        ((primeQuadraticPolynomial m).resultant (primeQuadraticPolynomial n)).natAbs ^ 2 := by
  rw [primeQuadraticDifferentCount_discr, primeQuadraticPolynomial_mul hm hn,
    discr_mul_of_monic (primeQuadraticPolynomial_monic m) (primeQuadraticPolynomial_monic n)]
  simp only [Int.natAbs_mul, Int.natAbs_pow, primeQuadraticDifferentCount_discr]

/-- Every nontrivial conductor square leaves the finite different-count locus. -/
theorem primeQuadraticDifferent_square_infinite {n : ℕ} (hn : 1 < n) :
    Infinite (PrimeQuadraticDifferent (n * n)) := by
  apply primeQuadraticDifferent_infinite (Nat.mul_ne_zero (by omega) (by omega))
  intro hs
  have hu : IsUnit n := hs n (dvd_refl (n*n))
  have := Nat.isUnit_iff.mp hu
  omega

#print axioms arithmeticIntersectionCount_eq_resultant_all
#print axioms arithmeticIntersectionRing_infinite
#print axioms monicDifferent_count
#print axioms primeQuadraticDifferentCount_eq
#print axioms primeQuadraticDifferent_finite
#print axioms primeQuadraticDifferent_infinite
#print axioms primeQuadraticDifferent_productFormula
#print axioms primeQuadraticPolynomial_mul
#print axioms primeQuadraticDifferentCount_mul
#print axioms primeQuadraticDifferent_square_infinite

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
