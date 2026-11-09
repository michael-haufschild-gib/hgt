import GaloisForLFunctions.HTGeometry.MonicTraceCokernel
import GaloisForLFunctions.HTGeometry.IntegralTraceCokernel
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.PrimeQuadraticDifferentCounts

/-!
# Trace counts of the prime-quadratic orders

The trace cokernel of `ℤ[X]/(F_n)` is integrally equivalent to the actual
different intersection. Its cardinality and product-formula height are
therefore derived from that order, including at repeated prime factors.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HTGeometry

/-- The full monogenic order has the polynomial's absolute trace discriminant, even when singular. -/
theorem monic_trace_discriminant_natAbs {f : ℤ[X]} (hf : f.Monic) :
    (Algebra.discr ℤ (AdjoinRoot.powerBasis' hf).basis).natAbs = f.discr.natAbs := by
  letI := hf.free_adjoinRoot
  letI := hf.finite_adjoinRoot
  rw [← card_traceCokernel_eq_natAbs_discr (AdjoinRoot.powerBasis' hf).basis]
  change Nat.card (MonicTraceCokernel f) = _
  rw [Nat.card_congr (monicTraceCokernelEquivDifferent hf).toEquiv]
  exact monicDifferent_count hf

/-- The actual dual lattice modulo the image of the prime-quadratic trace pairing. -/
abbrev PrimeQuadraticTraceQuotient (n : ℕ) := MonicTraceCokernel (primeQuadraticPolynomial n)

/-- The trace discriminant of the monomial basis of the actual integral order. -/
def primeQuadraticTraceDiscriminant (n : ℕ) : ℤ :=
  Algebra.discr ℤ (AdjoinRoot.powerBasis' (primeQuadraticPolynomial_monic n)).basis

/-- The cardinality of the actual trace quotient, with zero for an infinite quotient. -/
def primeQuadraticTraceCount (n : ℕ) : ℕ := Nat.card (PrimeQuadraticTraceQuotient n)

/-- The trace and different counts come from isomorphic integral modules. -/
def primeQuadraticTraceQuotientEquivDifferent (n : ℕ) :
    PrimeQuadraticTraceQuotient n ≃ₗ[ℤ] PrimeQuadraticDifferent n :=
  monicTraceCokernelEquivDifferent (primeQuadraticPolynomial_monic n)

theorem primeQuadraticTraceCount_eq (n : ℕ) :
    primeQuadraticTraceCount n = primeQuadraticDifferentCount n :=
  Nat.card_congr (primeQuadraticTraceQuotientEquivDifferent n).toEquiv

theorem primeQuadraticTraceDiscriminant_natAbs (n : ℕ) :
    (primeQuadraticTraceDiscriminant n).natAbs = (primeQuadraticPolynomial n).discr.natAbs :=
  monic_trace_discriminant_natAbs (primeQuadraticPolynomial_monic n)

theorem primeQuadraticTraceCount_discriminant (n : ℕ) :
    primeQuadraticTraceCount n = (primeQuadraticTraceDiscriminant n).natAbs := by
  rw [primeQuadraticTraceCount_eq, primeQuadraticDifferentCount_discr,
    primeQuadraticTraceDiscriminant_natAbs]

/-- Repeated factors are retained: their trace cokernels are infinite. -/
theorem primeQuadraticTraceQuotient_infinite {n : ℕ} (hn : n ≠ 0) (hs : ¬ Squarefree n) :
    Infinite (PrimeQuadraticTraceQuotient n) := by
  letI := primeQuadraticDifferent_infinite hn hs
  exact Infinite.of_injective (primeQuadraticTraceQuotientEquivDifferent n).symm
    (primeQuadraticTraceQuotientEquivDifferent n).symm.injective

theorem primeQuadraticTraceQuotient_finite {n : ℕ} (hs : Squarefree n) :
    Finite (PrimeQuadraticTraceQuotient n) := by
  letI := primeQuadraticDifferent_finite hs
  exact Finite.of_injective (primeQuadraticTraceQuotientEquivDifferent n)
    (primeQuadraticTraceQuotientEquivDifferent n).injective

/-- Prime-local trace-index multiplicities and the archimedean trace discriminant obey one product formula. -/
theorem primeQuadraticTrace_productFormula {n : ℕ} (hs : Squarefree n) :
    0 < primeQuadraticTraceCount n ∧
    (primeQuadraticTraceCount n).factorization.sum (fun p k => (k : ℝ) * Real.log p) =
      Real.log |(primeQuadraticTraceDiscriminant n : ℝ)| := by
  have ha : |(primeQuadraticTraceDiscriminant n : ℝ)| =
      |((primeQuadraticPolynomial n).discr : ℝ)| := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      congrArg (fun k : ℕ => (k : ℝ)) (primeQuadraticTraceDiscriminant_natAbs n)
  rw [primeQuadraticTraceCount_eq, ha]
  exact primeQuadraticDifferent_productFormula hs

#print axioms monic_trace_discriminant_natAbs
#print axioms primeQuadraticTraceQuotientEquivDifferent
#print axioms primeQuadraticTraceCount_discriminant
#print axioms primeQuadraticTraceQuotient_infinite
#print axioms primeQuadraticTraceQuotient_finite
#print axioms primeQuadraticTrace_productFormula
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
