import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHorizonStability
import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGlobalReflectedComparison
import GaloisForLFunctions.RHTower.XiDivisorDiagonalTraceClass

/-!
# Global atomic non-erasure and its stability fracture

One fixed reflected Meyer Gaussian supplies a square-summable horizon grade
which is nonzero at every multiplicity-exact Xi divisor copy.  For any fixed
prime label, the global adaptive reflected comparison is isometric and its
codiagonal has lower modulus `3/4`.

Combining those independent constructions gives one source-derived global
record whose resolved fibre and observed codiagonal fibre are both nonzero at
every divisor copy.  Every source-weighted divisor basis atom likewise
survives both maps.  This is unconditional global atomic non-erasure.

The result also records the sharp boundary: the Gaussian grade tends to zero
cofinally and has no positive uniform lower modulus.  Thus atomic non-erasure
is already closed, while stable centered-flow capacity conservation remains a
separate problem.
-/

open Complex

namespace RHTower.DeningerMeyerGaussianGreen

noncomputable section

/-- One fixed source-derived resolved record containing every Gaussian-weighted
Xi divisor atom. -/
def reflectedGaussianGlobalAtomicResolvedRecord
    (p : Nat.Primes) : AdaptivePrimeNormalGlobalReflectedResolvedL2 :=
  adaptivePrimeNormalGlobalReflectedComparison p
    reflectedGaussianHorizonGradeL2

/-- Conservative codiagonal of the global Gaussian atomic record. -/
def reflectedGaussianGlobalAtomicObservedRecord
    (p : Nat.Primes) : AdaptivePrimeNormalGlobalReflectedCodiagonalL2 :=
  adaptivePrimeNormalGlobalReflectedCodiagonal p
    reflectedGaussianHorizonGradeL2

@[simp]
theorem reflectedGaussianGlobalAtomicResolvedRecord_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    reflectedGaussianGlobalAtomicResolvedRecord p q =
      reflectedGaussianHorizonGrade q •
        adaptivePrimeNormalReflectedResolvedUnit p q := by
  rw [reflectedGaussianGlobalAtomicResolvedRecord,
    adaptivePrimeNormalGlobalReflectedComparison_apply,
    reflectedGaussianHorizonGradeL2_apply]

@[simp]
theorem reflectedGaussianGlobalAtomicObservedRecord_apply
    (p : Nat.Primes) (q : XiZeroCopy) :
    reflectedGaussianGlobalAtomicObservedRecord p q =
      reflectedGaussianHorizonGrade q •
        adaptivePrimeNormalReflectedCodiagonal q
          (lp.single (E := fun _ : Nat.Primes => ℂ) 1 p 1) := by
  rw [reflectedGaussianGlobalAtomicObservedRecord,
    adaptivePrimeNormalGlobalReflectedCodiagonal_apply,
    reflectedGaussianHorizonGradeL2_apply]

/-- Every resolved fibre of the one global source record is nonzero. -/
theorem reflectedGaussianGlobalAtomicResolvedRecord_apply_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    reflectedGaussianGlobalAtomicResolvedRecord p q ≠ 0 := by
  rw [reflectedGaussianGlobalAtomicResolvedRecord_apply]
  apply smul_ne_zero (reflectedGaussianHorizonGrade_ne_zero q)
  intro hzero
  have hnorm := norm_adaptivePrimeNormalReflectedResolvedUnit p q
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Every conservative observed fibre of the same global record is nonzero. -/
theorem reflectedGaussianGlobalAtomicObservedRecord_apply_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    reflectedGaussianGlobalAtomicObservedRecord p q ≠ 0 := by
  rw [reflectedGaussianGlobalAtomicObservedRecord_apply]
  exact smul_ne_zero
    (reflectedGaussianHorizonGrade_ne_zero q)
    (adaptivePrimeNormalReflectedCodiagonal_single_ne_zero q p)

/-- The global source record belongs to the closed reflected common-test
sector selected before observation. -/
theorem reflectedGaussianGlobalAtomicResolvedRecord_mem_sector
    (p : Nat.Primes) :
    reflectedGaussianGlobalAtomicResolvedRecord p ∈
      adaptivePrimeNormalGlobalReflectedSector p := by
  exact ⟨reflectedGaussianHorizonGradeL2, rfl⟩

/-- The source-weighted multiplicity-exact atom at one divisor copy. -/
def reflectedGaussianWeightedXiAtom (q : XiZeroCopy) : XiDivisorL2 :=
  reflectedGaussianHorizonGrade q • xiDivisorHilbertBasis q

theorem reflectedGaussianWeightedXiAtom_ne_zero (q : XiZeroCopy) :
    reflectedGaussianWeightedXiAtom q ≠ 0 := by
  rw [reflectedGaussianWeightedXiAtom]
  apply smul_ne_zero (reflectedGaussianHorizonGrade_ne_zero q)
  intro hzero
  have hnorm := xiDivisorHilbertBasis.orthonormal.1 q
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Every individual source-weighted atom survives the global resolved
comparison. -/
theorem reflectedGaussianWeightedXiAtom_resolved_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalGlobalReflectedComparison p
        (reflectedGaussianWeightedXiAtom q) ≠ 0 := by
  intro hzero
  apply reflectedGaussianWeightedXiAtom_ne_zero q
  apply (adaptivePrimeNormalGlobalReflectedComparison p).injective
  simpa using hzero

/-- Every individual source-weighted atom also survives conservative
codiagonal observation. -/
theorem reflectedGaussianWeightedXiAtom_observed_ne_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    adaptivePrimeNormalGlobalReflectedCodiagonal p
        (reflectedGaussianWeightedXiAtom q) ≠ 0 := by
  intro hzero
  apply reflectedGaussianWeightedXiAtom_ne_zero q
  apply adaptivePrimeNormalGlobalReflectedCodiagonal_injective p
  simpa using hzero

/-- Quantitative global retention of the source-derived record. -/
theorem reflectedGaussianGlobalAtomicObservedRecord_lower
    (p : Nat.Primes) :
    (3 / 4 : ℝ) * ‖reflectedGaussianHorizonGradeL2‖ ≤
      ‖reflectedGaussianGlobalAtomicObservedRecord p‖ := by
  exact adaptivePrimeNormalGlobalReflectedCodiagonal_lower p
    reflectedGaussianHorizonGradeL2

/-- **Global atomic non-erasure with sharp stability fracture.**  One fixed
source record and its conservative observation are fibrewise nonzero on every
Xi copy and retain the global `3/4` lower modulus, although the source grade
itself has no positive coefficientwise lower bound. -/
theorem reflectedGaussian_globalAtomicNonErasure
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      reflectedGaussianGlobalAtomicResolvedRecord p q ≠ 0) ∧
    (∀ q : XiZeroCopy,
      reflectedGaussianGlobalAtomicObservedRecord p q ≠ 0) ∧
    (3 / 4 : ℝ) * ‖reflectedGaussianHorizonGradeL2‖ ≤
      ‖reflectedGaussianGlobalAtomicObservedRecord p‖ ∧
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ q : XiZeroCopy, c ≤ ‖reflectedGaussianHorizonGrade q‖ := by
  exact ⟨reflectedGaussianGlobalAtomicResolvedRecord_apply_ne_zero p,
    reflectedGaussianGlobalAtomicObservedRecord_apply_ne_zero p,
    reflectedGaussianGlobalAtomicObservedRecord_lower p,
    not_exists_uniform_lower_bound_reflectedGaussianHorizonGrade⟩

end

end RHTower.DeningerMeyerGaussianGreen
