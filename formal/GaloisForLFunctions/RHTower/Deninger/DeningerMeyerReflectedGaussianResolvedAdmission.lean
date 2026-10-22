import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHorizonAdmission
import GaloisForLFunctions.RHTower.Deninger.DeningerCompletedXiHellingerGammaResolvedProvenanceCoface

/-!
# Resolved admission of the reflected-Gaussian singular Xi residue

The fixed reflected Meyer Gaussian supplies a source-defined, nonvanishing,
square-summable horizon grade.  This module carries the resulting admitted
singular Xi residue through actual Calderon--Witt incidence and then through
the resolved Hellinger--Gamma provenance quotient.

Every divisor coefficient remains a nonzero multiple of the fixed actual
cross-prime incidence witness.  Before codiagonalization it is the unsquared
antidiagonal defect; direct codiagonalization kills it, while the provenance
quotient has a left inverse and retains a nonzero class at every displacement.

This closes source grading, singular `ell^(2 : ℕ)` admission, coefficient-faithful
incidence, and resolved-coface conservativity for this fixed source.  It does
not identify the resulting completed vector with the actual global Green
resolved range or prove the remaining Hermitian Gram domination.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeningerMeyerGaussianGreen

noncomputable section

/-- The source-graded singular residue as an honest completed Xi vector. -/
def reflectedGaussianHorizonAdmittedResidue :
    DeningerArithmeticCompletedH1 :=
  ⟨fun q => reflectedGaussianHorizonAdmissionWeight q *
      xiGaussianGammaResiduePacket q,
    HilbertSchmidt.memℓp_of_sq
      summable_reflectedGaussianHorizonAdmissionPacket⟩

@[simp]
theorem reflectedGaussianHorizonAdmittedResidue_apply (q : XiZeroCopy) :
    reflectedGaussianHorizonAdmittedResidue q =
      reflectedGaussianHorizonGrade q := by
  exact reflectedGaussianHorizonAdmissionWeight_mul_packet q

theorem reflectedGaussianHorizonAdmittedResidue_ne_zero
    (r : XiZeroCopy) :
    reflectedGaussianHorizonAdmittedResidue ≠ 0 := by
  intro hzero
  have hr := congrArg
    (fun x : DeningerArithmeticCompletedH1 => x r) hzero
  rw [reflectedGaussianHorizonAdmittedResidue_apply] at hr
  exact reflectedGaussianHorizonGrade_ne_zero r hr

/-- Calderon--Witt incidence completion of the admitted reflected-Gaussian source residue. -/
def reflectedGaussianHorizonAdmittedIncidence
    (p q : Nat.Primes) (hpq : p ≠ q) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
    reflectedGaussianHorizonAdmittedResidue

theorem reflectedGaussianHorizonAdmittedIncidence_sourceValue
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (reflectedGaussianHorizonAdmittedIncidence p q hpq) =
      reflectedGaussianHorizonGrade r •
        deningerCalderonWittCrossPrimeGammaWitness hpq := by
  rw [reflectedGaussianHorizonAdmittedIncidence,
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue_xi,
    reflectedGaussianHorizonAdmittedResidue_apply]

theorem reflectedGaussianHorizonAdmittedIncidence_sourceValue_ne_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (reflectedGaussianHorizonAdmittedIncidence p q hpq) ≠ 0 := by
  rw [reflectedGaussianHorizonAdmittedIncidence_sourceValue]
  exact smul_ne_zero
    (reflectedGaussianHorizonGrade_ne_zero r)
    (deningerCalderonWittCrossPrimeGammaWitness_ne_zero p q hpq)

theorem reflectedGaussianHorizonAdmittedIncidence_ne_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    reflectedGaussianHorizonAdmittedIncidence p q hpq ≠ 0 := by
  intro hzero
  apply reflectedGaussianHorizonAdmittedIncidence_sourceValue_ne_zero
    p q hpq r
  rw [hzero]
  exact map_zero _

/-- Before codiagonalization, the admitted source remains its nonzero oriented antidiagonal. -/
theorem reflectedGaussianHorizonAdmittedResolvedDefect
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    hellingerGammaResolvedProvenanceSourceDefectValue hpq r
        (hellingerGammaResolvedProvenanceInsertion
          (reflectedGaussianHorizonAdmittedIncidence p q hpq)) =
      resolvedDefectAntidiagonal (R := ℂ)
        (reflectedGaussianHorizonGrade r •
          deningerCalderonWittCrossPrimeGammaWitness hpq) := by
  change resolvedDefectAntidiagonal (R := ℂ)
      (deningerCalderonWittCrossPrimeXiIncidenceCompletionSourceValue
        p q hpq r
        (reflectedGaussianHorizonAdmittedIncidence p q hpq)) = _
  rw [reflectedGaussianHorizonAdmittedIncidence_sourceValue]

theorem reflectedGaussianHorizonAdmittedResolvedDefect_ne_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    hellingerGammaResolvedProvenanceSourceDefectValue hpq r
        (hellingerGammaResolvedProvenanceInsertion
          (reflectedGaussianHorizonAdmittedIncidence p q hpq)) ≠ 0 := by
  rw [reflectedGaussianHorizonAdmittedResolvedDefect]
  intro hzero
  have hfst := congrArg Prod.fst hzero
  simp only [resolvedDefectAntidiagonal, LinearMap.coe_mk,
    AddHom.coe_mk, Prod.fst_zero] at hfst
  exact (smul_ne_zero
    (reflectedGaussianHorizonGrade_ne_zero r)
    (deningerCalderonWittCrossPrimeGammaWitness_ne_zero p q hpq)) hfst

/-- Direct codiagonalization loses the same nonzero source defect. -/
theorem reflectedGaussianHorizonAdmittedResolvedDefect_codiagonal
    (p q : Nat.Primes) (hpq : p ≠ q) (r : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
      (hellingerGammaResolvedProvenanceSourceDefectValue hpq r
        (hellingerGammaResolvedProvenanceInsertion
          (reflectedGaussianHorizonAdmittedIncidence p q hpq))) = 0 := by
  rw [reflectedGaussianHorizonAdmittedResolvedDefect]
  simp [resolvedDefectCodiagonal, resolvedDefectAntidiagonal]

/-- Relative Hellinger--Gamma class retaining the admitted source before codiagonal loss. -/
def reflectedGaussianHorizonAdmittedResolvedClass
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :=
  hellingerGammaResolvedProvenanceQuotientSource hpq a
    (reflectedGaussianHorizonAdmittedIncidence p q hpq)

theorem reflectedGaussianHorizonAdmittedResolvedClass_projection
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    hellingerGammaResolvedProvenanceQuotientProjection hpq a
        (reflectedGaussianHorizonAdmittedResolvedClass p q hpq a) =
      reflectedGaussianHorizonAdmittedIncidence p q hpq := by
  exact hellingerGammaResolvedProvenanceQuotientProjection_source hpq a _

theorem reflectedGaussianHorizonAdmittedResolvedClass_ne_zero
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) (r : XiZeroCopy) :
    reflectedGaussianHorizonAdmittedResolvedClass p q hpq a ≠ 0 := by
  intro hzero
  have hinc : reflectedGaussianHorizonAdmittedIncidence p q hpq = 0 := by
    rw [← reflectedGaussianHorizonAdmittedResolvedClass_projection p q hpq a,
      hzero]
    exact map_zero _
  exact reflectedGaussianHorizonAdmittedIncidence_ne_zero p q hpq r hinc

end

end RHTower.DeningerMeyerGaussianGreen
