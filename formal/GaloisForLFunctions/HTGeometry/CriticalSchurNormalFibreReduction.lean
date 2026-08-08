import GaloisForLFunctions.HTGeometry.CriticalGeometricNormalFibre
import GaloisForLFunctions.HTGeometry.CriticalNormalClosureSchurValuation
import GaloisForLFunctions.HTGeometry.CriticalSchurTailIntegrality

/-!
# Reduction of the actual critical normal fibre at the Schur place

The integral observation tails constructed at the source Schur divisor are transported through
the chosen extension valuation in the actual normal closure.  This supplies exact integral models
of both tails over the normal-closure valuation ring.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- Every element of the restricted observation valuation ring maps into the chosen extension
valuation ring in the normal closure. -/
theorem criticalNormalClosureSchurValuationSubring_observation_mem
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : criticalSchurObservationValuationSubring K hm hn) :
    criticalObservationNormalClosureMap K m n x ∈
      criticalNormalClosureSchurValuationSubring K hm hn := by
  let y : criticalSchurSourceValuationSubring K hm hn :=
    ⟨algebraMap (criticalObservationField K m n) (criticalSourceField K m n) x,
      (mem_criticalSchurObservationValuationSubring_iff K hm hn x).mp x.property⟩
  have hy := criticalNormalClosureSchurValuationSubring_source_mem K hm hn y
  convert hy using 1
  exact (criticalSourceNormalClosureEmbedding K m n).commutes x

/-- Integral embedding of the Schur observation valuation ring into the chosen normal-closure
valuation ring. -/
noncomputable def criticalSchurObservationValuationToNormalClosure
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurObservationValuationSubring K hm hn →+*
      criticalNormalClosureSchurValuationSubring K hm hn :=
  ((criticalObservationNormalClosureMap K m n).comp
    (criticalSchurObservationValuationSubring K hm hn).subtype).codRestrict
      (criticalNormalClosureSchurValuationSubring K hm hn).toSubring
      (criticalNormalClosureSchurValuationSubring_observation_mem K hm hn)

/-- Raw observation tail as a polynomial over the chosen normal-closure valuation ring. -/
noncomputable def criticalNormalClosureSchurRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurValuationSubring K hm hn)[X] :=
  (criticalSchurObservationRawTailIntegral K hm hn).map
    (criticalSchurObservationValuationToNormalClosure K hm hn)

/-- Reciprocal observation tail as a polynomial over the chosen normal-closure valuation ring. -/
noncomputable def criticalNormalClosureSchurReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurValuationSubring K hm hn)[X] :=
  (criticalSchurObservationReciprocalTailIntegral K hm hn).map
    (criticalSchurObservationValuationToNormalClosure K hm hn)

@[simp] theorem map_criticalNormalClosureSchurRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurRawTailIntegral K hm hn).map
        (criticalNormalClosureSchurValuationSubring K hm hn).subtype =
      (criticalObservationRawTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  apply Polynomial.ext
  intro k
  simp [criticalNormalClosureSchurRawTailIntegral,
    criticalSchurObservationValuationToNormalClosure]
  congr 1
  exact Polynomial.coeff_toSubring _ _ _

@[simp] theorem map_criticalNormalClosureSchurReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurReciprocalTailIntegral K hm hn).map
        (criticalNormalClosureSchurValuationSubring K hm hn).subtype =
      (criticalObservationReciprocalTail K m n).map
        (criticalObservationNormalClosureMap K m n) := by
  apply Polynomial.ext
  intro k
  simp [criticalNormalClosureSchurReciprocalTailIntegral,
    criticalSchurObservationValuationToNormalClosure]
  congr 1
  exact Polynomial.coeff_toSubring _ _ _

theorem X_pow_dvd_criticalNormalClosureSchurRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalNormalClosureSchurValuationSubring K hm hn)[X]) ^ m ∣
      criticalNormalClosureSchurRawTailIntegral K hm hn := by
  simpa [criticalNormalClosureSchurRawTailIntegral] using
    Polynomial.map_dvd (criticalSchurObservationValuationToNormalClosure K hm hn)
      (X_pow_dvd_criticalSchurObservationRawTailIntegral K hm hn)

theorem X_pow_dvd_criticalNormalClosureSchurReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (criticalNormalClosureSchurValuationSubring K hm hn)[X]) ^ n ∣
      criticalNormalClosureSchurReciprocalTailIntegral K hm hn := by
  simpa [criticalNormalClosureSchurReciprocalTailIntegral] using
    Polynomial.map_dvd (criticalSchurObservationValuationToNormalClosure K hm hn)
      (X_pow_dvd_criticalSchurObservationReciprocalTailIntegral K hm hn)

theorem X_pow_dvd_reduced_criticalNormalClosureSchurRawTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (IsLocalRing.ResidueField
      (criticalNormalClosureSchurValuationSubring K hm hn))[X]) ^ m ∣
      (criticalNormalClosureSchurRawTailIntegral K hm hn).map
        (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)) := by
  simpa using Polynomial.map_dvd
    (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn))
    (X_pow_dvd_criticalNormalClosureSchurRawTailIntegral K hm hn)

theorem X_pow_dvd_reduced_criticalNormalClosureSchurReciprocalTailIntegral
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (IsLocalRing.ResidueField
      (criticalNormalClosureSchurValuationSubring K hm hn))[X]) ^ n ∣
      (criticalNormalClosureSchurReciprocalTailIntegral K hm hn).map
        (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)) := by
  simpa using Polynomial.map_dvd
    (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn))
    (X_pow_dvd_criticalNormalClosureSchurReciprocalTailIntegral K hm hn)

end

end GaloisForLFunctions.HTGeometry
