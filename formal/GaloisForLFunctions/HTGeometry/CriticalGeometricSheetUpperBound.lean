import GaloisForLFunctions.HTGeometry.AdicCriticalFibreUpperBound
import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcResidueCharacteristic
import GaloisForLFunctions.HTGeometry.CriticalNormalClosureArcSheetLiftInjective
import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreReductionInjective

/-!
# Valuative upper bound for actual critical geometric sheets

Every geometric sheet has an integral lift at the common-scale normal-closure DVR.  Reduction is
injective there and lands in the pure factorisation fibre, giving the critical binomial ceiling for
the degree of the actual source/observation extension.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private abbrev ArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalNormalClosureArcValuationRing K m n hm hn

theorem X_pow_dvd_criticalNormalClosureArcRawTail
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (ArcValuationRing K m n hm hn)[X]) ^ m ∣
      criticalNormalClosureArcRawTail K hm hn := by
  classical
  rw [criticalNormalClosureArcRawTail]
  exact X_pow_dvd_shiftedFiniteTail m
    (criticalNormalClosureArcRawCoefficient K hm hn)

theorem X_pow_dvd_criticalNormalClosureArcReciprocalTail
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (X : (ArcValuationRing K m n hm hn)[X]) ^ n ∣
      criticalNormalClosureArcReciprocalTail K hm hn := by
  classical
  rw [criticalNormalClosureArcReciprocalTail]
  exact X_pow_dvd_shiftedFiniteTail n
    (criticalNormalClosureArcReciprocalCoefficient K hm hn)

/-- Reduction of an actual geometric sheet to a pure critical factorisation. -/
noncomputable def criticalGeometricSheetArcReduction
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n →
      MonicFactorization
        (pureCriticalCyclicPolynomial
          (K := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) (m + n))
        m n := fun σ =>
  criticalFibreResidueReduction
    (IsLocalRing.residue (ArcValuationRing K m n hm hn)) hm hn
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn)
    (criticalNormalClosureArcRawTail_map_residue K hm hn)
    (criticalNormalClosureArcReciprocalTail_map_residue K hm hn)
    (criticalGeometricSheetToArcFibre K hm hn σ)

theorem criticalGeometricSheetArcReduction_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalGeometricSheetArcReduction K hm hn) := by
  apply (criticalFibreResidueReduction_injective_of_dvr hm hn
    (criticalNormalClosureArcRawTail K hm hn)
    (criticalNormalClosureArcReciprocalTail K hm hn)
    (X_pow_dvd_criticalNormalClosureArcRawTail K hm hn)
    (X_pow_dvd_criticalNormalClosureArcReciprocalTail K hm hn)
    (criticalNormalClosureArcRawTail_map_residue K hm hn)
    (criticalNormalClosureArcReciprocalTail_map_residue K hm hn)
    (show (m : IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)) + n ≠ 0 by
      rw [← Nat.cast_add]
      exact Nat.cast_ne_zero.mpr (by omega : m + n ≠ 0))).comp
  exact criticalGeometricSheetToArcFibre_injective K hm hn

/-- The actual geometric sheet count is at most the critical binomial multiplicity. -/
theorem natCard_criticalGeometricSheet_le_criticalHorizonMultiplicity
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalGeometricSheet K m n) ≤ criticalHorizonMultiplicity m n := by
  let k := IsLocalRing.ResidueField (ArcValuationRing K m n hm hn)
  letI : Finite (MonicFactorization
      (pureCriticalCyclicPolynomial (K := k) (m + n)) m n) :=
    finite_pureCriticalMonicFactorization k (by omega)
  exact le_trans
    (Nat.card_le_card_of_injective
      (criticalGeometricSheetArcReduction K hm hn)
      (criticalGeometricSheetArcReduction_injective K hm hn))
    (natCard_pureCriticalMonicFactorization_le k (by omega))

/-- The actual source/observation extension degree is at most the critical binomial multiplicity. -/
theorem finrank_criticalSourceField_le_criticalHorizonMultiplicity
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Module.finrank (criticalObservationField K m n) (criticalSourceField K m n) ≤
      criticalHorizonMultiplicity m n := by
  rw [← natCard_criticalGeometricSheet_eq_finrank K hm hn]
  exact natCard_criticalGeometricSheet_le_criticalHorizonMultiplicity K hm hn

end


end GaloisForLFunctions.HTGeometry
