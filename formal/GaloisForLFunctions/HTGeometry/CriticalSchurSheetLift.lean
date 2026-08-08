import GaloisForLFunctions.HTGeometry.CriticalSchurMarkedReduction
import GaloisForLFunctions.HTGeometry.ValuationCriticalFibreLift

/-!
# Integral Schur-place lifts of all actual geometric sheets

Marked residue nonvanishing and projective boundary exclusion make every actual geometric sheet
integral at the chosen normal-closure Schur valuation.  This file constructs the integral lift,
proves it remains injective before reduction, and defines the actual reduced sheet label.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

private abbrev SchurValuationRing
    (K : Type*) [Field K] [CharZero K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  criticalNormalClosureSchurValuationSubring K hm hn

/-- Actual normal-closure critical fibre presented using the integral Schur tail models. -/
abbrev CriticalNormalClosureSchurFieldFibre
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  criticalFibre (criticalNormalClosure K m n) m n
    ((criticalNormalClosureSchurRawTailIntegral K hm hn).map
      (SchurValuationRing K m n hm hn).subtype)
    ((criticalNormalClosureSchurReciprocalTailIntegral K hm hn).map
      (SchurValuationRing K m n hm hn).subtype)

/-- Every actual geometric sheet as a point of the Schur-presented normal-closure fibre. -/
noncomputable def criticalGeometricSheetToSchurFieldFibre
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricSheet K m n → CriticalNormalClosureSchurFieldFibre K hm hn := by
  intro σ
  let p := criticalGeometricSheetToNormalFibre K m n σ
  refine ⟨p.1, p.2.1, p.2.2.1, ?_⟩
  rw [map_criticalNormalClosureSchurRawTailIntegral K hm hn,
    map_criticalNormalClosureSchurReciprocalTailIntegral K hm hn]
  exact p.2.2.2

/-- Every low coefficient of every actual sheet is integral at the upper Schur place. -/
theorem criticalGeometricSheetToSchurFieldFibre_coefficients_mem
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (p : CriticalNormalClosureSchurFieldFibre K (by omega) (by omega)) :
    (∀ i : Fin m, p.1.1.coeff i ∈
      SchurValuationRing K m n (by omega) (by omega)) ∧
      ∀ j : Fin n, p.1.2.coeff j ∈
        SchurValuationRing K m n (by omega) (by omega) := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  exact valuationSubring_criticalFibre_coefficients_mem_of_marked_reduction
    (SchurValuationRing K m n hm0 hn0) hm0 hn0
    (criticalNormalClosureSchurRawTailIntegral K hm0 hn0)
    (criticalNormalClosureSchurReciprocalTailIntegral K hm0 hn0)
    (X_pow_dvd_reduced_criticalNormalClosureSchurRawTailIntegral K hm0 hn0)
    (X_pow_dvd_reduced_criticalNormalClosureSchurReciprocalTailIntegral K hm0 hn0)
    (reduced_criticalNormalClosureSchurRawTailIntegral_coeff_marked_ne_zero K hm hn)
    (reduced_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked_ne_zero K hm hn)
    p

/-- Integral Schur-place representative of every actual geometric sheet. -/
noncomputable def criticalGeometricSheetToSchurFibre
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    criticalGeometricSheet K m n →
      criticalFibre (SchurValuationRing K m n (by omega) (by omega)) m n
        (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
        (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega)) := by
  intro σ
  let p := criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ
  exact valuationSubringCriticalFibreLift
    (SchurValuationRing K m n (by omega) (by omega))
    (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
    (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega))
    p (criticalGeometricSheetToSchurFieldFibre_coefficients_mem K hm hn p)

theorem criticalGeometricSheetToSchurFieldFibre_injective
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalGeometricSheetToSchurFieldFibre K hm hn) := by
  intro σ τ hστ
  have hA := congrArg (fun p => p.1.1) hστ
  have hB := congrArg (fun p => p.1.2) hστ
  change (criticalSourceRawLow K m n).map σ.toRingHom =
    (criticalSourceRawLow K m n).map τ.toRingHom at hA
  change (criticalSourceReciprocalLow K m n).map σ.toRingHom =
    (criticalSourceReciprocalLow K m n).map τ.toRingHom at hB
  apply criticalGeometricSheetToNormalFibre_injective K m n
  apply Subtype.ext
  exact Prod.ext hA hB

theorem criticalFibreMap_criticalGeometricSheetToSchurFibre
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) :
    criticalFibreMap
        (SchurValuationRing K m n (by omega) (by omega)).subtype m n
        (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
        (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega))
        (criticalGeometricSheetToSchurFibre K hm hn σ) =
      criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ := by
  exact criticalFibreMap_valuationSubringCriticalFibreLift
    (SchurValuationRing K m n (by omega) (by omega))
    (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
    (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega))
    (criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ)
    (criticalGeometricSheetToSchurFieldFibre_coefficients_mem K hm hn
      (criticalGeometricSheetToSchurFieldFibre K (by omega) (by omega) σ))

theorem criticalGeometricSheetToSchurFibre_injective
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    Function.Injective (criticalGeometricSheetToSchurFibre K hm hn) := by
  intro σ τ hστ
  apply criticalGeometricSheetToSchurFieldFibre_injective K (by omega) (by omega)
  have hmap := congrArg
    (criticalFibreMap
      (SchurValuationRing K m n (by omega) (by omega)).subtype m n
      (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
      (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega))) hστ
  simpa only [criticalFibreMap_criticalGeometricSheetToSchurFibre K hm hn] using hmap

/-- Actual residue-fibre label of a geometric sheet at the generic Schur place. -/
noncomputable def criticalGeometricSheetToSchurReducedFibre
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    criticalGeometricSheet K m n →
      criticalFibre
        (IsLocalRing.ResidueField
          (SchurValuationRing K m n (by omega) (by omega))) m n
        ((criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega)).map
          (IsLocalRing.residue (SchurValuationRing K m n (by omega) (by omega))))
        ((criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega)).map
          (IsLocalRing.residue (SchurValuationRing K m n (by omega) (by omega)))) :=
  criticalFibreMap
    (IsLocalRing.residue (SchurValuationRing K m n (by omega) (by omega))) m n
    (criticalNormalClosureSchurRawTailIntegral K (by omega) (by omega))
    (criticalNormalClosureSchurReciprocalTailIntegral K (by omega) (by omega)) ∘
      criticalGeometricSheetToSchurFibre K hm hn

end

end GaloisForLFunctions.HTGeometry
