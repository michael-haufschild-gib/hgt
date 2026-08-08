import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaReduction

/-!
# Schur inertia on integral sheet coefficients

The normal-closure coefficient action restricts to the chosen upper valuation ring.  Its inertia
subgroup consequently fixes the residue of every integral coefficient of every actual sheet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- The integral raw coefficient of an inertia translate is the decomposition-group translate of
the original integral coefficient. -/
theorem criticalGeometricSheetToSchurFibre_rawCoeff_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) (i : Fin m) :
    (criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.1.coeff i =
      (g : criticalSchurDecompositionGroup K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) •
        (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i := by
  apply Subtype.ext
  let D := criticalSchurDecompositionGroup K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  have hleft := criticalGeometricSheetToSchurFibre_rawCoeff_coe K hm hn
    (criticalSchurInertiaAction K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ) i
  have haction := criticalSchurInertiaAction_rawCoeff K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ i
  have hright := criticalGeometricSheetToSchurFibre_rawCoeff_coe K hm hn σ i
  have hmap := congrArg (fun z : criticalNormalClosure K m n => (g : D) • z) hright.symm
  have hcoe := SubMulAction.val_smul
    (p := (criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).subMulAction
        (criticalObservationField K m n)) (g : D)
    ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i)
  exact hleft.trans (haction.trans (hmap.trans hcoe.symm))

/-- The integral reciprocal coefficient of an inertia translate is the decomposition-group
translate of the original integral coefficient. -/
theorem criticalGeometricSheetToSchurFibre_recipCoeff_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) (j : Fin n) :
    (criticalGeometricSheetToSchurFibre K hm hn
        (criticalSchurInertiaAction K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.2.coeff j =
      (g : criticalSchurDecompositionGroup K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) •
        (criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j := by
  apply Subtype.ext
  let D := criticalSchurDecompositionGroup K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  have hleft := criticalGeometricSheetToSchurFibre_recipCoeff_coe K hm hn
    (criticalSchurInertiaAction K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ) j
  have haction := criticalSchurInertiaAction_recipCoeff K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ j
  have hright := criticalGeometricSheetToSchurFibre_recipCoeff_coe K hm hn σ j
  have hmap := congrArg (fun z : criticalNormalClosure K m n => (g : D) • z) hright.symm
  have hcoe := SubMulAction.val_smul
    (p := (criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).subMulAction
        (criticalObservationField K m n)) (g : D)
    ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j)
  exact hleft.trans (haction.trans (hmap.trans hcoe.symm))

/-- Inertia fixes the residue of every raw low coefficient of every actual sheet. -/
theorem criticalGeometricSheetToSchurFibre_rawCoeff_residue_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) (i : Fin m) :
    IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((criticalGeometricSheetToSchurFibre K hm hn
          (criticalSchurInertiaAction K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.1.coeff i) =
      IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i) := by
  calc
    _ = IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((g : criticalSchurDecompositionGroup K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) •
          (criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i) :=
      congrArg (IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
        (criticalGeometricSheetToSchurFibre_rawCoeff_inertia K hm hn g σ i)
    _ = _ := criticalSchurInertia_residue_smul K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g _

/-- Inertia fixes the residue of every reciprocal low coefficient of every actual sheet. -/
theorem criticalGeometricSheetToSchurFibre_recipCoeff_residue_inertia
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (g : criticalSchurInertiaGroup K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (σ : criticalGeometricSheet K m n) (j : Fin n) :
    IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((criticalGeometricSheetToSchurFibre K hm hn
          (criticalSchurInertiaAction K
            (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ)).1.2.coeff j) =
      IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j) := by
  calc
    _ = IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        ((g : criticalSchurDecompositionGroup K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) •
          (criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j) :=
      congrArg (IsLocalRing.residue
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
        (criticalGeometricSheetToSchurFibre_recipCoeff_inertia K hm hn g σ j)
    _ = _ := criticalSchurInertia_residue_smul K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g _

end

end GaloisForLFunctions.HTGeometry
