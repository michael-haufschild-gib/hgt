import GaloisForLFunctions.HTGeometry.Critical.Schur.InertiaAction
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.SheetLift

/-!
# Schur inertia preserves the actual reduced sheet label

The chosen decomposition group acts on the upper valuation ring and its residue field.  By
definition, the inertia subgroup is the kernel of the residue-field action.  Consequently every
inertia element fixes the reduction of every integral coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

/-- An actual Schur inertia element fixes the residue of every upper integral element. -/
theorem criticalSchurInertia_residue_smul
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (g : criticalSchurInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)
        ((g : criticalSchurDecompositionGroup K hm hn) • a) =
      IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn) a := by
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let D := criticalSchurDecompositionGroup K hm hn
  have hg : MulSemiringAction.toRingAut D (IsLocalRing.ResidueField A)
      (g : D) = 1 := by
    exact g.property
  rw [IsLocalRing.ResidueField.residue_smul]
  have happly := DFunLike.congr_fun hg (IsLocalRing.residue A a)
  simpa [D] using happly

/-- Mapping the integral Schur lift back to the normal closure identifies each raw low
coefficient with the corresponding actual sheet coefficient. -/
theorem criticalGeometricSheetToSchurFibre_rawCoeff_coe
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (i : Fin m) :
    (criticalNormalClosureSchurValuationSubring K (by omega) (by omega)).subtype
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i) =
      ((criticalSourceRawLow K m n).map σ.toRingHom).coeff i := by
  have h := congrArg (fun p => p.1.1.coeff (i : ℕ))
    (criticalFibreMap_criticalGeometricSheetToSchurFibre K hm hn σ)
  have hmap :
    (criticalNormalClosureSchurValuationSubring K (by omega) (by omega)).subtype
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.1.coeff i) =
      (criticalGeometricSheetToNormalFibre K m n σ).1.1.coeff i := by
    simpa only [criticalFibreMap, Polynomial.coeff_map,
      criticalGeometricSheetToSchurFieldFibre] using h
  exact hmap.trans (by rfl)

/-- Mapping the integral Schur lift back to the normal closure identifies each reciprocal low
coefficient with the corresponding actual sheet coefficient. -/
theorem criticalGeometricSheetToSchurFibre_recipCoeff_coe
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (σ : criticalGeometricSheet K m n) (j : Fin n) :
    (criticalNormalClosureSchurValuationSubring K (by omega) (by omega)).subtype
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j) =
      ((criticalSourceReciprocalLow K m n).map σ.toRingHom).coeff j := by
  have h := congrArg (fun p => p.1.2.coeff (j : ℕ))
    (criticalFibreMap_criticalGeometricSheetToSchurFibre K hm hn σ)
  have hmap :
    (criticalNormalClosureSchurValuationSubring K (by omega) (by omega)).subtype
        ((criticalGeometricSheetToSchurFibre K hm hn σ).1.2.coeff j) =
      (criticalGeometricSheetToNormalFibre K m n σ).1.2.coeff j := by
    simpa only [criticalFibreMap, Polynomial.coeff_map,
      criticalGeometricSheetToSchurFieldFibre] using h
  exact hmap.trans (by rfl)

/-- On a raw low coefficient, the concrete inertia sheet action is the underlying normal-closure
automorphism. -/
theorem criticalSchurInertiaAction_rawCoeff
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (g : criticalSchurInertiaGroup K hm hn)
    (σ : criticalGeometricSheet K m n) (i : Fin m) :
    ((criticalSourceRawLow K m n).map
      (criticalSchurInertiaAction K hm hn g σ).toRingHom).coeff i =
      (g : criticalSchurDecompositionGroup K hm hn) •
        ((criticalSourceRawLow K m n).map σ.toRingHom).coeff i := by
  have hinertia : criticalSchurInertiaAction K hm hn g σ =
      criticalSchurDecompositionAction K hm hn
        (g : criticalSchurDecompositionGroup K hm hn) σ := rfl
  have hdecomposition : criticalSchurDecompositionAction K hm hn
      (g : criticalSchurDecompositionGroup K hm hn) σ =
      criticalNormalClosureAction K m n
        (g : criticalSchurDecompositionGroup K hm hn).1 σ := rfl
  have hnormal : criticalNormalClosureAction K m n
      (g : criticalSchurDecompositionGroup K hm hn).1 σ
        ((criticalSourceRawLow K m n).coeff i) =
      (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceRawLow K m n).coeff i)) := rfl
  have heval := congrArg
    (fun f : criticalGeometricSheet K m n =>
      f ((criticalSourceRawLow K m n).coeff i))
    (hinertia.trans hdecomposition)
  calc
    ((criticalSourceRawLow K m n).map
        (criticalSchurInertiaAction K hm hn g σ).toRingHom).coeff i =
        criticalSchurInertiaAction K hm hn g σ
          ((criticalSourceRawLow K m n).coeff i) :=
      Polynomial.coeff_map
        (criticalSchurInertiaAction K hm hn g σ).toRingHom (i : ℕ)
    _ = criticalNormalClosureAction K m n
        (g : criticalSchurDecompositionGroup K hm hn).1 σ
          ((criticalSourceRawLow K m n).coeff i) := heval
    _ = (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceRawLow K m n).coeff i)) := hnormal
    _ = (g : criticalSchurDecompositionGroup K hm hn) •
        σ ((criticalSourceRawLow K m n).coeff i) := by
      exact (AlgEquiv.smul_def
        (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceRawLow K m n).coeff i))).symm |>.trans
          (MulAction.subgroup_smul_def
            (g : criticalSchurDecompositionGroup K hm hn)
            (σ ((criticalSourceRawLow K m n).coeff i))).symm
    _ = (g : criticalSchurDecompositionGroup K hm hn) •
        ((criticalSourceRawLow K m n).map σ.toRingHom).coeff i := by
      exact congrArg (fun z =>
        (g : criticalSchurDecompositionGroup K hm hn) • z)
        (Polynomial.coeff_map σ.toRingHom (i : ℕ)).symm

/-- On a reciprocal low coefficient, the concrete inertia sheet action is the underlying
normal-closure automorphism. -/
theorem criticalSchurInertiaAction_recipCoeff
    (K : Type*) [Field K] [CharZero K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (g : criticalSchurInertiaGroup K hm hn)
    (σ : criticalGeometricSheet K m n) (j : Fin n) :
    ((criticalSourceReciprocalLow K m n).map
      (criticalSchurInertiaAction K hm hn g σ).toRingHom).coeff j =
      (g : criticalSchurDecompositionGroup K hm hn) •
        ((criticalSourceReciprocalLow K m n).map σ.toRingHom).coeff j := by
  have hinertia : criticalSchurInertiaAction K hm hn g σ =
      criticalSchurDecompositionAction K hm hn
        (g : criticalSchurDecompositionGroup K hm hn) σ := rfl
  have hdecomposition : criticalSchurDecompositionAction K hm hn
      (g : criticalSchurDecompositionGroup K hm hn) σ =
      criticalNormalClosureAction K m n
        (g : criticalSchurDecompositionGroup K hm hn).1 σ := rfl
  have hnormal : criticalNormalClosureAction K m n
      (g : criticalSchurDecompositionGroup K hm hn).1 σ
        ((criticalSourceReciprocalLow K m n).coeff j) =
      (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceReciprocalLow K m n).coeff j)) := rfl
  have heval := congrArg
    (fun f : criticalGeometricSheet K m n =>
      f ((criticalSourceReciprocalLow K m n).coeff j))
    (hinertia.trans hdecomposition)
  calc
    ((criticalSourceReciprocalLow K m n).map
        (criticalSchurInertiaAction K hm hn g σ).toRingHom).coeff j =
        criticalSchurInertiaAction K hm hn g σ
          ((criticalSourceReciprocalLow K m n).coeff j) :=
      Polynomial.coeff_map
        (criticalSchurInertiaAction K hm hn g σ).toRingHom (j : ℕ)
    _ = criticalNormalClosureAction K m n
        (g : criticalSchurDecompositionGroup K hm hn).1 σ
          ((criticalSourceReciprocalLow K m n).coeff j) := heval
    _ = (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceReciprocalLow K m n).coeff j)) := hnormal
    _ = (g : criticalSchurDecompositionGroup K hm hn) •
        σ ((criticalSourceReciprocalLow K m n).coeff j) := by
      exact (AlgEquiv.smul_def
        (g : criticalSchurDecompositionGroup K hm hn).1
        (σ ((criticalSourceReciprocalLow K m n).coeff j))).symm |>.trans
          (MulAction.subgroup_smul_def
            (g : criticalSchurDecompositionGroup K hm hn)
            (σ ((criticalSourceReciprocalLow K m n).coeff j))).symm
    _ = (g : criticalSchurDecompositionGroup K hm hn) •
        ((criticalSourceReciprocalLow K m n).map σ.toRingHom).coeff j := by
      exact congrArg (fun z =>
        (g : criticalSchurDecompositionGroup K hm hn) • z)
        (Polynomial.coeff_map σ.toRingHom (j : ℕ)).symm

end

end GaloisForLFunctions.HTGeometry
