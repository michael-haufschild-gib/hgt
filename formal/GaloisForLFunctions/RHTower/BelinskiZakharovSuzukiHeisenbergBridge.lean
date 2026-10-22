import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteMatrixHeisenberg
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Belinski--Zakharov residue as the finite Suzuki Heisenberg shift

The unit BZ nilpotent residue and the Suzuki two-level shift differ only by their finite index
types.  This module makes that reindexing explicit, identifies the BZ one-pole dressing with the
corresponding Suzuki shear, and applies the existing finite Heisenberg flow to the BZ generator.

This is a finite algebraic model of a nilpotent BZ residue.  It is not a spectral-parameter
inverse-scattering construction and carries no Riemann-hypothesis consequence.
-/

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

noncomputable section

namespace RHTower

/-- The index reordering from the BZ `Fin 2` convention to the Suzuki `Bool` convention. -/
def belinskiZakharovFinTwoBoolEquiv : Fin 2 ≃ Bool where
  toFun i := if i = 0 then false else true
  invFun b := if b then 1 else 0
  left_inv i := by
    fin_cases i <;> simp
  right_inv b := by
    cases b <;> rfl

/-- The unit BZ nilpotent residue reindexes to the two-level Suzuki shift. -/
theorem reindex_belinskiZakharovNilpotentResidue_unit_eq_nilpotentShift2 :
    Matrix.reindex belinskiZakharovFinTwoBoolEquiv belinskiZakharovFinTwoBoolEquiv
        (GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1) =
      nilpotentShift2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, belinskiZakharovFinTwoBoolEquiv,
      GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue, nilpotentShift2]

/-- The BZ position projector reindexes to the existing Suzuki position projector. -/
def belinskiZakharovPositionProjection : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, 1]

theorem reindex_belinskiZakharovPositionProjection_eq_positionProjection2 :
    Matrix.reindex belinskiZakharovFinTwoBoolEquiv belinskiZakharovFinTwoBoolEquiv
        belinskiZakharovPositionProjection = positionProjection2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, belinskiZakharovFinTwoBoolEquiv,
      belinskiZakharovPositionProjection, positionProjection2]

/-- Under the same reindexing, a unit-residue BZ one-pole dressing is the Suzuki shear. -/
theorem reindex_belinskiZakharovOnePoleDressing_unit_eq_suzukiShear
    (spectral pole : ℝ) :
    Matrix.reindex belinskiZakharovFinTwoBoolEquiv belinskiZakharovFinTwoBoolEquiv
        (GaloisForLFunctions.HTGeometry.belinskiZakharovOnePoleDressing spectral pole 1) =
      1 + (1 / (spectral - pole)) • nilpotentShift2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex_apply, belinskiZakharovFinTwoBoolEquiv,
      GaloisForLFunctions.HTGeometry.belinskiZakharovOnePoleDressing,
      GaloisForLFunctions.HTGeometry.belinskiZakharovUnipotentDressing, nilpotentShift2]

/-- The unit BZ residue has the same exact position commutator as the finite Suzuki shift. -/
theorem belinskiZakharovNilpotentResidue_unit_positionProjection_commutator :
    GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1 *
        belinskiZakharovPositionProjection -
      belinskiZakharovPositionProjection *
        GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1 =
      GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue,
      belinskiZakharovPositionProjection]

/-- The BZ unit residue generates the exact affine Heisenberg position flow. -/
theorem belinskiZakharovNilpotentResidue_unit_position_heisenbergFlow (t : ℝ) :
    exp (t • GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1) *
        belinskiZakharovPositionProjection *
        exp ((-t) • GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1) =
      belinskiZakharovPositionProjection +
        t • GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1 :=
  conj_position_eq
    (GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1)
    belinskiZakharovPositionProjection
    (GaloisForLFunctions.HTGeometry.belinskiZakharovNilpotentResidue 1)
    belinskiZakharovNilpotentResidue_unit_positionProjection_commutator
    (Commute.refl _) t

end RHTower
