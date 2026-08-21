import GaloisForLFunctions.HTGeometry.SeibergWitten.Hodge
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Traceless self-dual curvature from the finite Seiberg--Witten spinor

The three traceless real coordinates of the Hermitian outer square `q(ψ)` define a point in the
flat self-dual three-plane of `Λ²ℝ⁴`.  This is the finite-coordinate analogue of retaining the
self-dual, trace-free component of the Seiberg--Witten quadratic curvature map.  It is fixed by
the flat Hodge star and invariant under the common `U(1)` phase action.

This file does not identify the finite outer square with the curvature of a continuum connection.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Self-dual two-form formed from the traceless Pauli coordinates of `q(ψ)`. -/
def seibergWittenSelfDualCurvature (psi : SeibergWittenSpinor) :
    SeibergWitten.FlatFourTwoForms :=
  SeibergWitten.flatSelfDualTwoForm
    (higgsSpinorX psi) (higgsSpinorY psi) (higgsSpinorZ psi)

/-- The finite trace-free curvature belongs to the flat self-dual three-plane. -/
theorem seibergWittenSelfDualCurvature_isSelfDual (psi : SeibergWittenSpinor) :
    SeibergWitten.flatFourHodgeStar.isSelfDual (seibergWittenSelfDualCurvature psi) :=
  SeibergWitten.flatSelfDualTwoForm_isSelfDual _ _ _

/-- First traceless Hermitian coordinate is invariant under the finite gauge action. -/
theorem higgsSpinorX_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    higgsSpinorX (u • psi) = higgsSpinorX psi := by
  have h := congrArg (fun M : SeibergWittenCurvature => (M 0 1).re)
    (seibergWittenQuadraticMap_gaugeInvariant u psi)
  simpa [seibergWittenQuadraticMap, higgsSpinorEventMatrix, higgsSpinorX,
    Matrix.vecMulVec_apply] using h

/-- Second traceless Hermitian coordinate is invariant under the finite gauge action. -/
theorem higgsSpinorY_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    higgsSpinorY (u • psi) = higgsSpinorY psi := by
  have h := congrArg (fun M : SeibergWittenCurvature => (M 0 1).im)
    (seibergWittenQuadraticMap_gaugeInvariant u psi)
  simpa [seibergWittenQuadraticMap, higgsSpinorEventMatrix, higgsSpinorY,
    Matrix.vecMulVec_apply] using h

/-- Third traceless Hermitian coordinate is invariant under the finite gauge action. -/
theorem higgsSpinorZ_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    higgsSpinorZ (u • psi) = higgsSpinorZ psi := by
  have h := congrArg (fun M : SeibergWittenCurvature =>
      ((M 0 0).re - (M 1 1).re) / 2)
    (seibergWittenQuadraticMap_gaugeInvariant u psi)
  simpa [seibergWittenQuadraticMap, higgsSpinorEventMatrix, higgsSpinorZ,
    Matrix.vecMulVec_apply, Complex.normSq_apply] using h

/-- The finite self-dual curvature is constant along every common-phase gauge orbit. -/
theorem seibergWittenSelfDualCurvature_gaugeInvariant
    (u : Circle) (psi : SeibergWittenSpinor) :
    seibergWittenSelfDualCurvature (u • psi) = seibergWittenSelfDualCurvature psi := by
  unfold seibergWittenSelfDualCurvature
  rw [higgsSpinorX_gaugeInvariant, higgsSpinorY_gaugeInvariant, higgsSpinorZ_gaugeInvariant]

/-- The north finite spinor vacuum has nonzero self-dual trace-free curvature. -/
theorem seibergWittenVacuum_selfDualCurvature_ne_zero :
    seibergWittenSelfDualCurvature abelianHiggsSpinorVacuum ≠ 0 := by
  intro h
  have h2 := congrFun h 2
  simp [seibergWittenSelfDualCurvature, SeibergWitten.flatSelfDualTwoForm,
    abelianHiggsSpinorVacuum, higgsSpinorX, higgsSpinorY, higgsSpinorZ, Complex.normSq] at h2

end GaloisForLFunctions.HTGeometry
