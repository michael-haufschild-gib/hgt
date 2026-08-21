import GaloisForLFunctions.HTGeometry.ColorGramMinkowskiCone
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Seiberg--Witten curvature as a colour Gram record

The finite Seiberg--Witten curvature `q(ψ) = ψψ†` is exactly the Gram matrix of a one-colour
event whose row is the conjugate spinor.  The conjugation is forced by the convention
`Xᴴ X` for a colour Gram matrix.  Consequently every finite Seiberg--Witten curvature lies on the
future-null boundary of the colour Gram cone, and its entire `U(1)` gauge orbit has the same public
Gram record.

This is a finite Hermitian-record correspondence.  It does not identify colour with a gauge group
of a smooth Seiberg--Witten four-manifold.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- One-colour event representing a finite Seiberg--Witten spinor curvature. -/
def seibergWittenColorEvent (psi : SeibergWittenSpinor) : ColorEventMatrix :=
  singleColorEvent (star psi)

/-- The Seiberg--Witten quadratic curvature is exactly this one-colour Gram record. -/
theorem seibergWittenQuadraticMap_eq_colorGram (psi : SeibergWittenSpinor) :
    seibergWittenQuadraticMap psi = colorGramMatrix (seibergWittenColorEvent psi) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seibergWittenQuadraticMap, higgsSpinorEventMatrix, seibergWittenColorEvent,
      colorGramMatrix, singleColorEvent, Matrix.mul_apply, Matrix.vecMulVec_apply]

/-- The colour-event lift of a finite Seiberg--Witten gauge orbit. -/
def seibergWittenColorEventCurve (psi : SeibergWittenSpinor) :
    Circle → ColorEventMatrix :=
  fun u => seibergWittenColorEvent (u • psi)

/-- The Gram curvature at every point of the lifted orbit solves the finite equation. -/
theorem seibergWittenColorEventCurve_solvesEquation
    (psi : SeibergWittenSpinor) (u : Circle) :
    seibergWittenEquation (colorGramMatrix (seibergWittenColorEventCurve psi u))
      (seibergWittenGaugeOrbitCurve psi u) := by
  change colorGramMatrix (seibergWittenColorEvent (u • psi)) =
    seibergWittenQuadraticMap (u • psi)
  exact (seibergWittenQuadraticMap_eq_colorGram _).symm

/-- The colour Gram record is constant along every lifted `U(1)` orbit. -/
theorem seibergWittenColorEventCurve_gramInvariant
    (psi : SeibergWittenSpinor) (u : Circle) :
    colorGramMatrix (seibergWittenColorEventCurve psi u) =
      colorGramMatrix (seibergWittenColorEventCurve psi 1) := by
  calc
    colorGramMatrix (seibergWittenColorEventCurve psi u) =
        seibergWittenQuadraticMap (u • psi) :=
      (seibergWittenQuadraticMap_eq_colorGram _).symm
    _ = seibergWittenQuadraticMap psi :=
      seibergWittenQuadraticMap_gaugeInvariant u psi
    _ = colorGramMatrix (seibergWittenColorEventCurve psi 1) := by
      rw [show seibergWittenColorEventCurve psi 1 = seibergWittenColorEvent psi by
        simp [seibergWittenColorEventCurve]]
      exact seibergWittenQuadraticMap_eq_colorGram psi

/-- Every finite Seiberg--Witten curvature is a future-null one-colour Gram record. -/
theorem seibergWittenColorEvent_lorentz_null (psi : SeibergWittenSpinor) :
    colorGramLorentzMassSq (seibergWittenColorEvent psi) = 0 :=
  singleColorEvent_lorentz_null (star psi)

end GaloisForLFunctions.HTGeometry
