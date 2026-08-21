import GaloisForLFunctions.HTGeometry.LeeYangTwoSpinCircle
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Lee--Yang circle shadow of a finite Seiberg--Witten curve

The Lee--Yang two-spin model and the finite Seiberg--Witten skeleton both use the same complex
unit circle.  This module regards that circle as a gauge-orbit curve through a fixed two-spinor.
Its finite Seiberg--Witten curvature invariant is constant.  The closed marginal Lee--Yang zero
at diagonal fugacity `-1` supplies a distinguished point on this orbit.

This is a shared-circle algebraic construction, not a claim that a Lee--Yang zero locus is a
Seiberg--Witten moduli curve.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Base spinor for the shared Lee--Yang-circle gauge orbit. -/
def leeYangCircleSeibergWittenBase : SeibergWittenSpinor :=
  ![(1 : ℂ), 1]

/-- The finite Seiberg--Witten configuration curve parameterized by the complex unit circle. -/
def leeYangCircleSeibergWittenCurve (u : Circle) : SeibergWittenSpinor :=
  u • leeYangCircleSeibergWittenBase

/-- The shared-circle curve is exactly the finite Seiberg--Witten gauge orbit curve. -/
theorem leeYangCircleSeibergWittenCurve_eq_orbit (u : Circle) :
    leeYangCircleSeibergWittenCurve u =
      seibergWittenGaugeOrbitCurve leeYangCircleSeibergWittenBase u := rfl

/-- The finite Seiberg--Witten curvature invariant is constant on the Lee--Yang-circle curve. -/
theorem leeYangCircleSeibergWittenCurve_invariant (u : Circle) :
    seibergWittenInvariant (leeYangCircleSeibergWittenCurve u) =
      seibergWittenInvariant leeYangCircleSeibergWittenBase := by
  exact seibergWittenInvariant_gaugeInvariant u leeYangCircleSeibergWittenBase

/-- The diagonal Lee--Yang polynomial has the closed marginal zero at the circle point `-1`. -/
theorem leeYangMarginal_zero :
    GaloisForLFunctions.leeYangTwoSpin 1 (-1) (-1) = 0 := by
  rw [GaloisForLFunctions.leeYangTwoSpin_marginal_pos]
  ring

/-- The Lee--Yang marginal zero corresponds to a gauge-orbit point with the base curvature record. -/
theorem leeYangMarginalSeibergWittenCurve_invariant :
    seibergWittenInvariant (leeYangCircleSeibergWittenCurve (-1 : Circle)) =
      seibergWittenInvariant leeYangCircleSeibergWittenBase :=
  leeYangCircleSeibergWittenCurve_invariant (-1 : Circle)

end GaloisForLFunctions.HTGeometry
