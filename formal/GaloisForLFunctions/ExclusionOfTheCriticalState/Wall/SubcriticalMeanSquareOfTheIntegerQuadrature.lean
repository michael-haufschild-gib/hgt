import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IntegerQuadratureAsAFractionalPartConvolution

/-!
# Subcritical exponential tilts of the integer quadrature error
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Integer wave minus its continuous density, on the real Mellin line of tilt β. -/
def tiltedIntegerError (Φ : ℝ → ℝ) (β t : ℝ) : ℝ :=
  Real.exp (β*t)*(integerReferenceWave Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*Φ u))

end GaloisForLFunctions.ExclusionOfTheCriticalState
