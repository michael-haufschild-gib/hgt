import GaloisForLFunctions.HTGeometry.HalfLogCesaroAverage
import GaloisForLFunctions.HTGeometry.GammaTransportKernel

/-!
# The equation bounds the half-log trace

The logarithmic normal equation says the Dirichlet operator plus the transport operator equals the
source.  A bound on the source together with a bound on the transport term therefore bounds the
Dirichlet operator, and dividing by `2√L` converts that into a bound on the half-log trace offset
by the averaged trace.

This is where the equation is actually used: everything else in the chain is an estimate about one
of the two operators separately.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The equation bounds the trace from above.**  A source bounded by `T` and a transport term
bounded below by `−B` give `√X f(X) ≤ (T+B)/(2√X) + A(X)`. -/
theorem halfLog_le_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : S ≤ T)
    (hB : -B ≤ gammaTransport f X) :
    Real.sqrt X * f X ≤ (T + B) / (2 * Real.sqrt X) + halfLogAverage f X := by
  refine halfLog_le_of_logDirichlet_le hX ?_
  linarith [heq, hS, hB]

/-- **The equation bounds the trace from below.**  The mirror, with the transport term bounded
above. -/
theorem le_halfLog_of_equation {f : ℝ → ℝ} {X S T B : ℝ} (hX : 0 < X)
    (heq : logDirichlet f X + gammaTransport f X = S) (hS : T ≤ S)
    (hB : gammaTransport f X ≤ B) :
    (T - B) / (2 * Real.sqrt X) + halfLogAverage f X ≤ Real.sqrt X * f X := by
  refine le_halfLog_of_le_logDirichlet hX ?_
  linarith [heq, hS, hB]

end GaloisForLFunctions.HTGeometry
