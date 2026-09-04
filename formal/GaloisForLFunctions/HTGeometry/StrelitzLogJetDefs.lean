import Mathlib.Analysis.Complex.RealDeriv

/-!
# Strelitz logarithmic-jet coordinates

Lightweight definitions of the first and second Euler logarithmic jets.  Keeping these coordinates
independent of the order-two differential-algebra compiler prevents elementary maximum-modulus
modules from importing the full entire-heat/Newton chain.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Euler logarithmic derivative `z f'(z) / f(z)`. -/
def eulerLogDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z / f z

/-- Euler derivative of the Euler logarithmic derivative. -/
def eulerLogDerivSecond (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv (eulerLogDeriv f) z

end

end GaloisForLFunctions.HTGeometry
