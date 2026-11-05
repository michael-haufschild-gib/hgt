import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomFourierTail
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Analytic radial profiles of the first theta atom

The complex radial source has a product exponential envelope on a fixed
strip. Cauchy estimates control every derivative under its radial tail.
-/

open Complex Filter Set MeasureTheory
open scoped Topology SchwartzMap FourierTransform
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry _root_.RHTower
noncomputable section

/-- Complex continuation of the first-atom radial tail integrand. -/
def firstAtomRadialKernel (u : ℝ) (z : ℂ) : ℂ :=
  (u ^ (3 / 2 : ℝ) : ℝ) *
    (4 * (u : ℂ) ^ 2 + 9 - 12 * (u : ℂ) * Complex.cosh (2 * z)) *
      Complex.exp (-2 * (u : ℂ) * Complex.cosh (2 * z))

end
end GaloisForLFunctions.CompletedArithmeticForms
