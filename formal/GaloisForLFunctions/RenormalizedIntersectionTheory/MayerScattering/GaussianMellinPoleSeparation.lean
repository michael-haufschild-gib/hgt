import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.GaussianCoreMellinSynthesis
import GaloisForLFunctions.RHTower.XiSignedFactorZeroSeparation
import GaloisForLFunctions.HTGeometry.ConvexDiffCountableConnected
import GaloisForLFunctions.RHTower.WeilLagFunctionCriterion
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!+# Mellin poles of Gaussian resonance-core sums

The continued kernel is written using entire xi and explicit pole factors.
This form distinguishes a removable pole from the raw total Gamma-function value.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory Filter Topology Zeta23
open scoped lp ENNReal ComplexConjugate
open GaloisForLFunctions
open CohomologyOfWindowsOfSpecZ ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticPolarization SpacingScaleHarmonicAnalysis
open RenormalizedIntersectionTheory
open MayerCauchyMellinSymbol MayerScatteringCore MayerCoreMellin MayerEpsteinHeightMeasurability

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- The xi expression for the continued Mellin transform, away from its explicit pole factors. -/
def resonantMellinKernel (s : upperMayerResonances) (u : ℂ) : ℂ :=
  4 * symbol (2 * s.1) u * _root_.RHTower.xi u * _root_.RHTower.xi (2 * s.1 - u) /
    (Gammaℝ (2 * s.1) * u * (u - 1) * (2 * s.1 - u) * (2 * s.1 - u - 1))

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
