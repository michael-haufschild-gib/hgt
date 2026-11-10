import GaloisForLFunctions.HyperbolicArakelovTheory.TheGeometricScatteringTowerDetectsTheWeilFormDomain
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadGammaAutocorrelationEnergy
import GaloisForLFunctions.RHTower.FourierL2SobolevDomain
import GaloisForLFunctions.ArithmeticIncidencePositivity.CubicGaugeSurplusPotential
import GaloisForLFunctions.HTGeometry.CharacteristicEquilibriumDefect
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The second height jet of the geometric scattering tower

The omitted positive jump tail concentrates at the origin as the scattering height grows.
The quadratic height scaling probes the physical Fourier Dirichlet energy, while the exact
Robin mass term and the finite arithmetic contacts retain their separate normalizations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology Complex
open scoped ENNReal InnerProductSpace BigOperators
namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
open _root_.RHTower

/-- The extended omitted jump energy at a positive integer scattering height. -/
def scatteringSecondHeightEnergy (N : ℕ) (f : SoninL2) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
    (((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) + 1) * t) *
      archLevyDensity t * ccmActualHeadTranslationDefect t f)

/-- Physical Dirichlet energy in the unitary Fourier normalization, retaining infinity. -/
def scatteringDirichletEnergy (f : SoninL2) : ℝ≥0∞ :=
  ∫⁻ ξ : ℝ, ENNReal.ofReal ((2 * Real.pi * ξ) ^ 2 * ‖fourierUnitary f ξ‖ ^ 2)

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
