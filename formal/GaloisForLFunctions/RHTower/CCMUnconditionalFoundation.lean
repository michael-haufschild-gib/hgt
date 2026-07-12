/-
# Unconditional CCM route foundation

This module gathers the three unconditional mechanisms used by the current
Connes--Consani--Moscovici route:

* finite diagonal-Fock defect/passivity and source incidence;
* bilateral polarization of an off-line quartet resolvent;
* exact Sonin resolvent dressing of the boundary commutator.
* an explicit rectangular two-edge Xi test family, including its exact
  transform decomposition and unconditional divisor square-summability.

The source incidence includes the complete complex right-half-plane polar--prime critical Mellin
colligation, not only its positive-real-ray restriction.

It also states the cofinal finite-section law and imports the exact global
Xi--Weil/source identities already present in the non-q62 formal corpus.  The
global RH-bearing input is named `CCMGlobalWeilPassivity` and proved equivalent
to RH.  At finite level it is represented by source-resolved passivity at every
section.  Nothing in this file asserts either passivity condition for the
distinguished semilocal Sonin source construction.
-/
import GaloisForLFunctions.RHTower.CCMFiniteFockPassivity
import GaloisForLFunctions.RHTower.CCMQuartetResolventPolarization
import GaloisForLFunctions.RHTower.CCMSoninResolventCommutator
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.HTGeometry.PrimeLogCauchySeamRank
import GaloisForLFunctions.RHTower.GammaDampedPrimeLogCauchyDomain
import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect
import GaloisForLFunctions.RHTower.CCMComplexMellinColligation
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt
import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion
import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion
import GaloisForLFunctions.RHTower.CCMCompletedPrimeGammaAccretivityCriterion
import GaloisForLFunctions.RHTower.PrimeArchSourceUpperBoundGate
import GaloisForLFunctions.RHTower.SoninLogCoordinateScattering
import GaloisForLFunctions.RHTower.HermitianDeterminantRH
import GaloisForLFunctions.RHTower.PrimeEnergyZeroTransfer
import GaloisForLFunctions.RHTower.RadialPSWFInteractionPicture

namespace RHTower

noncomputable section

/-- The exact global RH-bearing passivity condition on the multiplicity-exact
Xi divisor. -/
def CCMGlobalWeilPassivity : Prop :=
  ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
    0 ≤ (xiWeilPolarization F F).re

/-- The global CCM/Weil passivity condition is exactly RH.  A successful
semilocal construction must therefore transport its source positivity to this
complete divisor domain. -/
theorem ccmGlobalWeilPassivity_iff_riemannHypothesis :
    CCMGlobalWeilPassivity ↔ RiemannHypothesis := by
  rw [CCMGlobalWeilPassivity, riemannHypothesis_iff_xiWeilPolarization_nonneg]

/-- Positivity on the moving regular two-pole Cauchy carrier.  Normalized pole
exhaustion proves that this much smaller condition already contains every
off-line conjugate-fiber negative direction. -/
def CCMRegularTwoPolePassivity : Prop :=
  XiWeilRegularTwoCauchyNonneg

/-- Exact rank-two CCM criterion: regular two-pole Cauchy passivity is RH. -/
theorem ccmRegularTwoPolePassivity_iff_riemannHypothesis :
    CCMRegularTwoPolePassivity ↔ RiemannHypothesis := by
  rw [CCMRegularTwoPolePassivity,
    ← riemannHypothesis_iff_regularTwoCauchy_nonneg]

/-- The explicit continued prime--archimedean rank-two source condition is
already RH-equivalent.  The construction problem is to prove this positivity
from the distinguished semilocal Sonin model. -/
theorem ccmContinuedTwoPoleSourcePassivity_iff_riemannHypothesis :
    CCMContinuedTwoPoleSourcePassivity ↔ RiemannHypothesis := by
  rw [← riemannHypothesis_iff_ccmContinuedTwoPoleSourcePassivity]

/-- Cofinal source-resolved passivity for a family of finite CCM sections. -/
def CCMCofinalSourceResolvedPassivity
    (A E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ n, CCMSourceResolvedPassivity (A n) (E n) (B n) (M n)

/-- Cofinal contractivity of the finite diagonal-Fock lifts. -/
def CCMCofinalFiniteFockPassivity
    (A C : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ n, CCMFiniteFockPassivity (A n) (C n)

/-- Exact cofinal algebraic reduction from source incidence to diagonal-Fock
contractivity. -/
theorem ccmCofinalFiniteFockPassivity_iff_sourceResolved
    (A C E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ n, C n = E n - B n + M n) :
    CCMCofinalFiniteFockPassivity A C ↔
      CCMCofinalSourceResolvedPassivity A E B M := by
  unfold CCMCofinalFiniteFockPassivity CCMCofinalSourceResolvedPassivity
  apply forall_congr'
  intro n
  exact ccmFiniteFockPassivity_iff_sourceResolved
    (A n) (C n) (E n) (B n) (M n) (hC n)

/-- Exact cofinal defect law.  Under the incidence identity, positivity of every
finite diagonal-Fock defect is equivalent to the one remaining cofinal
source-resolved passivity assertion. -/
theorem ccmCofinalDefect_kreinNonneg_iff_sourceResolved
    (A C E B M : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℂ)
    (hC : ∀ n, C n = E n - B n + M n) :
    (∀ n, KreinNonneg (ccmDiagonalDefectGram (A n) (C n))) ↔
      CCMCofinalSourceResolvedPassivity A E B M := by
  unfold CCMCofinalSourceResolvedPassivity
  apply forall_congr'
  intro n
  exact ccmDiagonalDefect_kreinNonneg_iff_sourceResolved
    (A n) (C n) (E n) (B n) (M n) (hC n)

end

end RHTower
