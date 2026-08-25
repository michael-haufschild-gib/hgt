import GaloisForLFunctions.HTGeometry.SourceMarkedInterfinityBridge
import GaloisForLFunctions.RHTower.RouteRSourceMarkedFiniteCompletion

/-!
# Xi completion defects as Interfinity stable classes

The source-marked completion state of Route R has a canonical stable-cohomology class: the literal
Fisher source relation modulo source relations that remain exact after physical completion.  This
class vanishes at a Xi divisor exactly on the critical line.  Hence RH is global vanishing of these
source-provenance stable classes.

This does not supply the arithmetic law forcing vanishing.  It proves that stable-primitive
Interfinity geometry is an exact home for the already source-derived completion defect, rather than
a numerical relabelling of its width.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- Stable source-relation class carried by one physical Xi completion state. -/
def routeRPrimeGammaXiPhysicalStableClass (rho : XiDivisorSupport) :=
  SourceMarkedExFlag.sourceStableClass
    (routeRPrimeGammaPhysicalMarkedState (2 * (rho : ℂ).re - 1))
    routeRPrimeGammaMarkedFisherBoundary

/-- The physical Interfinity class dies exactly on the critical line. -/
theorem routeRPrimeGammaXiPhysicalStableClass_eq_zero_iff_re_eq_half
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiPhysicalStableClass rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeGammaXiPhysicalStableClass,
    SourceMarkedExFlag.sourceStableClass_eq_zero_iff]
  change routeRPrimeGammaFixedGradeTailLanding (2 * (rho : ℂ).re - 1)
      routeRPrimeGammaFisherSourceBoundary ∈ routeRTailRoosBoundary ↔ _
  rw [← boundaryEscapeClass_eq_zero_iff]
  exact routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho

/-- An off-line Xi divisor is exactly a surviving source-provenance stable class. -/
theorem routeRPrimeGammaXiPhysicalStableClass_ne_zero_iff_re_ne_half
    (rho : XiDivisorSupport) :
    routeRPrimeGammaXiPhysicalStableClass rho ≠ 0 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  exact not_congr (routeRPrimeGammaXiPhysicalStableClass_eq_zero_iff_re_eq_half rho)

/-- RH is global vanishing of the canonical source-provenance stable classes. -/
theorem all_routeRPrimeGammaXiPhysicalStableClass_eq_zero_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      routeRPrimeGammaXiPhysicalStableClass rho = 0) ↔
      RiemannHypothesis := by
  rw [← routeRPrimeGammaXiGlobalCompletionEscapeFree_iff_riemannHypothesis]
  change (∀ rho : XiDivisorSupport,
      routeRPrimeGammaXiPhysicalStableClass rho = 0) ↔
    ∀ rho : XiDivisorSupport,
      routeRPrimeGammaXiCompletionEscapeClass rho = 0
  constructor
  · intro h rho
    exact (routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiPhysicalStableClass_eq_zero_iff_re_eq_half rho).1 (h rho))
  · intro h rho
    exact (routeRPrimeGammaXiPhysicalStableClass_eq_zero_iff_re_eq_half rho).2
      ((routeRPrimeGammaXiCompletionEscapeClass_eq_zero_iff_re_eq_half rho).1 (h rho))

end

end RHTower
