import GaloisForLFunctions.RHTower.RouteRSourceMarkedFiniteCompletion
import GaloisForLFunctions.RHTower.RouteRResolutionCoreNoetherCharge

/-!
# Route R completion phantoms and their Noether charge

A Route R completion phantom is not merely a nonzero completed quotient class.  It is a
source-marked history with three simultaneous properties:

* every finite truncation is escape-free on the literal Fisher boundary line;
* every fixed target coordinate eventually agrees exactly with the physical landing;
* the finite states nevertheless fail to converge in source-provenance topology.

Thus the obstruction is invisible to every fixed finite observer but survives globally.  In the
physical Xi fibre, such a phantom exists exactly off the critical line and exactly when the
conserved multiplicity-calibrated Noether orientation charge is nonzero.

No completion principle or RH premise is assumed.  The final equivalence identifies the precise
global phenomenon that an independent no-phantom law would have to exclude.
-/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.BoundaryMigration

namespace RHTower

noncomputable section

/-- The canonical finite Route R tower is a completion phantom at modular grade `t`: every
finite stage is exact and every fixed coordinate stabilizes to the physical landing, but the
source-marked exactness states do not converge to that physical state. -/
def RouteRPrimeGammaCompletionPhantom (t : ℝ) : Prop :=
  (∀ N : ℕ,
    EscapeFree (routeRPrimeGammaFiniteMarkedState N t).landing
      (⊤ : Submodule ℂ routeRPrimeGammaFisherBoundaryLine)
      (routeRPrimeGammaFiniteMarkedState N t).target.boundary) ∧
  (∀ x : routeRPrimeGammaFisherBoundaryLine, ∀ n : ℕ,
    ∀ᶠ N in atTop,
      routeRPrimeGammaFiniteMarkedLanding N t x n =
        routeRPrimeGammaPhysicalMarkedLanding t x n) ∧
  ¬ Tendsto (fun N => routeRPrimeGammaFiniteMarkedState N t) atTop
      (nhds (routeRPrimeGammaPhysicalMarkedState t))

/-- Inside the physical modular strip, the canonical tower is a completion phantom exactly away
from neutral grade.  The finite exactness and coordinate-shadow clauses are unconditional; only
source-provenance convergence detects the grade. -/
theorem routeRPrimeGammaCompletionPhantom_iff
    {t : ℝ} (ht : |t| < 1) :
    RouteRPrimeGammaCompletionPhantom t ↔ t ≠ 0 := by
  constructor
  · intro hphantom ht0
    exact hphantom.2.2
      ((routeRPrimeGammaFiniteMarkedState_tendsto_iff ht).2 ht0)
  · intro ht0
    refine ⟨fun N => routeRPrimeGammaFiniteMarkedState_escapeFree N t, ?_, ?_⟩
    · intro x n
      exact routeRPrimeGammaFiniteMarkedLanding_eventually_eq_coordinate t x n
    · exact (routeRPrimeGammaFiniteMarkedState_tendsto_iff ht).not.mpr ht0

/-- Xi-labelled completion phantom. -/
def RouteRPrimeGammaXiCompletionPhantom (rho : XiDivisorSupport) : Prop :=
  RouteRPrimeGammaCompletionPhantom (2 * (rho : ℂ).re - 1)

/-- One actual Xi support point carries a completion phantom exactly when it is off the critical
line. -/
theorem routeRPrimeGammaXiCompletionPhantom_iff_re_ne_half
    (rho : XiDivisorSupport) :
    RouteRPrimeGammaXiCompletionPhantom rho ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [RouteRPrimeGammaXiCompletionPhantom,
    routeRPrimeGammaCompletionPhantom_iff
      (xiCenteredPrimeIdealRate_abs_lt_one rho)]
  constructor <;> intro h <;> intro hzero
  · apply h
    linarith
  · apply h
    linarith

/-- Completion phantom and conserved Noether charge are the same global defect classification.
The charge does not create the defect; it measures the failure of finite exact histories to descend
through completion. -/
theorem routeRPrimeGammaXiCompletionPhantom_iff_noetherCharge_ne_zero
    (rho : XiDivisorSupport) :
    RouteRPrimeGammaXiCompletionPhantom rho ↔
      routeRPrimeGammaXiNoetherOrientationCharge rho ≠ 0 := by
  rw [routeRPrimeGammaXiCompletionPhantom_iff_re_ne_half]
  constructor
  · intro hoff hcharge
    exact hoff
      ((routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).1
        hcharge)
  · intro hcharge hline
    exact hcharge
      ((routeRPrimeGammaXiNoetherOrientationCharge_eq_zero_iff_re_eq_half rho).2
        hline)

/-- Global absence of actual completion phantoms. -/
def RouteRPrimeGammaXiGlobalCompletionPhantomFree : Prop :=
  ∀ rho : XiDivisorSupport, ¬ RouteRPrimeGammaXiCompletionPhantom rho

/-- RH is exactly the no-phantom law for the canonical finite arithmetic observer tower. -/
theorem routeRPrimeGammaXiGlobalCompletionPhantomFree_iff_riemannHypothesis :
    RouteRPrimeGammaXiGlobalCompletionPhantomFree ↔ RiemannHypothesis := by
  rw [← routeRPrimeGammaXiGlobalNoetherOrientationChargeFree_iff_riemannHypothesis]
  constructor
  · intro h rho
    by_contra hcharge
    exact h rho
      ((routeRPrimeGammaXiCompletionPhantom_iff_noetherCharge_ne_zero rho).2 hcharge)
  · intro h rho hphantom
    exact
      ((routeRPrimeGammaXiCompletionPhantom_iff_noetherCharge_ne_zero rho).1 hphantom)
        (h rho)

end

end RHTower
