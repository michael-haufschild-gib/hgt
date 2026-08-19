import GaloisForLFunctions.RHTower.SuzukiFriedrichsExtension
import GaloisForLFunctions.RHTower.SuzukiDirichletFormCore

/-!
# Suzuki (2026), Theorem 1.1

This is the closed Friedrichs-extension statement for the literal operators in
Masatoshi Suzuki, *Weil's quadratic form via the screw function*, Theorem 1.1.
`suzukiWeilFriedrichsOperator a` is the operator represented by the completed exact Weil form;
the three conclusions certify that it is the self-adjoint extension of the literal Dirichlet
screw operator and that the latter's form-domain lift is dense in that completed form domain.
No Riemann-hypothesis, regularity, density, or numerical premise is assumed.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Suzuki (2026), Theorem 1.1: the literal interval Weil operator is the Friedrichs
extension of `B_a = D† G_a D`.  The last conjunct is precisely the form-core closure that
identifies this represented self-adjoint operator with the Friedrichs extension. -/
theorem suzukiTheoremOneOne_friedrichsExtension
    (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (suzukiWeilFriedrichsOperator a) ∧
      suzukiDirichletScrewOperator a ≤ suzukiWeilFriedrichsOperator a ∧
      DenseRange (suzukiDirichletDomainCCMFormLift a) := by
  exact ⟨suzukiWeilFriedrichsOperator_isSelfAdjoint a,
    suzukiDirichletScrewOperator_le_weilFriedrichsOperator a,
    denseRange_suzukiDirichletDomainCCMFormLift a⟩

end RHTower
