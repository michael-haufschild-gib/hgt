import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsCapDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSquareSourceDifferential

/-!
# Literal cyclic Peierls action expansion

The cap vertex is not a homogeneous angular Green field.  Its exact physical
scalar action contains the complete squared-source gradient energy, with the
coefficient forced by the literal two-leg metric.  This identifies the term
which any B2 cap-to-contact transport must retain alongside full and square
boundary currents.

Proof-chain role:
`literal cap action -> full/square/gradient action expansion -> complete
mixed radial-current transport -> HB B2 decision`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsActionExpansion

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse
open D4BMFullSeedCapPhysicalAction D4BMLiteralCyclicPeierlsCapDefect

noncomputable section
set_option autoImplicit false

/-- Exact physical action of the literal cyclic Peierls vertex.  In
particular, its retained square-action contribution includes the full
hyperbolic gradient energy; it cannot be replaced by a homogeneous
full-minus-square Green current. -/
theorem cyclicPeierlsPhysicalAction_expand (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    cyclicPeierlsPhysicalAction q branch X k =
      parameter q branch * fullAngularField q branch ![X, Real.exp k] +
        (parameter q branch -
          (physicalRate q branch * (physicalRate q branch - 1) / 4) *
            (2 * (physicalRate q branch + 1) * (physicalRate q branch + 2))) *
          fullSquarePotential q ![X, Real.exp k] -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) *
          fullGradientEnergy q ![X, Real.exp k] := by
  unfold cyclicPeierlsPhysicalAction
  rw [full_physicalScalarAction q branch X k,
    physicalScalarAction_eq _ _ (Real.exp_pos k),
    fullSquarePotential_laplacian q branch _ (Real.exp_pos k)]
  ring

end
end RHTower.D4BMLiteralCyclicPeierlsActionExpansion
