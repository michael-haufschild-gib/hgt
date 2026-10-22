import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSeedCapPhysicalAction

/-!
# Literal cyclic Peierls cap-defect action

The full-minus-native causal lift defect has vertex `H - Q`.  The literal
two-leg Einstein metric instead carries `H - s(s-1) Q / 4`.  This file proves
the exact accounting identity at the noncompact cap: the difference is the
lift-defect physical action plus the retained native cap action, with its
forced coefficient.  Thus no coefficient can be silently absorbed in the
cap/contact comparison.

Proof-chain role:
`full-minus-native causal defect + native cap action = exact physical metric
cap action -> left-QNM contact comparison -> HB B2 decision`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCapDefect

open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMLaplaceRadial D4BMGlobalAngularResponse
open D4BMFutureSeedHorizon D4BMFutureHorizon D4BMCapRadialMemory
open D4BMFullSeedCapPhysicalAction D4BMLiteralCyclicPeierlsLiftDefect

noncomputable section
set_option autoImplicit false

/-- Physical scalar action of the full-minus-native angular vertex. -/
def liftDefectPhysicalAction (q : XiZeroCopy) (branch : Bool) (X k : ℝ) : ℂ :=
  physicalScalarAction (fullAngularField q branch) ![X, Real.exp k] -
    physicalScalarAction (fullSquarePotential q) ![X, Real.exp k]

/-- Native physical cap action retained after the full-minus-native split. -/
def nativeCapPhysicalAction (q : XiZeroCopy) (X k : ℝ) : ℂ :=
  physicalScalarAction (fullSquarePotential q) ![X, Real.exp k]

/-- Exact angular action selected by the literal two-leg physical metric. -/
def cyclicPeierlsPhysicalAction (q : XiZeroCopy) (branch : Bool) (X k : ℝ) : ℂ :=
  physicalScalarAction (fullAngularField q branch) ![X, Real.exp k] -
    (physicalRate q branch * (physicalRate q branch - 1) / 4) *
      physicalScalarAction (fullSquarePotential q) ![X, Real.exp k]

/-- The metric action is the full-minus-native lift-defect action plus exactly
the native cap action still forced by the physical source coefficient. -/
theorem cyclicPeierlsPhysicalAction_eq_liftDefect_add_native (q : XiZeroCopy)
    (branch : Bool) (X k : ℝ) :
    cyclicPeierlsPhysicalAction q branch X k =
      liftDefectPhysicalAction q branch X k +
        (1 - physicalRate q branch * (physicalRate q branch - 1) / 4) *
          nativeCapPhysicalAction q X k := by
  unfold cyclicPeierlsPhysicalAction liftDefectPhysicalAction nativeCapPhysicalAction
  ring

/-- The noncompact combined-cap coefficient factors through the exact physical
two-leg metric action, with no omitted seed or source-cap coefficient. -/
theorem combinedCapPhysicalNormalCoefficient_eq_cyclicPeierlsAction
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    combinedCapPhysicalNormalCoefficient q branch amp v X k =
      -parameter q branch * power (2 * physicalRate q branch) 2 * amp ^ 2 *
        cyclicPeierlsPhysicalAction q branch X k * sourceMemory q branch v := by
  unfold combinedCapPhysicalNormalCoefficient
  unfold seedTraceCoefficient liftTraceCoefficient cyclicPeierlsPhysicalAction
  ring

/-- Literal cap endpoint in full-minus-native variables.  The only part not
already present in the native retarded/future/cap identity is the displayed
lift-defect action; its coefficient is forced. -/
theorem combinedCapPhysicalNormalCoefficient_eq_liftDefect_native
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    combinedCapPhysicalNormalCoefficient q branch amp v X k =
      -parameter q branch * power (2 * physicalRate q branch) 2 * amp ^ 2 *
        (liftDefectPhysicalAction q branch X k +
          (1 - physicalRate q branch * (physicalRate q branch - 1) / 4) *
            nativeCapPhysicalAction q X k) * sourceMemory q branch v := by
  rw [combinedCapPhysicalNormalCoefficient_eq_cyclicPeierlsAction,
    cyclicPeierlsPhysicalAction_eq_liftDefect_add_native]

end

end RHTower.D4BMLiteralCyclicPeierlsCapDefect
