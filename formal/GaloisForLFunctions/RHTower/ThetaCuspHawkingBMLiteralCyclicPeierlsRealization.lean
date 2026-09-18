import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsPulseLayer
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsActionExpansion

/-!
# Literal cyclic Peierls cap realization

This leaf joins the literal co-moving pulse transport to the physical
two-leg cap action.  It retains the full angular square and its gradient
energy: the cap limit is not identified with a bare homogeneous scalar
boundary value.  It does not identify this scalar normal trace with the
left-QNM metric contact; that remaining metric-current equality is B2's
only boundary obligation.

Proof-chain role:
`literal direct/image pulse transport + two-arm cap trace + metric action
accounting -> exact late-clock cyclic Peierls cap realization -> left-QNM
metric-current equality -> HB B2`.
-/

open Filter Topology

namespace RHTower.D4BMLiteralCyclicPeierlsRealization

open D4BMHorizon D4BMModularCore
open D4BMFutureSeedHorizon D4BMFutureHorizon D4BMCapRadialMemory
open D4BMFullSeedCapPhysicalAction
open D4BMLiteralCyclicPeierlsCorrectedFutureCap
open D4BMLiteralCyclicPeierlsPulseLayer
open D4BMLiteralCyclicPeierlsCapDefect
open D4BMLiteralCyclicPeierlsActionExpansion

noncomputable section
set_option autoImplicit false

/-- At a late original clock, the actual corrected-future normal trace is
the literal cyclic Peierls physical action, with both cap arms and the
finite-depth direct/image analysis already accounted for. -/
theorem correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_cyclicPeierlsAction
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (hv : 1 < v) :
    Tendsto (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (-parameter q branch * power (2 * physicalRate q branch) 2 * amp ^ 2 *
        cyclicPeierlsPhysicalAction q branch X k * sourceMemory q branch v)) := by
  have hcoefficient :
      (2 * seedTraceCoefficient q branch amp *
          (parameter q branch *
            (fullAngularField q branch ![X, Real.exp k] + fullSquarePotential q ![X, Real.exp k]) /
              2) *
          sourceMemory q branch v -
        parameter q branch *
          (liftTraceCoefficient q branch amp *
            scalarLaplacian (fullSquarePotential q) ![X, Real.exp k] *
              sourceMemory q branch v)) =
        combinedCapPhysicalNormalCoefficient q branch amp v X k := by
    unfold combinedCapPhysicalNormalCoefficient
    rw [full_physicalScalarAction]
    rw [physicalScalarAction_eq _ _ (Real.exp_pos k)]
    ring
  rw [← combinedCapPhysicalNormalCoefficient_eq_cyclicPeierlsAction,
    ← hcoefficient]
  exact correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_late
    q branch amp v X k hv

/-- The same literal cap realization, expanded into the full bulk action.
The unavoidable gradient-energy term records why a scalar `H - c Q` boundary
surrogate cannot close the metric-current step. -/
theorem correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_expandedAction
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) (hv : 1 < v) :
    Tendsto (fun x : ℝ =>
      deriv (fun y : ℝ => correctedFutureCapResidual q branch amp (v - y) y X k) x /
        (capScale x : ℂ)) atBot
      (𝓝 (-parameter q branch * power (2 * physicalRate q branch) 2 * amp ^ 2 *
        (parameter q branch * fullAngularField q branch ![X, Real.exp k] +
          (parameter q branch -
            (physicalRate q branch * (physicalRate q branch - 1) / 4) *
              (2 * (physicalRate q branch + 1) * (physicalRate q branch + 2))) *
              fullSquarePotential q ![X, Real.exp k] -
          (physicalRate q branch * (physicalRate q branch - 1) / 4) *
            fullGradientEnergy q ![X, Real.exp k]) *
        sourceMemory q branch v)) := by
  rw [← cyclicPeierlsPhysicalAction_expand]
  exact correctedFutureCapResidual_ingoing_normal_div_capScale_tendsto_cyclicPeierlsAction
    q branch amp v X k hv

end

end RHTower.D4BMLiteralCyclicPeierlsRealization
