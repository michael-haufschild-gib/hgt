import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularSourceReflection
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsLiftDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCTPCriticalCancellation

/-!
# PW-B completed CTP source in original cap/lift coordinates

The branch-completed PW-B numerator and the literal cyclic Peierls pairing
use the same full direct-minus-image two-event density. Their source-leg
ordering agrees with `fullCausalSourcePair q branch true false`, not its
negative. Consequently the completed numerator is exactly twice the native
retarded-minus-future-minus-cap functional plus the two branch lift defects.

This closes the CTP-to-cap/lift identification only. It does not identify
that scalar with the fixed-grade PW imbalance or prove RH.
-/

namespace RHTower

open D4BMFullAngularSourceReflection
open D4BMFullAngularCausalPeierls
open D4BMLiteralCyclicPeierlsLiftDefect
open D4BMOriginalCausalDifference
open D4BMFullSourceReciprocity
open D4BMJointSource
open D4BMOriginalCausalPotential
open D4BMFutureHorizon
open D4BMModularCore
open D4BMCompleteOriginalWeakSource

noncomputable section
set_option autoImplicit false

/-- The PW-B ordered branch is the existing full causal pairing with the
`true,false` source-leg order; there is no sign reversal. -/
theorem pwb_fullCircleCrossBranch_eq_fullCausalSourcePair
    (q : XiZeroCopy) (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair q branch a X k =
      fullCausalSourcePair q branch true false a a X k := by
  rw [fullCausalSourcePair_decomposition]
  rfl

/-- Each PW-B branch retains the original source pair and its exact
full-minus-native lift defect. -/
theorem pwb_fullCircleCrossBranch_native_lift
    (q : XiZeroCopy) (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair q branch a X k =
      causalSourcePair q true false a a X k +
        causalSourceLiftDefect q branch true false a a X k := by
  rw [pwb_fullCircleCrossBranch_eq_fullCausalSourcePair,
    fullCausalSourcePair_eq_native_add_liftDefect]

/-- The literal original retarded, corrected-future, and cap fields are the
common native part of the PW-B branch pairing. -/
theorem pwb_fullCircleCrossBranch_original_fields_lift
    (q : XiZeroCopy) (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair q branch a X k =
      (∫ p : D4BMLiteralCyclicPeierlsLiftDefect.Event,
        timeReducedCoefficient (physicalRate q true) a p.1 p.2 *
          (originalPotential q false a (p.1 + p.2) (p.1 - p.2) X k -
            correctedFutureField q false a (p, X + Complex.I * k) -
              capBoundaryField q false a p.1 p.2 X k) ∂
          D4BMLiteralCyclicPeierlsLiftDefect.eventMeasure) +
        causalSourceLiftDefect q branch true false a a X k := by
  rw [pwb_fullCircleCrossBranch_eq_fullCausalSourcePair,
    fullCausalSourcePair_original_fields_liftDefect]

/-- Original native Peierls action, retaining the actual cap rather than
replacing it by a normalized scalar receiver. -/
def pwbOriginalNativeCapFunctional
    (q : XiZeroCopy) (a : ℂ) (X k : ℝ) : ℂ :=
  ∫ p : D4BMLiteralCyclicPeierlsLiftDefect.Event,
    timeReducedCoefficient (physicalRate q true) a p.1 p.2 *
      (originalPotential q false a (p.1 + p.2) (p.1 - p.2) X k -
        correctedFutureField q false a (p, X + Complex.I * k) -
          capBoundaryField q false a p.1 p.2 X k) ∂
      D4BMLiteralCyclicPeierlsLiftDefect.eventMeasure

/-- Branch completion duplicates only the native pair. Both full-minus-native
lift defects remain separately visible. -/
theorem pwb_completedCTP_native_lift_exact
    (q : XiZeroCopy) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair q a X k =
      2 * causalSourcePair q true false a a X k +
        causalSourceLiftDefect q true true false a a X k +
        causalSourceLiftDefect q false true false a a X k := by
  rw [fullCircleCrossBranchSymmetricCausalPair,
    pwb_fullCircleCrossBranch_native_lift q true,
    pwb_fullCircleCrossBranch_native_lift q false]
  ring

/-- Exact completed PW-B source normal form: original causal cap plus both
ordered lift defects. The unproved step is its source-derived comparison with
the PW grade imbalance. -/
theorem pwb_completedCTP_original_cap_lift_exact
    (q : XiZeroCopy) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair q a X k =
      2 * pwbOriginalNativeCapFunctional q a X k +
        causalSourceLiftDefect q true true false a a X k +
        causalSourceLiftDefect q false true false a a X k := by
  rw [pwb_completedCTP_native_lift_exact,
    causalSourcePair_original_fields]
  change
    2 * pwbOriginalNativeCapFunctional q a X k +
      causalSourceLiftDefect q true true false a a X k +
      causalSourceLiftDefect q false true false a a X k = _
  rfl

/-- On the critical divisor fibre, the real original retarded/future/cap
pairing is canceled exactly by both full-minus-native lift defects. This is
not an all-divisor extinction law. -/
theorem pwb_original_cap_lift_re_balance_on_critical
    (q : XiZeroCopy) (hq : (deningerDivisorThetaEigen q).re = (1 / 2 : ℝ))
    (X k : ℝ) :
    (2 * pwbOriginalNativeCapFunctional q 1 X k +
      causalSourceLiftDefect q true true false 1 1 X k +
      causalSourceLiftDefect q false true false 1 1 X k).re = 0 := by
  rw [← pwb_completedCTP_original_cap_lift_exact]
  exact fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_on_critical q hq X k

end

end RHTower
