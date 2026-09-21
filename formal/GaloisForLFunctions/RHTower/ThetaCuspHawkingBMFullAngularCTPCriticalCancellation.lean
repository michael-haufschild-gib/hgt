import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCTPSchwarz

/-!
# Critical-fibre cancellation of the literal full-circle CTP source

The literal branch-completed CTP source has the exact Schwarz real structure on the
critical fibre.  Combined with the already-formalized reflection classification, this
forces its real part to vanish there at unit source amplitude.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff ENNReal SchwartzMap

namespace RHTower.D4BMFullAngularSourceReflection

open D4BMGlobalAngularResponse D4BMQuadraticMixedSource D4BMModularCore D4BMHorizon
open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMFullSourceReciprocity
open D4BMJointSource

noncomputable section

/-- The real branch-completed literal CTP source cancels on the critical fibre. -/
theorem fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_on_critical
    (q : XiZeroCopy) (hq : (deningerDivisorThetaEigen q).re = (1 / 2 : ℝ))
    (X k : ℝ) :
    (fullCircleCrossBranchSymmetricCausalPair q 1 X k).re = 0 := by
  apply (fullCircleCrossBranchSymmetricCausalPair_re_eq_zero_iff_conjInvariant_on_critical
    q hq 1 X k).mpr
  have h := congrArg Complex.re
    (fullCircleCrossBranchSymmetricCausalPair_conj_unit q X k)
  simpa using h.symm

end

end RHTower.D4BMFullAngularSourceReflection
