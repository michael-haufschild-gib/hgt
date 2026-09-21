import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceSchwarz
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularEnergySchwarz
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularSourceReflection

/-!
# Schwarz covariance of the literal full-circle CTP source

This module transports the exact original-time source, fundamental physical rate, and
direct-minus-image angular kernel through the ordered two-event CTP product integral.
At unit source amplitude, the completed branch pair is Schwarz covariant.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff ENNReal SchwartzMap

namespace RHTower.D4BMFullAngularSourceReflection

open D4BMGlobalAngularResponse D4BMQuadraticMixedSource D4BMModularCore D4BMHorizon
open D4BMFullAngularCircle D4BMFullAngularReconstruction D4BMFullSourceReciprocity
open D4BMJointSource

noncomputable section

/-- Pointwise Schwarz covariance of the literal two-event full-circle source density. -/
theorem fullCircleSourcePairDensity_conj (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ)
    (z : Event × Event) :
    (starRingEnd ℂ) (fullCircleSourcePairDensity q branch b c a d X k z) =
      fullCircleSourcePairDensity (xiZeroCopyConjEquiv q) branch b c
        ((starRingEnd ℂ) a) ((starRingEnd ℂ) d) X k z := by
  unfold fullCircleSourcePairDensity
  rw [map_mul, map_mul,
    D4BMJointSource.timeReducedCoefficient_conj,
    D4BMModularCore.physicalRate_conj,
    D4BMModularCore.angularDirichletKernel_conj,
    D4BMJointSource.timeReducedCoefficient_conj,
    D4BMModularCore.physicalRate_conj]

/-- Schwarz covariance of the ordered literal cross-branch CTP pair at unit amplitude. -/
theorem fullCircleCrossBranchCausalPair_conj_unit (q : XiZeroCopy)
    (branch : Bool) (X k : ℝ) :
    (starRingEnd ℂ) (fullCircleCrossBranchCausalPair q branch 1 X k) =
      fullCircleCrossBranchCausalPair (xiZeroCopyConjEquiv q) branch 1 X k := by
  unfold fullCircleCrossBranchCausalPair
  rw [map_sub, ← integral_conj, ← integral_conj]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      simpa only [map_one] using
        fullCircleSourcePairDensity_conj q branch false true (1 : ℂ) 1 X k z)
  · apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      simpa only [map_one] using
        fullCircleSourcePairDensity_conj q branch true false (1 : ℂ) 1 X k z)

/-- Schwarz covariance of the branch-completed literal CTP source at unit amplitude. -/
theorem fullCircleCrossBranchSymmetricCausalPair_conj_unit (q : XiZeroCopy)
    (X k : ℝ) :
    (starRingEnd ℂ) (fullCircleCrossBranchSymmetricCausalPair q 1 X k) =
      fullCircleCrossBranchSymmetricCausalPair (xiZeroCopyConjEquiv q) 1 X k := by
  unfold fullCircleCrossBranchSymmetricCausalPair
  rw [map_add,
    fullCircleCrossBranchCausalPair_conj_unit,
    fullCircleCrossBranchCausalPair_conj_unit]

end

end RHTower.D4BMFullAngularSourceReflection
