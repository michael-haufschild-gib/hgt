import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalFundamentalFrequencies
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMConnectionSimpleZero
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedGreenNumerator

/-! The original cleared radial denominator has a derived nonzero slope at each physical fundamental resonance. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

theorem physicalFundamental_zeroArgument (q : XiZeroCopy) (side : Bool) :
    connectionZeroArgument (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side = 0 := by
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp only [connectionZeroArgument,Bool.false_eq_true,↓reduceIte]
  all_goals dsimp only [gaussA,gaussB,gaussC]; ring

theorem physicalFundamental_connection_hasDerivAt (q : XiZeroCopy) (side : Bool) :
    HasDerivAt (fun w => connection w (physicalRadialFrequency q))
      (connectionSimpleSlope (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side)
      (physicalFundamentalFrequency q side) :=
  connection_fundamental_hasDerivAt _ _ _ (physicalFundamentalFrequency_strip q side).1
    (physicalFundamental_zeroArgument q side)

theorem physicalFundamental_connectionSlope_ne_zero (q : XiZeroCopy) (side : Bool) :
    connectionSimpleSlope (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side ≠ 0 :=
  connectionSimpleSlope_ne_zero _ _ _ (physicalFundamentalFrequency_strip q side).1
    (physicalFundamental_zeroArgument q side)

def physicalFundamentalDenominatorSlope (q : XiZeroCopy) (branch side : Bool) : ℂ :=
  -(physicalFundamentalFrequency q side-2*physicalRate q branch)*
    connectionSimpleSlope (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side

theorem physicalFundamental_denominatorSlope_ne_zero (q : XiZeroCopy) (branch side : Bool) :
    physicalFundamentalDenominatorSlope q branch side ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side))
    (physicalFundamental_connectionSlope_ne_zero q side)

theorem physicalFundamental_clearingFactor_zero (q : XiZeroCopy) (branch side : Bool) :
    reducedGreenClearingFactor (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
      (physicalRate q branch) = 0 := by
  simp only [reducedGreenClearingFactor,physicalFundamentalFrequency_connection_zero,mul_zero]

/-- The source denominator and original connection normalization are both included in this slope. -/
theorem physicalFundamental_clearingFactor_hasDerivAt (q : XiZeroCopy) (branch side : Bool) :
    HasDerivAt (fun w => reducedGreenClearingFactor w (physicalRadialFrequency q) (physicalRate q branch))
      (physicalFundamentalDenominatorSlope q branch side) (physicalFundamentalFrequency q side) := by
  have h := (((hasDerivAt_id (physicalFundamentalFrequency q side)).sub_const
    (2*physicalRate q branch)).neg).mul (physicalFundamental_connection_hasDerivAt q side)
  convert! h using 1
  simp only [physicalFundamentalDenominatorSlope,physicalFundamentalFrequency_connection_zero,
    mul_zero,zero_add,Pi.neg_apply,id_eq]

end
end RHTower.D4BMJointSource
