import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalPrincipalRegularity
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalFundamentalSlope

/-! Exact Laurent coefficients of the complete original same-copy physical responses. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private theorem simple_denominator_residue {N D : ℂ → ℂ} {w d : ℂ}
    (hN : ContinuousAt N w) (hD : HasDerivAt D d w) (hDz : D w = 0) (hd : d ≠ 0) :
    Tendsto (fun v => (v-w)*(N v/D v)) (𝓝[≠] w) (𝓝 (N w/d)) := by
  have h := (hN.tendsto.mono_left nhdsWithin_le_nhds).div hD.tendsto_slope hd
  apply h.congr'
  filter_upwards [] with v
  simp only [Pi.div_apply,slope_def_field,hDz,sub_zero,div_div_eq_mul_div]
  ring

/-- The original unit source has its literal cleared numerator divided by the derived denominator slope. -/
theorem physicalReducedGreen_residue_tendsto (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (t : ℝ) (ht : t < 0) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*
      continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q branch) a 1 t)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
        (physicalRate q branch) a t/physicalFundamentalDenominatorSlope q branch side)) := by
  have hw := physicalFundamentalFrequency_strip q side
  have hN := clearedReducedGreen_analyticAt _ (physicalRadialFrequency q) (physicalRate q branch) a
    hw.1 (abs_lt.mp hw.2).1 t ht
  have hD := physicalFundamental_clearingFactor_hasDerivAt q branch side
  have hz := physicalFundamental_clearingFactor_zero q branch side
  have hd := physicalFundamental_denominatorSlope_ne_zero q branch side
  have h := simple_denominator_residue hN.continuousAt hD hz hd
  apply h.congr'
  filter_upwards [hD.eventually_ne (c := 0) hd] with w hwD
  have hs : w-2*physicalRate q branch ≠ 0 := by
    intro he
    apply hwD
    simp only [reducedGreenClearingFactor,he,neg_zero,zero_mul]
  have hc : connection w (physicalRadialFrequency q) ≠ 0 := by
    intro he
    apply hwD
    simp only [reducedGreenClearingFactor,he,mul_zero]
  rw [clearedReducedGreen_eq _ _ _ _ hs hc]
  congr 1
  exact mul_div_cancel_left₀ _ hwD

/-- Derived coefficient of the actual full response, retaining the entire angular and radial source. -/
def physicalSelfResidueCoefficient (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (t : ℝ) : ℂ :=
  physicalSelfSourceCoefficient q*
    (clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
      (physicalRate q branch) a t/physicalFundamentalDenominatorSlope q branch side)

/-- All three principal channels are regular here, so the full physical Laurent coefficient is exactly the retained source product. -/
theorem continuedPhysicalSelfResponse_residue_tendsto (q : XiZeroCopy) (branch side : Bool) (a : ℂ)
    (t : ℝ) (ht : t < 0) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)*continuedPhysicalSelfResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 (physicalSelfResidueCoefficient q branch side a t)) := by
  have hU := (physicalReducedGreen_residue_tendsto q branch side a t ht).const_mul
    (physicalSelfSourceCoefficient q)
  have hB : Tendsto (fun w => physicalSelfPrincipalResponse q branch w a t)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (physicalSelfPrincipalResponse q branch (physicalFundamentalFrequency q side) a t)) :=
    (physicalSelfPrincipalResponse_analyticAt q branch side a t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun w : ℂ => w-physicalFundamentalFrequency q side)
      (𝓝[≠] physicalFundamentalFrequency q side) (𝓝 0) := by
    have hx : Tendsto (fun w : ℂ => w) (𝓝[≠] physicalFundamentalFrequency q side)
        (𝓝 (physicalFundamentalFrequency q side)) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hx.sub_const (physicalFundamentalFrequency q side)
  have h := hU.add (hw.mul hB)
  simp only [zero_mul,add_zero] at h
  apply h.congr'
  filter_upwards [] with w
  rw [continuedPhysicalSelfResponse_decomposition]
  ring

/-- No denominator degeneracy remains: cancellation is precisely angular-source or radial-moment cancellation. -/
theorem physicalSelfResidueCoefficient_zero_iff (q : XiZeroCopy) (branch side : Bool) (a : ℂ) (t : ℝ) :
    physicalSelfResidueCoefficient q branch side a t = 0 ↔
      physicalSelfSourceCoefficient q = 0 ∨
      clearedReducedGreen (physicalFundamentalFrequency q side) (physicalRadialFrequency q)
        (physicalRate q branch) a t = 0 := by
  simp only [physicalSelfResidueCoefficient,mul_eq_zero,div_eq_zero_iff,
    physicalFundamental_denominatorSlope_ne_zero,or_false]

end
end RHTower.D4BMJointSource
