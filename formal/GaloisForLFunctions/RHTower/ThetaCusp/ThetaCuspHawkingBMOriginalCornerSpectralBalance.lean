import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMTemporalNormalizableOuterCurrent

/-! The physical opposite-mode coefficient, its derivative, and the original radial norm.
The derivative of the meromorphic response retains an exact pole after multiplication
by the vanishing opposite-mode coefficient. -/
open Complex Set Filter Topology
namespace RHTower.D4BMOriginalCornerSpectralBalance
open D4BMLaplaceRadial D4BMJointSource D4BMModularCore D4BMFundamentalNorm
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

/-- The derivative of the original connection equals twice the physical frequency
times the original horizon-restored radial norm. -/
theorem physical_connectionSlope_eq_norm (q : XiZeroCopy) (side : Bool) :
    connectionSimpleSlope (physicalFundamentalFrequency q side) (physicalRadialFrequency q) side =
      2 * physicalFundamentalFrequency q side * normFinitePart (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hw0 : w ≠ 0 := by
    intro h
    apply hw.1
    change w.im = 0
    rw [h]
    rfl
  have ho := connection_argument_sum w (physicalRadialFrequency q) side
  rw [physicalFundamental_zeroArgument q side, zero_add] at ho
  change connectionSimpleSlope w (physicalRadialFrequency q) side = 2 * w * normFinitePart w
  rw [connectionSimpleSlope, ho, gaussC, normFinitePart_eq_gamma w (abs_lt.mp hw.2).1 hw.1,
    add_comm (1 : ℂ) w, Complex.Gamma_add_one w hw0]
  have hg : Gamma (3/2 : ℂ) = (1/2 : ℂ) * Gamma (1/2 : ℂ) := by
    rw [show (3/2 : ℂ) = 1/2+1 by norm_num, Complex.Gamma_add_one _ (by norm_num)]
  rw [hg, add_comm (3/2 : ℂ) w]
  ring

/-- The first derivative of the actual opposite-mode coefficient is the radial norm. -/
theorem physical_oppositeCoefficient_hasDerivAt (q : XiZeroCopy) (side : Bool) :
    HasDerivAt (fun w => connection w (physicalRadialFrequency q) / (2*w))
      (normFinitePart (physicalFundamentalFrequency q side))
      (physicalFundamentalFrequency q side) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hw0 : w ≠ 0 := by
    intro h
    apply hw.1
    change w.im = 0
    rw [h]
    rfl
  have hd := (physicalFundamental_connection_hasDerivAt q side).div
    ((hasDerivAt_id w).const_mul 2) (mul_ne_zero (by norm_num) hw0)
  apply hd.congr_deriv
  rw [physicalFundamentalFrequency_connection_zero, physical_connectionSlope_eq_norm]
  change (2*w*normFinitePart w*(2*w)-0* (2*1)) / (2*w)^(2 : ℕ) = normFinitePart w
  field_simp
  ring

/-- Differentiating the actual response gives the exact quadratic leading coefficient,
including the case of a vanishing source residue. -/
theorem physical_response_derivative_leading (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side)^(2 : ℕ) *
      deriv (fun u => continuedPhysicalSelfResponse q branch u a t) w)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (-physicalSelfResidueCoefficient q branch side a t)) := by
  let w₀ := physicalFundamentalFrequency q side
  let R := physicalSelfResidueCoefficient q branch side a t
  obtain ⟨g, hg, he⟩ := continuedPhysicalSelfResponse_laurent_remainder q branch side a t t.property
  change AnalyticAt ℂ g w₀ at hg
  change (fun w => continuedPhysicalSelfResponse q branch w a t) =ᶠ[𝓝[≠] w₀]
    (fun w => R/(w-w₀)+g w) at he
  have hd := he.nhdsNE_deriv
  have hlim : Tendsto (fun w => -R+(w-w₀)^(2 : ℕ)*deriv g w) (𝓝 w₀) (𝓝 (-R)) := by
    simpa using (tendsto_const_nhds.add
      (((tendsto_id.sub_const w₀).pow 2).mul hg.deriv.continuousAt.tendsto))
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [hd, hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hgw hn
  have hn' : w-w₀ ≠ 0 := sub_ne_zero.mpr hn
  have hp := (hasDerivAt_const w R).div ((hasDerivAt_id w).sub_const w₀) hn'
  have hder : deriv (fun u : ℂ => R/(u-w₀)+g u) w = -R/(w-w₀)^(2 : ℕ)+deriv g w := by
    simpa only [Pi.add_def, Pi.div_def, id_eq, zero_mul, zero_sub, mul_one] using
      (hp.add hgw.differentiableAt.hasDerivAt).deriv
  rw [hw, hder]
  dsimp only [w₀] at hn' ⊢
  field_simp [hn']

/-- The original opposite coefficient does not erase the differentiated response pole:
its residue is minus the original radial norm times the complete response residue. -/
theorem physical_opposite_response_derivative_residue (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) :
    Tendsto (fun w => (w-physicalFundamentalFrequency q side) *
      (connection w (physicalRadialFrequency q)/(2*w)) *
        deriv (fun u => continuedPhysicalSelfResponse q branch u a t) w)
      (𝓝[≠] physicalFundamentalFrequency q side)
      (𝓝 (-normFinitePart (physicalFundamentalFrequency q side) *
        physicalSelfResidueCoefficient q branch side a t)) := by
  let w₀ := physicalFundamentalFrequency q side
  have hβ := (physical_oppositeCoefficient_hasDerivAt q side).tendsto_slope
  have hlim := hβ.mul (physical_response_derivative_leading q branch side a t)
  simp only [mul_neg, neg_mul] at hlim ⊢
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hn : w-w₀ ≠ 0 := sub_ne_zero.mpr hw
  simp only [slope_def_field, physicalFundamentalFrequency_connection_zero, zero_div, sub_zero]
  change (connection w (physicalRadialFrequency q)/(2*w)/(w-w₀))*
      ((w-w₀)^(2 : ℕ) * deriv (fun u => continuedPhysicalSelfResponse q branch u a t) w) = _
  dsimp only [w₀] at hn ⊢
  field_simp [hn]

/-- In the complete radial temporal residue, the radial norm cancels the connection slope,
leaving precisely the original angular, source-moment and onset factors. -/
theorem physical_radial_residue_source_value (q : XiZeroCopy) (branch side : Bool)
    (a : ℂ) (zang : D4BMHorizon.Point) :
    physicalTemporalFundamentalRadialResidue q branch side a zang =
      D4BMPhysicalModeAction.modeAngularSquare (D4BMPhysicalModeAction.physicalModeAngularJet q zang) *
      (physicalAngularParameter q^(2 : ℕ)-1/4-2) * physicalSelfSourceCoefficient q *
      fundamentalSourceMoment (physicalFundamentalFrequency q side) (physicalRate q branch) a *
      clearedOnset (physicalRate q branch) (physicalFundamentalFrequency q side) /
      (physicalFundamentalFrequency q side-2*physicalRate q branch) := by
  let w := physicalFundamentalFrequency q side
  have hw := physicalFundamentalFrequency_strip q side
  have hw0 : w ≠ 0 := by
    intro h
    apply hw.1
    change w.im = 0
    rw [h]
    rfl
  have hn := normFinitePart_ne_zero w (abs_lt.mp hw.2).1 hw.1
  have hs := physicalFundamentalFrequency_sub_sourceRate_ne_zero q branch side
  unfold physicalTemporalFundamentalRadialResidue physicalTemporalFundamentalAmplitude
    physicalFundamentalDenominatorSlope
  rw [physical_connectionSlope_eq_norm]
  dsimp only [w] at hw0 hn
  field_simp [hw0, hn, hs]

end
end RHTower.D4BMOriginalCornerSpectralBalance
