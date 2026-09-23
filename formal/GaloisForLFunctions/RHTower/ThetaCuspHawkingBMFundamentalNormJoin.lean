import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingPairingFinitePart
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialNorm
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalRadialModes

/-! Joining the original incoming and outer fundamental norms at a common cutoff. -/
namespace RHTower.D4BMFundamentalNorm
open Complex Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry D4BMJointSource D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

private def sqrtKernel (z : ℝ) : ℂ := (Real.sqrt (1-z):ℂ)/2

private theorem sqrtKernel_remainder (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
    sqrtKernel z-1/2-(-1/4)*(z:ℂ)=(z:ℂ)/2*(HalfOrderBeta.core z-HalfOrderBeta.core 0) := by
  rw [sqrtKernel,HalfOrderBeta.sqrt_eq_core z hz,HalfOrderBeta.core_zero]
  ring

private theorem sqrtKernel_remainder_bound (z : ℝ) (hz : z ∈ Icc (0:ℝ) 1) :
    ‖sqrtKernel z-1/2-(-1/4)*(z:ℂ)‖ ≤ (1/4)*z^(2 : ℕ) := by
  rw [sqrtKernel_remainder z hz,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hz.1]
  rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  calc
    _ ≤ (z/2)*((1/2)*z) := mul_le_mul_of_nonneg_left
      (HalfOrderBeta.core_remainder_bound z hz) (div_nonneg hz.1 (by norm_num))
    _ = _ := by ring

private theorem cpow_mul_base (w : ℂ) {z : ℝ} (hz : 0 < z) :
    (z:ℂ)^(w-1)*(z:ℂ)=(z:ℂ)^w := by
  calc
    _ = (z:ℂ)^(w-1)*(z:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]
    _ = _ := by rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hz.ne'),sub_add_cancel]

private theorem sqrtKernel_finitePart_one (w : ℂ) :
    QuadraticEndpointMellin.finitePart (fun _ => sqrtKernel)
      (fun _ => 1/2) (fun _ => -1/4) 1 w=normFinitePart w := by
  have hr : QuadraticEndpointMellin.remainder (fun _ => sqrtKernel)
      (fun _ => 1/2) (fun _ => -1/4) 1 w=
      (1/2:ℂ)*firstEndpointMellinRemainder (fun _ => HalfOrderBeta.core) 1 w := by
    rw [QuadraticEndpointMellin.remainder,firstEndpointMellinRemainder,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [sqrtKernel_remainder z ⟨hz.1.le,hz.2⟩]
    calc
      _ = (1/2:ℂ)*((z:ℂ)^(w-1)*(z:ℂ))*(HalfOrderBeta.core z-HalfOrderBeta.core 0) := by ring
      _ = _ := by rw [cpow_mul_base w hz.1]; ring
  rw [QuadraticEndpointMellin.finitePart,hr,normFinitePart,HalfOrderBeta.finitePart,
    firstEndpointMellin,HalfOrderBeta.core_zero]
  simp only [Complex.ofReal_one,Complex.one_cpow]
  ring

private theorem sqrtKernel_finitePart_join (w : ℂ) (b : ℝ)
    (hb : 0 < b) (hb1 : b ≤ 1) (hw : -2 < w.re) (hw0 : w ≠ 0) (hw1 : w+1 ≠ 0) :
    QuadraticEndpointMellin.finitePart (fun _ => sqrtKernel)
      (fun _ => 1/2) (fun _ => -1/4) b w+
      (1/2:ℂ)*(∫ z in b..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ))=normFinitePart w := by
  have hc : Continuous sqrtKernel :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).div_const 2
  have he := QuadraticEndpointMellin.cutoff_eq (F := fun _ => sqrtKernel)
    (a₀ := fun _ => 1/2) (a₁ := fun _ => -1/4) hb hb1 hw hw0 hw1
    hc.continuousOn (fun z hz => sqrtKernel_remainder_bound z ⟨hz.1.le,hz.2⟩)
  rw [sqrtKernel_finitePart_one] at he
  have hi : (∫ z in b..1, (z:ℂ)^(w-1)*sqrtKernel z)=
      (1/2:ℂ)*(∫ z in b..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _
    dsimp only [sqrtKernel]
    ring
  rw [hi] at he
  dsimp only [QuadraticEndpointMellin.finitePart]
  linear_combination he

private theorem fundamental_first_coefficient (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    horizonGaussFirstCoefficient w chi=-1/2 := by
  have hc : gaussC w ≠ 0 := by
    intro he
    apply hw
    simpa only [gaussC,Complex.add_im,Complex.one_im,Complex.zero_im,zero_add] using congrArg Complex.im he
  rw [horizonGaussFirstCoefficient_eq,div_eq_iff hc]
  rcases hf with rfl | rfl <;> dsimp only [gaussA,gaussB,gaussC] <;> ring

private theorem incomingPairingFactor_fundamental (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) :
    incomingPairingFactor w chi z=sqrtKernel z := by
  rcases hz.2.eq_or_lt with he | hl
  · subst z
    simp [incomingPairingFactor,sqrtKernel]
  · have hs : (Real.sqrt (1-z):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hl)))
    rw [incomingPairingFactor,gaussFactor_horizon_fundamental w chi hw hf ⟨hz.1,hl⟩,
      power_half_eq_sqrt (sub_nonneg.mpr hz.2)]
    dsimp only [sqrtKernel]
    field_simp [hs]

private theorem incomingNormFinitePart_fundamental (w chi : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {b : ℝ} (hb1 : b ≤ 1) :
    incomingNormFinitePart chi b w=QuadraticEndpointMellin.finitePart
      (fun _ => sqrtKernel) (fun _ => 1/2) (fun _ => -1/4) b w := by
  unfold incomingNormFinitePart QuadraticEndpointMellin.finitePart
  dsimp only
  rw [fundamental_first_coefficient w chi hw hf,show (-1/2:ℂ)+1/4=-1/4 by norm_num]
  congr 1
  unfold QuadraticEndpointMellin.remainder
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  dsimp only
  rw [incomingPairingFactor_fundamental w chi hw hf ⟨hz.1.le,hz.2.trans hb1⟩,
    fundamental_first_coefficient w chi hw hf,show (-1/2:ℂ)+1/4=-1/4 by norm_num]

/-- The incoming endpoint finite part and original outer integral join with no cutoff defect. -/
theorem fundamentalNorm_join (w chi : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) (T : ℝ) (hT : T < 0) :
    incomingNormFinitePart chi (horizonCoordinate T) w+
      (∫ t in Ioo T 0, normalizable w chi (horizonCoordinate t)^(2 : ℕ))=normFinitePart w := by
  have hz := horizonCoordinate_interior T hT
  have hw0 : w ≠ 0 := by intro he; exact hw (by simp [he])
  have hw1 : w+1 ≠ 0 := by
    intro he
    apply hw
    simpa only [Complex.add_im,Complex.one_im,Complex.zero_im,add_zero] using congrArg Complex.im he
  have hi : (∫ t in Ioo T 0, normalizable w chi (horizonCoordinate t)^(2 : ℕ))=
      (1/2:ℂ)*(∫ z in horizonCoordinate T..1, (z:ℂ)^(w-1)*(Real.sqrt (1-z):ℂ)) := by
    simp_rw [normalizable_fundamental_value w chi hf]
    change (∫ t in Ioo T 0, mode w t^(2 : ℕ))=_
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hT.le]
    exact mode_square_integral w T hT
  rw [incomingNormFinitePart_fundamental w chi hw hf hz.2.le,hi]
  exact sqrtKernel_finitePart_join w _ hz.1 hz.2.le hwr hw0 hw1

/-- Every actual Xi fundamental mode satisfies the common-cutoff norm identity. -/
theorem physicalFundamentalNorm_join (q : XiZeroCopy) (side : Bool) (T : ℝ) (hT : T < 0) :
    incomingNormFinitePart (physicalRadialFrequency q) (horizonCoordinate T)
      (physicalFundamentalFrequency q side)+
      (∫ t in Ioo T 0, normalizable (physicalFundamentalFrequency q side)
        (physicalRadialFrequency q) (horizonCoordinate t)^(2 : ℕ))=
      normFinitePart (physicalFundamentalFrequency q side) := by
  have hs := physicalFundamentalFrequency_strip q side
  apply fundamentalNorm_join _ _ hs.1 (abs_lt.mp hs.2).1 _ T hT
  rw [physicalFundamentalFrequency_connection_root]
  cases side <;> simp

end
end RHTower.D4BMFundamentalNorm
