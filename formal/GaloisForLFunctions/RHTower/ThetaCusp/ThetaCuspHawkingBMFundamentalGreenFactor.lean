import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalSourceMoment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceClearedRadialAdmission

/-! The complete fundamental pole numerator separates into a nonvanishing mode and one fixed source moment. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Moving the splitting point transfers precisely the same density between the two actual source moments. -/
theorem fundamental_source_sum_hasDerivAt (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    HasDerivAt (fun r =>
      firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) r w+
      ∫ z in Ioc r (1:ℝ), normalizable w chi z*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 z) 0 b := by
  have hM := horizonFirstMoment_hasDerivAt s chi a 1 (reducedGreenGradient chi s 1) w hw hwr hb
  have hO := outerSourceIntegral_hasDerivAt s chi a 1 (reducedGreenGradient chi s 1) w hb
  exact (hM.add hO).congr_deriv (by
    rw [horizonMellinCore_fundamental w chi s a hw hf ⟨hb.1.le,hb.2⟩,
      normalizable_source_fundamental w chi s a hf hb.1]
    ring)

/-- The single fixed elementary moment equals the original complete pairing at every interior cut. -/
theorem fundamental_source_sum_eq_moment (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) b w+
      (∫ z in Ioc b (1:ℝ), normalizable w chi z*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 z)=
        fundamentalSourceMoment w s a := by
  rw [fundamentalSourceMoment_eq_original w chi s a hw hf]
  apply isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun r : ℝ =>
    firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) r w+
    ∫ z in Ioc r (1:ℝ), normalizable w chi z*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 z)
    isPreconnected_Ioo
  · intro z hz
    exact (fundamental_source_sum_hasDerivAt w chi s a hw hwr hf hz).differentiableAt.differentiableWithinAt
  · intro z hz
    exact (fundamental_source_sum_hasDerivAt w chi s a hw hwr hf hz).deriv
  · exact hb
  · constructor <;> norm_num

/-- Both original endpoint integrals combine into an elementary, nonvanishing observation mode times one source scalar. -/
theorem clearedReducedGreen_fundamental_factor (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) (t : ℝ) (ht : t < 0) :
    clearedReducedGreen w chi s a t=
      (power (w/2) (horizonCoordinate t)*power (1/2) (1-horizonCoordinate t))*
        (fundamentalSourceMoment w s a*clearedOnset s w) := by
  have hb := horizonCoordinate_interior t ht
  have hc : connection w chi=0 := by
    rcases hf with rfl | rfl
    · exact (connection_fundamental_zero chi).1
    · exact (connection_fundamental_zero chi).2
  rw [clearedReducedGreen_at_connection_zero w chi s a hc t,
    horizon_eq_normalizable_fundamental w chi hw hf hb,← mul_add,
    fundamental_source_sum_eq_moment w chi s a hw hwr hf hb,
    normalizable_fundamental_value w chi hf,mul_assoc]

/-- No interior observation point can hide a nonzero complete fundamental source moment. -/
theorem clearedReducedGreen_fundamental_zero_iff (w chi s a : ℂ) (hw : w.im ≠ 0) (hwr : -2 < w.re)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) (t : ℝ) (ht : t < 0) :
    clearedReducedGreen w chi s a t=0 ↔
      fundamentalSourceMoment w s a=0 ∨ clearedOnset s w=0 := by
  have hb := horizonCoordinate_interior t ht
  have hn : power (w/2) (horizonCoordinate t)*power (1/2) (1-horizonCoordinate t) ≠ 0 :=
    mul_ne_zero (power_ne_zero (w/2) hb.1) (power_ne_zero (1/2) (sub_pos.mpr hb.2))
  rw [clearedReducedGreen_fundamental_factor w chi s a hw hwr hf t ht,mul_eq_zero]
  simp only [hn,false_or,mul_eq_zero]

end
end RHTower.D4BMJointSource
