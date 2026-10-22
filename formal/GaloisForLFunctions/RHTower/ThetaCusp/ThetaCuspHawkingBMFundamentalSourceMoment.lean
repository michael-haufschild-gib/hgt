import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFundamentalRadialModes
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenNumerator

/-! The elementary source pairing at the original fundamental radial resonance. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The actual fundamental source after removal of only the singular Mellin power. -/
def fundamentalSourceCore (w s a : ℂ) (z : ℝ) : ℂ :=
  power (1/2) (1-z)*sourceRemainder s w a 1
    ((w+1)*(w+2)/2-(s+1)*(s+2)) 1 z

/-- One fixed, source-faithful finite-part pairing; the original onset factor remains separate. -/
def fundamentalSourceMoment (w s a : ℂ) : ℂ :=
  firstEndpointMellin (fun u => fundamentalSourceCore u s a) (1/2) w+
    ∫ z in Ioc (1/2:ℝ) 1, (z:ℂ)^w*fundamentalSourceCore w s a z

/-- The physical target gradient becomes its exact fundamental polynomial. -/
theorem reducedGreenGradient_fundamental (w chi s : ℂ)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    reducedGreenGradient chi s 1=(w+1)*(w+2)/2-(s+1)*(s+2) := by
  rcases hf with rfl | rfl
  all_goals unfold reducedGreenGradient; ring_nf; simp only [Complex.I_sq]; ring

/-- The native horizon source core is the elementary core throughout the physical horizon interval. -/
theorem horizonMellinCore_fundamental (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {z : ℝ} (hz : z ∈ Ico 0 1) :
    horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1) w z=
      fundamentalSourceCore w s a z := by
  rw [horizonMellinCore,gaussFactor_horizon_fundamental w chi hw hf hz,
    reducedGreenGradient_fundamental w chi s hf]
  rfl

/-- The actual outer integrand has the same elementary density, including its outer endpoint. -/
theorem normalizable_source_fundamental (w chi s a : ℂ)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {z : ℝ} (hz : 0 < z) :
    normalizable w chi z*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 z=
      (z:ℂ)^w*fundamentalSourceCore w s a z := by
  rw [normalizable_fundamental_value w chi hf,reducedGreenGradient_fundamental w chi s hf]
  have hp : power (w/2) z*power (w/2) z=(z:ℂ)^w := by
    rw [power,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))]
    congr 1
    ring
  dsimp only [sourceProfile,fundamentalSourceCore]
  linear_combination power (1/2) (1-z)*sourceRemainder s w a 1
    ((w+1)*(w+2)/2-(s+1)*(s+2)) 1 z*hp

/-- Replacing the horizon integrand retains the exact endpoint subtraction. -/
theorem firstEndpointMellin_fundamental (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) b w=
      firstEndpointMellin (fun u => fundamentalSourceCore u s a) b w := by
  have hzero := horizonMellinCore_fundamental w chi s a hw hf (show (0:ℝ) ∈ Ico 0 1 by simp)
  unfold firstEndpointMellin firstEndpointMellinRemainder
  rw [hzero]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  dsimp only
  rw [horizonMellinCore_fundamental w chi s a hw hf ⟨hz.1.le,hz.2.trans_lt hb.2⟩]

/-- The fixed elementary moment is exactly the sum of both original source integrals. -/
theorem fundamentalSourceMoment_eq_original (w chi s a : ℂ) (hw : w.im ≠ 0)
    (hf : w=-3/2-Complex.I*chi ∨ w=-3/2+Complex.I*chi) :
    fundamentalSourceMoment w s a=
      firstEndpointMellin (horizonMellinCore s chi a 1 (reducedGreenGradient chi s 1)) (1/2) w+
      ∫ z in Ioc (1/2:ℝ) 1, normalizable w chi z*sourceProfile s w a 1 (reducedGreenGradient chi s 1) 1 z := by
  rw [fundamentalSourceMoment,firstEndpointMellin_fundamental w chi s a hw hf (by constructor <;> norm_num)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  exact (normalizable_source_fundamental w chi s a hf (by linarith [hz.1])).symm

end
end RHTower.D4BMJointSource
