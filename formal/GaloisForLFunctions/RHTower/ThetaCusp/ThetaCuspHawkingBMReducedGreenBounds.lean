import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMReducedGreenContinuation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGreenProfileBounds
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceContinuationCorridor

/-! The independent-angular reduced response retains the original boundedness and zero endpoint. -/
open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem reducedGreen_boundary {w chi : ℂ} (h : Chamber w chi) (s a J T : ℂ) :
    Tendsto (reducedGreen w chi s a J T) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  simpa only [reducedGreen,zero_mul,sub_zero] using!
    (tortoiseGreen_boundary h s a J (reducedGreenGradient chi s J) T).sub
      ((radialLift_boundary s w a T).mul_const J)

theorem reducedGreen_bounded {w chi : ℂ} (h : Chamber w chi) (s a J T : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖reducedGreen w chi s a J T t‖ ≤ C := by
  obtain ⟨C,hC,hG⟩ := tortoiseGreen_bounded h s a J (reducedGreenGradient chi s J) T
  obtain ⟨D,hD,hL⟩ := radialLift_bounded s w a T (chamber_re_pos h)
  refine ⟨C+D*‖J‖,add_nonneg hC (mul_nonneg hD (norm_nonneg _)),fun t ht => ?_⟩
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add (hG t ht) (mul_le_mul_of_nonneg_right (hL t ht) (norm_nonneg _))

/-- With the actual source rate, continuation preserves the original outer trace on the physical overlap. -/
theorem continuedReducedGreen_physical_boundary (q : XiZeroCopy) (branch : Bool) (w chi a J : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hc : Chamber w chi) :
    Tendsto (continuedReducedGreen w chi (physicalRate q branch) a J) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  apply (reducedGreen_boundary hc (physicalRate q branch) a J
    (onsetTransform (2*physicalRate q branch) w)).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (continuedReducedGreen_eq_original w chi _ a J hwi (by linarith) (by linarith) t ht).symm

/-- The actual reduced-source continuation has a uniform spatial bound on the physical overlap. -/
theorem continuedReducedGreen_physical_bounded (q : XiZeroCopy) (branch : Bool) (w chi a J : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hc : Chamber w chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0, ‖continuedReducedGreen w chi (physicalRate q branch) a J t‖ ≤ C := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  obtain ⟨C,hC,hG⟩ := reducedGreen_bounded hc (physicalRate q branch) a J
    (onsetTransform (2*physicalRate q branch) w)
  refine ⟨C,hC,fun t ht => ?_⟩
  rw [continuedReducedGreen_eq_original w chi _ a J hwi (by linarith) (by linarith) t ht]
  exact hG t ht

end
end RHTower.D4BMJointSource
