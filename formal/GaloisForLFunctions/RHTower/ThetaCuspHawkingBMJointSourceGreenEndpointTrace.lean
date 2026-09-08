import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceResidualCoefficients
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalWavePotential

/-! The actual endpoint Green difference has zero trace in the original tortoise coordinate. -/
open Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMLaplaceRadial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

/-- The physical endpoint is approached from inside the original radial interval. -/
theorem horizonCoordinate_tendsto_boundary :
    Tendsto horizonCoordinate (𝓝[<] (0:ℝ)) (𝓝[<] (1:ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h := horizonCoordinate_continuous.tendsto (0:ℝ)
    have he : horizonCoordinate 0=1 := by simp [horizonCoordinate,radialUnit]
    rw [he] at h
    exact h.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (horizonCoordinate_interior x hx).2

/-- The admitted original Green response has zero tortoise endpoint trace. -/
theorem tortoiseGreen_boundary {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Tendsto (tortoiseGreen w chi s a J K T) (𝓝[<] (0:ℝ)) (𝓝 0) :=
  (response_boundary h s a J K T).comp horizonCoordinate_tendsto_boundary

/-- The exact square lift vanishes at the endpoint. -/
theorem radialLift_zero (s w a T : ℂ) : radialLift s w a T 0=0 := by
  simp [radialLift,radialUnit]

/-- Its actual negative-ray limit agrees with that value. -/
theorem radialLift_boundary (s w a T : ℂ) :
    Tendsto (radialLift s w a T) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have h := (radialLift_hasDerivAt s w a T 0).continuousAt.tendsto
  rw [radialLift_zero] at h
  exact h.mono_left inf_le_left

/-- The literal Green correction and the actual causal Laplace profile share the zero endpoint trace. -/
theorem principalDifference_boundary (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (i : Fin 3) :
    Tendsto (principalDifference q branch w a T i) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have hg := tortoiseGreen_boundary (hw i) (physicalRate q branch) a
    (principalAmplitude q i) (principalGradient q branch i) T
  have hl := (radialLift_boundary (physicalRate q branch) w a T).mul_const (principalAmplitude q i)
  simpa only [principalDifference,zero_mul,sub_zero] using! hg.sub hl

end
end RHTower.D4BMJointSource
