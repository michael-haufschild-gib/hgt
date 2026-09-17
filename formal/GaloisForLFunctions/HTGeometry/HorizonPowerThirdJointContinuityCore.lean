import GaloisForLFunctions.HTGeometry.HorizonPowerThirdJetCore
import GaloisForLFunctions.HTGeometry.HorizonLogJointContinuityCore

/-! Pointwise joint continuity of the literal third source-power derivative. -/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem horizonPowerThirdCore_joint_continuousAt (p : ℂ × ℝ) (hp : p.2 < 1) :
    ContinuousAt (fun q : ℂ × ℝ => horizonPowerThirdCore q.1 q.2) p := by
  obtain ⟨hL, hL1, hL2, hL3⟩ := literalSourceHorizonLog_jets_joint_continuousAt p hp
  have hcast (f : ℂ × ℝ → ℝ) (hf : ContinuousAt f p) :
      ContinuousAt (fun q : ℂ × ℝ => (f q : ℂ)) p :=
    Complex.ofRealCLM.continuous.continuousAt.comp hf
  have hP : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonPower q.1 q.2) p := by
    unfold literalSourceHorizonPower
    exact ((hcast _ hL).mul continuousAt_fst).cexp
  have hX := (hcast _ hL1).mul continuousAt_fst
  have hY := (hcast _ hL2).mul continuousAt_fst
  have hZ := (hcast _ hL3).mul continuousAt_fst
  unfold horizonPowerThirdCore
  exact (((hZ.add ((continuousAt_const.mul hY).mul hX)).add (hX.pow 3)).mul hP)

end
end GaloisForLFunctions.HTGeometry
