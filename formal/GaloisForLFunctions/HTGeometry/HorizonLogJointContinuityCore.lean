import GaloisForLFunctions.HTGeometry.HorizonLogThirdJetCore
import GaloisForLFunctions.HTGeometry.HorizonLogThirdContinuityRule

/-! Pointwise joint continuity of literal source logarithmic-height jets. -/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology
noncomputable section
set_option autoImplicit false

theorem literalSourceHorizonLog_jets_joint_continuousAt (p : ℂ × ℝ) (hp : p.2 < 1) :
    ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLog q.2) p ∧
      ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLogFirst q.2) p ∧
        ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLogSecond q.2) p ∧
          ContinuousAt (fun q : ℂ × ℝ => horizonLogThirdCore q.2) p := by
  have hsub : ContinuousAt (fun x : ℝ => 1 - x) p.2 := by fun_prop
  have hbase : 1 - p.2 ≠ 0 := by linarith
  have hrpow (a : ℝ) : ContinuousAt (fun q : ℂ × ℝ => (1 - q.2) ^ a) p :=
    ((Real.continuousAt_rpow_const (1 - p.2) a (Or.inl hbase)).comp hsub).comp continuousAt_snd
  have hH : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonHeight q.2) p := by
    unfold literalSourceHorizonHeight
    fun_prop
  have hHne : literalSourceHorizonHeight p.2 ≠ 0 := by
    dsimp [literalSourceHorizonHeight]
    positivity
  have hH1 : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonHeightFirst q.2) p := by
    unfold literalSourceHorizonHeightFirst
    exact continuousAt_const.mul (hrpow (-(1 / 2 : ℝ)))
  have hH2 : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonHeightSecond q.2) p := by
    unfold literalSourceHorizonHeightSecond
    exact continuousAt_const.mul (hrpow (-(3 / 2 : ℝ)))
  have hH3 : ContinuousAt (fun q : ℂ × ℝ => horizonLogHeightThirdCore q.2) p := by
    unfold horizonLogHeightThirdCore
    exact continuousAt_const.mul (hrpow (-(5 / 2 : ℝ)))
  have hL : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLog q.2) p := by
    unfold literalSourceHorizonLog
    exact hH.log hHne
  have hL1 : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLogFirst q.2) p := by
    unfold literalSourceHorizonLogFirst
    exact hH1.div hH hHne
  have hL2 : ContinuousAt (fun q : ℂ × ℝ => literalSourceHorizonLogSecond q.2) p := by
    unfold literalSourceHorizonLogSecond
    exact ((hH2.mul hH).sub (hH1.mul hH1)).div (hH.pow 2) (pow_ne_zero 2 hHne)
  have hL3 : ContinuousAt (fun q : ℂ × ℝ => horizonLogThirdCore q.2) p := by
    unfold horizonLogThirdCore
    exact continuousAt_log_third_form
      (fun q : ℂ × ℝ => literalSourceHorizonHeight q.2)
      (fun q : ℂ × ℝ => literalSourceHorizonHeightFirst q.2)
      (fun q : ℂ × ℝ => literalSourceHorizonHeightSecond q.2)
      (fun q : ℂ × ℝ => horizonLogHeightThirdCore q.2)
      hH hH1 hH2 hH3 hHne
  exact ⟨hL, hL1, hL2, hL3⟩

end
end GaloisForLFunctions.HTGeometry
