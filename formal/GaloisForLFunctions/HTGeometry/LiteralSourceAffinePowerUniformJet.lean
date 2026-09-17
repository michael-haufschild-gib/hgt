import GaloisForLFunctions.HTGeometry.LiteralSourceHorizonPowerUniformJet
import GaloisForLFunctions.HTGeometry.LiteralSourceAffinePowerJets
import GaloisForLFunctions.HTGeometry.UniformThirdOrderJetProduct

/-! Uniform cubic source-pole jets for the literal affine source bracket. -/

namespace GaloisForLFunctions.HTGeometry
open Set Metric
noncomputable section
set_option autoImplicit false

private theorem literalSourceHorizonPower_zero_continuous :
    Continuous (fun α : ℂ => literalSourceHorizonPower α 0) := by
  unfold literalSourceHorizonPower
  fun_prop

private theorem literalSourceHorizonPowerFirst_zero_continuous :
    Continuous (fun α : ℂ => literalSourceHorizonPowerFirst α 0) := by
  have hp := literalSourceHorizonPower_zero_continuous
  unfold literalSourceHorizonPowerFirst
  exact (continuous_const.mul continuous_id).mul hp

private theorem literalSourceHorizonPowerSecond_half_zero_continuous :
    Continuous (fun α : ℂ => literalSourceHorizonPowerSecond α 0 / 2) := by
  have hp := literalSourceHorizonPower_zero_continuous
  have h1 : Continuous (fun α : ℂ => (literalSourceHorizonLogFirst 0 : ℂ) * α) :=
    continuous_const.mul continuous_id
  have h2 : Continuous (fun α : ℂ => (literalSourceHorizonLogSecond 0 : ℂ) * α) :=
    continuous_const.mul continuous_id
  unfold literalSourceHorizonPowerSecond
  apply Continuous.div
  · exact (h2.add (h1.pow 2)).mul hp
  · exact continuous_const
  · intro α
    norm_num

/-- The actual source power times its literal affine angular bracket has all
three source-pole counterterms and one frequency-uniform cubic remainder. -/
theorem exists_literalSourceAffinePower_uniformJet3 (α₀ B₀ B₁ : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧
      HasUniformJet3 (closedBall α₀ 1) (1 / 2)
        (fun α z => literalSourceAffinePower α B₀ B₁ z)
        (fun α => literalSourceHorizonPower α 0 * B₀)
        (fun α => literalSourceHorizonPower α 0 * (-(α * B₀ / 4) - B₁))
        (fun α => literalSourceHorizonPower α 0 *
          (α * (α - 3) * B₀ / 32 + α * B₁ / 4)) C := by
  let S : Set ℂ := closedBall α₀ 1
  have hS : IsCompact S := isCompact_closedBall _ _
  obtain ⟨CP, hCP0, hP⟩ := exists_literalSourceHorizonPower_uniformJet3 α₀
  obtain ⟨M0, hM00, hM0⟩ := exists_compact_continuous_norm_bound hS _
    literalSourceHorizonPower_zero_continuous.continuousOn
  obtain ⟨M1, hM10, hM1⟩ := exists_compact_continuous_norm_bound hS _
    literalSourceHorizonPowerFirst_zero_continuous.continuousOn
  obtain ⟨M2, hM20, hM2⟩ := exists_compact_continuous_norm_bound hS _
    literalSourceHorizonPowerSecond_half_zero_continuous.continuousOn
  let M : ℝ := max (max M0 (max M1 M2)) (max ‖B₀‖ ‖B₁‖)
  have hM0le : M0 ≤ M := by
    dsimp [M]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hM1le : M1 ≤ M := by
    dsimp [M]
    exact (le_max_left M1 M2).trans
      ((le_max_right M0 (max M1 M2)).trans (le_max_left _ _))
  have hM2le : M2 ≤ M := by
    dsimp [M]
    exact (le_max_right M1 M2).trans
      ((le_max_right M0 (max M1 M2)).trans (le_max_left _ _))
  have hB0le : ‖B₀‖ ≤ M := by
    dsimp [M]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hB1le : ‖B₁‖ ≤ M := by
    dsimp [M]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hM : 0 ≤ M := hM00.trans hM0le
  have hAffine : HasUniformJet3 S (1 / 2)
      (fun (_ : ℂ) (z : ℝ) => B₀ - (z : ℂ) * B₁)
      (fun _ => B₀) (fun _ => -B₁) (fun _ => 0) 0 := by
    intro α hα z hz
    simp only [neg_mul]
    ring_nf
    norm_num
  have hprod := hP.mul (b := (1 / 2 : ℝ)) (by norm_num) hAffine hCP0 (by norm_num) hM
    (fun α hα => (hM0 α hα).trans hM0le)
    (fun α hα => (hM1 α hα).trans hM1le)
    (fun α hα => (hM2 α hα).trans hM2le)
    (fun α hα => hB0le)
    (fun α hα => by simpa only [norm_neg] using hB1le)
    (fun α hα => by simp; exact hM)
  refine ⟨3 * M ^ 2 + CP * (3 * M + 0) + 3 * M * 0, by positivity, ?_⟩
  intro α hα z hz
  have hj := literalSourceHorizonPower_zero_jets α
  have h := hprod α hα z hz
  simp only at h ⊢
  rw [hj.2.1, hj.2.2] at h
  dsimp only [literalSourceAffinePower, horizonAffinePowerCore]
  convert h using 1
  congr 1
  ring

end
end GaloisForLFunctions.HTGeometry
