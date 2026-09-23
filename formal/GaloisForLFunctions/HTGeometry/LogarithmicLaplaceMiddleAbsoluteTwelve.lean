import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceMiddleAbsoluteBounds
import GaloisForLFunctions.HTGeometry.LogarithmicLaplaceScoreTwelve

/-! # Absolute cooling bounds through twelve on the original middle ray -/
namespace HTGeometry
noncomputable section
private theorem absolute_score_11 {z : ℝ} (hz : 111/10 ≤ z) : |laplaceCoolingJet 11 0 z| ≤ (2*z)^(11 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  obtain ⟨t, ht0, rfl⟩ := exists_nonneg_add_of_le hz
  have hp : 0 ≤ (2*(111/10+t))^(11 : ℕ)+laplaceCoolingJet 11 0 (111/10+t) := by
    rw [laplaceCoolingJet_11]
    ring_nf
    positivity
  have hm : 0 ≤ (2*(111/10+t))^(11 : ℕ)-laplaceCoolingJet 11 0 (111/10+t) := by
    rw [laplaceCoolingJet_11]
    ring_nf
    positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem absolute_score_12 {z : ℝ} (hz : 111/10 ≤ z) : |laplaceCoolingJet 12 0 z| ≤ (2*z)^(12 : ℕ) := by
  have ht : 0 ≤ z-111/10 := by linarith
  obtain ⟨t, ht0, rfl⟩ := exists_nonneg_add_of_le hz
  have hp : 0 ≤ (2*(111/10+t))^(12 : ℕ)+laplaceCoolingJet 12 0 (111/10+t) := by
    rw [laplaceCoolingJet_12]
    ring_nf
    positivity
  have hm : 0 ≤ (2*(111/10+t))^(12 : ℕ)-laplaceCoolingJet 12 0 (111/10+t) := by
    rw [laplaceCoolingJet_12]
    ring_nf
    positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every required score has its leading-monomial absolute bound from `111/10`. -/
theorem laplaceCoolingJet_abs_le_of_middle_twelve {n : ℕ} (hn : n ≤ 12) {z : ℝ}
    (hz : 111/10 ≤ z) : |laplaceCoolingJet n 0 z| ≤ (2*z)^n := by
  by_cases h : n ≤ 10
  · exact laplaceCoolingJet_abs_le_of_middle h hz
  · have he : n = 11 ∨ n = 12 := by omega
    rcases he with rfl | rfl
    · exact absolute_score_11 hz
    · exact absolute_score_12 hz

end
end HTGeometry
