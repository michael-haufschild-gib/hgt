import Mathlib.Analysis.Complex.Basic

/-!
# Nested balls under signed reciprocal inversion

The map `z ↦ -z⁻¹` is an involutive homeomorphism of the punctured complex plane.  This file
packages the two local inclusions needed to compare determinant zeros with operator spectrum.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Metric

/-- Around a nonzero point and its signed reciprocal, choose nested balls which map into one
another in both directions. -/
theorem exists_nested_balls_signed_reciprocal {z₀ mu₀ : ℂ} (hz₀ : z₀ ≠ 0)
    (hmu₀ : mu₀ = -z₀⁻¹) {A delta : ℝ} (hA : 0 < A) (hdelta : 0 < delta) :
    ∃ r a : ℝ, 0 < r ∧ r < delta ∧ 0 < a ∧ a < A ∧
      (∀ z ∈ ball z₀ r, -z⁻¹ ∈ ball mu₀ A) ∧
      (∀ mu ∈ ball mu₀ a, -mu⁻¹ ∈ ball z₀ r) := by
  let phi : ℂ → ℂ := fun z => -z⁻¹
  have hphi_z₀ : phi z₀ = mu₀ := by simp [phi, hmu₀]
  have hmu₀0 : mu₀ ≠ 0 := by
    rw [hmu₀]
    exact neg_ne_zero.mpr (inv_ne_zero hz₀)
  have hphi_mu₀ : phi mu₀ = z₀ := by
    simp [phi, hmu₀]
  have hz_cont : ContinuousAt phi z₀ := (continuousAt_inv₀ hz₀).neg
  have hmu_cont : ContinuousAt phi mu₀ := (continuousAt_inv₀ hmu₀0).neg
  have hz_event : ∀ᶠ z in nhds z₀, phi z ∈ ball mu₀ A := by
    rw [← hphi_z₀]
    exact hz_cont.tendsto (ball_mem_nhds _ hA)
  obtain ⟨r₀, hr₀, hz_ball⟩ := Metric.eventually_nhds_iff.mp hz_event
  let r : ℝ := min (r₀ / 2) (delta / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrdelta : r < delta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hmu_event : ∀ᶠ mu in nhds mu₀, phi mu ∈ ball z₀ r := by
    rw [← hphi_mu₀]
    exact hmu_cont.tendsto (ball_mem_nhds _ hr)
  obtain ⟨a₀, ha₀, hmu_ball⟩ := Metric.eventually_nhds_iff.mp hmu_event
  let a : ℝ := min (a₀ / 2) (A / 2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haA : a < A := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨r, a, hr, hrdelta, ha, haA, ?_, ?_⟩
  · intro z hz
    apply hz_ball
    have hzdist := mem_ball.mp hz
    calc
      dist z z₀ < r := hzdist
      _ ≤ r₀ / 2 := min_le_left _ _
      _ < r₀ := by linarith
  · intro mu hmu
    apply hmu_ball
    have hmudist := mem_ball.mp hmu
    calc
      dist mu mu₀ < a := hmudist
      _ ≤ a₀ / 2 := min_le_left _ _
      _ < a₀ := by linarith

end GaloisForLFunctions.HTGeometry
