import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform small budgets after normalization

A cost with an arbitrarily small comparison-scale coefficient vanishes after
normalization whenever that scale stays bounded relative to escaping energy.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- Uniform little-oh budgets vanish whenever the comparison scale stays bounded relative to escaping energy. -/
theorem normalized_cost_tendsto_zero_of_uniform_small_budget
    (F : ℕ → ℕ → ℝ) (S E : ℕ → ℝ)
    (hF : ∀ k T, 0 ≤ F k T)
    (hbudget : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, ∀ k T, F k T ≤ δ * S k + B)
    (hE : Tendsto E atTop atTop) (k : ℕ → ℕ)
    (hk : ∃ C : ℝ, ∀ᶠ T : ℕ in atTop, S (k T) / E T ≤ C) :
    Tendsto (fun T => F (k T) T / E T) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hk
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  have hCp : 0 < |C| + 1 := by positivity
  obtain ⟨B, hB⟩ := hbudget (η / (2 * (|C| + 1))) (by positivity)
  have hsmall : ∀ᶠ T : ℕ in atTop, B / E T < η / 2 :=
    (tendsto_const_nhds.div_atTop hE).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hC, hsmall, hE.eventually_ge_atTop 1] with T hCT hBT hET
  have hEpos : 0 < E T := by linarith only [hET]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (hF (k T) T) hEpos.le)]
  calc
    _ ≤ (η / (2 * (|C| + 1))) * (S (k T) / E T) + B / E T := by
      have h := div_le_div_of_nonneg_right (hB (k T) T) hEpos.le
      simpa only [add_div, mul_div_assoc] using h
    _ ≤ (η / (2 * (|C| + 1))) * (|C| + 1) + B / E T := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (hCT.trans (by linarith only [le_abs_self C])) (by positivity)) le_rfl
    _ < η := by
      have heq : (η / (2 * (|C| + 1))) * (|C| + 1) = η / 2 := by field_simp
      rw [heq]
      linarith only [hBT]

end GaloisForLFunctions.HTGeometry
