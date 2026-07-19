import GaloisForLFunctions.HTGeometry.CauchyTransformIteratedDeriv

/-!
# Uniform kernel bounds on a compact node patch

The Lipschitz estimate for the jet map carries a constant built from the kernel bound at the node,
so it is uniform in the parameter but not, on its face, in the node.  Restricting the node to a
compact set off the real axis repairs this: the distance to the axis attains a positive minimum
there, so every kernel power is bounded by a single constant over the whole patch.

This is the uniformity hypothesis of the joint-continuity principle, and it is what makes the
compact-patch Baire argument applicable.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- On a compact set avoiding the real axis the distance to the axis has a positive lower bound. -/
theorem exists_pos_le_abs_im_of_compact {K : Set ℂ} (hK : IsCompact K)
    (hKne : ∀ z ∈ K, z.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ |z.im| := by
  rcases K.eq_empty_or_nonempty with hempty | hne
  · exact ⟨1, one_pos, by simp [hempty]⟩
  · obtain ⟨z₀, hz₀K, hmin⟩ :=
      hK.exists_isMinOn hne (continuous_abs.comp Complex.continuous_im).continuousOn
    refine ⟨|z₀.im|, abs_pos.mpr (hKne z₀ hz₀K), ?_⟩
    intro z hz
    exact hmin hz

/-- **Uniform kernel bound on a compact node patch.**  Every kernel power is bounded by a single
constant over a compact set of nodes avoiding the real axis. -/
theorem exists_uniform_kernelPow_bound {K : Set ℂ} (hK : IsCompact K)
    (hKne : ∀ z ∈ K, z.im ≠ 0) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ∀ t : ℝ,
      ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖ ≤ B := by
  obtain ⟨c, hcpos, hc⟩ := exists_pos_le_abs_im_of_compact hK hKne
  refine ⟨(c⁻¹) ^ (k + 1), by positivity, ?_⟩
  intro z hz t
  refine le_trans (norm_kernelPow_le (hKne z hz) k t) ?_
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ hcpos (hc z hz)

/-- The uniform bound also dominates the kernel itself, uniformly on the patch. -/
theorem exists_uniform_kernel_bound {K : Set ℂ} (hK : IsCompact K)
    (hKne : ∀ z ∈ K, z.im ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ K, ∀ t : ℝ, ‖(((t : ℝ) : ℂ) - z)⁻¹‖ ≤ B := by
  obtain ⟨B, hBpos, hB⟩ := exists_uniform_kernelPow_bound hK hKne 0
  refine ⟨B, hBpos, ?_⟩
  intro z hz t
  simpa using hB z hz t

end

end GaloisForLFunctions.HTGeometry
