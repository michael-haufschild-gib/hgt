import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Cosine on a symmetric arc

On the arc `[δ, 2π − δ]` the cosine is at most `cos δ`.
-/

open Real

namespace HTGeometry

theorem cos_le_cos_of_mem_arc {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (h1 : δ ≤ t) (h2 : t ≤ 2 * π - δ) : Real.cos t ≤ Real.cos δ := by
  rcases le_or_gt t π with ht | ht
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hδ0 ht h1
  · have hrefl : Real.cos t = Real.cos (2 * π - t) := by
      rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      ring
    rw [hrefl]
    refine Real.cos_le_cos_of_nonneg_of_le_pi hδ0 ?_ (by linarith)
    linarith [Real.pi_pos]

theorem cos_le_cos_of_abs_mem_arc {δ t : ℝ} (hδ0 : 0 ≤ δ)
    (h1 : δ ≤ |t|) (h2 : |t| ≤ 2 * π - δ) : Real.cos t ≤ Real.cos δ := by
  rcases abs_cases t with ⟨heq, _⟩ | ⟨heq, _⟩
  · rw [heq] at h1 h2
    exact cos_le_cos_of_mem_arc hδ0 h1 h2
  · rw [heq] at h1 h2
    rw [← Real.cos_neg t]
    exact cos_le_cos_of_mem_arc hδ0 h1 h2

end HTGeometry
