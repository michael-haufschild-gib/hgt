import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The right half-plane is σ-compact

The sets `{z : 1/(n+1) ≤ Re z, ‖z‖ ≤ n+1}` are closed and bounded, hence compact, and their union
is `{Re z > 0}`.  Both conditions are eventually satisfied by any point of the half-plane, the first
because `Re z > 0` and the second because `z` is a fixed point.

σ-compactness is the instance a compact exhaustion needs, and it is not inferred automatically for a
subtype of `ℂ`.

* `HTGeometry.isSigmaCompact_rightHalfPlane`.
-/

open Metric

namespace HTGeometry

/-- **The right half-plane is σ-compact.** -/
theorem isSigmaCompact_rightHalfPlane : IsSigmaCompact {z : ℂ | 0 < z.re} := by
  refine ⟨fun n : ℕ => {z : ℂ | 1 / ((n : ℝ) + 1) ≤ z.re ∧ ‖z‖ ≤ (n : ℝ) + 1}, ?_, ?_⟩
  · intro n
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) ?_ ?_
    · exact (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      rw [mem_closedBall_zero_iff]
      exact hz.2
  · ext z
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, -⟩
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hz
      obtain ⟨n₁, hn₁⟩ := exists_nat_gt (1 / z.re)
      obtain ⟨n₂, hn₂⟩ := exists_nat_gt ‖z‖
      refine ⟨max n₁ n₂, ?_, ?_⟩
      · have hle : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_left n₁ n₂
        have hlt : 1 / z.re < ((max n₁ n₂ : ℕ) : ℝ) + 1 := by linarith
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hz] at hlt
        linarith
      · have hle : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_max_right n₁ n₂
        linarith

end HTGeometry
