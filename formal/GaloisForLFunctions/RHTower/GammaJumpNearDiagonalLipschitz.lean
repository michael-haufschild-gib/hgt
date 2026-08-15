import GaloisForLFunctions.RHTower.GammaJumpMultiplierBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The near-diagonal symbol difference gains one full frequency

On the near-diagonal region `|ξ − η| ≤ (1+|η|)/2` the jump symbol is Lipschitz with the *frequency-
weighted* constant: every point of the segment from `η` to `ξ` still has `1 + |θ| ≥ (1+|η|)/2`, so
the derivative bound `|r'| ≤ C/(1+|η|)` holds uniformly along it, and the two frequencies are
comparable, `1 + |ξ| ≤ (3/2)(1+|η|)`.  Hence

`(1+|ξ|)|r(ξ) − r(η)| ≤ C'|ξ − η|`.

This is the near-diagonal half of the order-minus-one commutator estimate: the factor `1+|ξ|` that
an `H¹` bound demands is paid for by the symbol difference itself, leaving a kernel that the
Schwartz decay of the cutoff transform absorbs.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Every point of the segment stays comparable to the base frequency. -/
theorem one_add_abs_ge_of_mem_uIcc {ξ η θ : ℝ} (hθ : θ ∈ uIcc η ξ)
    (hnear : |ξ - η| ≤ (1 + |η|) / 2) :
    (1 + |η|) / 2 ≤ 1 + |θ| := by
  have hsub : |θ - η| ≤ |ξ - η| := by
    rcases abs_cases (ξ - η) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases mem_uIcc.mp hθ with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
      rw [abs_sub_le_iff] <;> constructor <;> [skip; skip; skip; skip; skip; skip; skip; skip] <;>
      first
        | linarith [abs_nonneg (ξ - η), le_abs_self (ξ - η), neg_abs_le (ξ - η)]
  have hlow : |η| - |ξ - η| ≤ |θ| := by
    have h1 : |η| - |θ| ≤ |η - θ| := abs_sub_abs_le_abs_sub η θ
    rw [abs_sub_comm η θ] at h1
    linarith [hsub]
  linarith

/-- **`(35)`: the weighted near-diagonal Lipschitz bound.** -/
theorem exists_bound_gammaJump_nearDiagonal :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η : ℝ, |ξ - η| ≤ (1 + |η|) / 2 →
      (1 + |ξ|) * |gammaJumpMultiplier ξ - gammaJumpMultiplier η| ≤ C * |ξ - η| := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_deriv_gammaJumpMultiplier_bound
  refine ⟨3 * C₀, by positivity, fun ξ η hnear => ?_⟩
  have hηpos : (0 : ℝ) < 1 + |η| := by positivity
  -- the uniform derivative bound on the segment
  have hderivbound : ∀ θ ∈ uIcc η ξ, ‖deriv gammaJumpMultiplier θ‖ ≤ 2 * C₀ / (1 + |η|) := by
    intro θ hθ
    have hθpos : (1 + |η|) / 2 ≤ 1 + |θ| := one_add_abs_ge_of_mem_uIcc hθ hnear
    have hθ0 : (0 : ℝ) < 1 + |θ| := by positivity
    have hd : deriv gammaJumpMultiplier θ
        = 2 * ∑' n : ℕ, 2 * θ * ((n : ℝ) + 1) / ((((n : ℝ) + 1) ^ 2 + θ ^ 2) ^ 2) :=
      (hasDerivAt_gammaJumpMultiplier θ).deriv
    rw [Real.norm_eq_abs, hd]
    refine (hbound θ).trans ?_
    rw [div_le_div_iff₀ hθ0 hηpos]
    nlinarith [hC₀, hθpos, hηpos]
  have hdiff : ∀ θ ∈ uIcc η ξ, DifferentiableAt ℝ gammaJumpMultiplier θ :=
    fun θ _ => (hasDerivAt_gammaJumpMultiplier θ).differentiableAt
  have hMVT := (convex_uIcc η ξ).norm_image_sub_le_of_norm_deriv_le hdiff hderivbound
    (left_mem_uIcc) (right_mem_uIcc)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hMVT
  -- the two frequencies are comparable
  have hcomp : 1 + |ξ| ≤ 3 / 2 * (1 + |η|) := by
    have h1 : |ξ| ≤ |η| + |ξ - η| := by
      have := abs_sub_abs_le_abs_sub ξ η
      linarith
    linarith
  calc (1 + |ξ|) * |gammaJumpMultiplier ξ - gammaJumpMultiplier η|
      ≤ (3 / 2 * (1 + |η|)) * (2 * C₀ / (1 + |η|) * |ξ - η|) := by
        refine mul_le_mul hcomp hMVT (abs_nonneg _) (by positivity)
    _ = 3 * C₀ * |ξ - η| := by
        field_simp

end GaloisForLFunctions.RHTower
