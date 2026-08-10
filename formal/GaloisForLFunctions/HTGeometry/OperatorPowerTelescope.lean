import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Telescoping a difference of operator powers

For two operators `X` and `Y` on a normed space,

`X^r v - Y^r v = ∑_(i<r) Y^(r-1-i) (X - Y) (X^i v)`,

so the deviation of the powers is controlled by the deviation of the operators applied to the
*iterates of `X`*, with only powers of `‖Y‖` in front.  This is the form to use when `X` is
unbounded uniformly in a parameter but `Y` is not: the growing operator is never applied to an
error term.
-/

open Finset

namespace GaloisForLFunctions

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- **Telescoping bound for a difference of operator powers.**  Only powers of `‖Y‖` occur; `X` is
applied only to `v`. -/
theorem norm_pow_apply_sub_pow_apply_le (X Y : E →L[𝕜] E) (v : E) (r : ℕ) :
    ‖(X ^ r) v - (Y ^ r) v‖
      ≤ ∑ i ∈ Finset.range r, ‖Y‖ ^ (r - 1 - i) * ‖(X - Y) ((X ^ i) v)‖ := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hXr : (X ^ (r + 1)) v = X ((X ^ r) v) := by
        rw [pow_succ']
        rfl
      have hYr : (Y ^ (r + 1)) v = Y ((Y ^ r) v) := by
        rw [pow_succ']
        rfl
      have hsplit : X ((X ^ r) v) - Y ((Y ^ r) v)
          = Y ((X ^ r) v - (Y ^ r) v) + (X - Y) ((X ^ r) v) := by
        rw [map_sub, sub_apply]
        abel
      rw [hXr, hYr, hsplit]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖Y ((X ^ r) v - (Y ^ r) v)‖
          ≤ ‖Y‖ * ∑ i ∈ Finset.range r, ‖Y‖ ^ (r - 1 - i) * ‖(X - Y) ((X ^ i) v)‖ :=
        (Y.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg Y))
      calc ‖Y ((X ^ r) v - (Y ^ r) v)‖ + ‖(X - Y) ((X ^ r) v)‖
          ≤ ‖Y‖ * (∑ i ∈ Finset.range r, ‖Y‖ ^ (r - 1 - i) * ‖(X - Y) ((X ^ i) v)‖) +
              ‖(X - Y) ((X ^ r) v)‖ := add_le_add h1 le_rfl
        _ = (∑ i ∈ Finset.range r, ‖Y‖ ^ (r - i) * ‖(X - Y) ((X ^ i) v)‖) +
              ‖(X - Y) ((X ^ r) v)‖ := by
            rw [Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hir : i < r := Finset.mem_range.mp hi
            rw [← mul_assoc, ← pow_succ']
            congr 2
            omega
        _ = ∑ i ∈ Finset.range (r + 1), ‖Y‖ ^ (r + 1 - 1 - i) * ‖(X - Y) ((X ^ i) v)‖ := by
            rw [Finset.sum_range_succ]
            simp

end GaloisForLFunctions
