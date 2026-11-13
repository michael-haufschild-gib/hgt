import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic.Ring

/-!
# Stability of signed quadratic moments

The moment estimate in Li--Liu, Lemma B.3, extends from a diagonal sign
operator to every bounded operator. The error has a mixed term and a
quadratic remainder. Perturbing the operator adds its own norm error.
No positivity or selfadjointness is required.
-/

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The elementary bilinear bound keeps the operator norm explicit. -/
theorem norm_operator_pairing_le (T : E →L[𝕜] E) (x y : E) :
    ‖inner 𝕜 (T x) y‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ :=
  (norm_inner_le_norm (T x) y).trans
    (mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg y))

/-- An exact expansion separates the two mixed errors and the quadratic remainder. -/
theorem operator_quadratic_add_sub (T : E →L[𝕜] E) (v e : E) :
    inner 𝕜 (T (v + e)) (v + e) - inner 𝕜 (T v) v =
      inner 𝕜 (T v) e + inner 𝕜 (T e) v + inner 𝕜 (T e) e := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  ring

/-- The signed moment changes by at most a mixed term plus the squared perturbation. -/
theorem norm_operator_quadratic_add_sub_le (T : E →L[𝕜] E) (v e : E) :
    ‖inner 𝕜 (T (v + e)) (v + e) - inner 𝕜 (T v) v‖ ≤
      ‖T‖ * (2 * ‖v‖ * ‖e‖ + ‖e‖ ^ 2) := by
  rw [operator_quadratic_add_sub]
  calc
    _ ≤ (‖inner 𝕜 (T v) e‖ + ‖inner 𝕜 (T e) v‖) + ‖inner 𝕜 (T e) e‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖T‖ * ‖v‖ * ‖e‖ + ‖T‖ * ‖e‖ * ‖v‖) + ‖T‖ * ‖e‖ * ‖e‖ :=
      add_le_add (add_le_add (norm_operator_pairing_le T v e)
        (norm_operator_pairing_le T e v)) (norm_operator_pairing_le T e e)
    _ = _ := by ring

/-- The same estimate in terms of an exact vector and an approximation. -/
theorem norm_operator_quadratic_sub_le (T : E →L[𝕜] E) (u v : E) :
    ‖inner 𝕜 (T u) u - inner 𝕜 (T v) v‖ ≤
      ‖T‖ * (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) := by
  simpa only [← add_sub_assoc, add_sub_cancel_left] using
    norm_operator_quadratic_add_sub_le T v (u - v)

/-- Operator and testing-vector errors have separate, explicit costs. -/
theorem norm_operator_quadratic_sub_operator_le (T S : E →L[𝕜] E) (u v : E) :
    ‖inner 𝕜 (T u) u - inner 𝕜 (S v) v‖ ≤
      ‖T - S‖ * ‖u‖ ^ 2 + ‖S‖ * (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) := by
  have he : inner 𝕜 (T u) u - inner 𝕜 (S v) v =
      inner 𝕜 ((T - S) u) u + (inner 𝕜 (S u) u - inner 𝕜 (S v) v) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    ring
  rw [he]
  calc
    _ ≤ ‖inner 𝕜 ((T - S) u) u‖ + ‖inner 𝕜 (S u) u - inner 𝕜 (S v) v‖ :=
      norm_add_le _ _
    _ ≤ ‖T - S‖ * ‖u‖ * ‖u‖ + ‖S‖ * (2 * ‖v‖ * ‖u - v‖ + ‖u - v‖ ^ 2) :=
      add_le_add (norm_operator_pairing_le (T - S) u u)
        (norm_operator_quadratic_sub_le S u v)
    _ = _ := by ring

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
