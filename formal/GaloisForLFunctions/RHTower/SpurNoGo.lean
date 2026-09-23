/-
Doc 28 §4 (task #143): the two-cluster no-go, machine-checked instance.

The tempting general count theorem — "(D−τ)(D−τ̄) applied to a hyperbolic polynomial has
at most one non-real conjugate pair" — is FALSE. Witness: `A = (X(X−100))²` (hyperbolic,
real roots 0, 0, 100, 100) and `τ = i`, so the operator is `D² + 1`:
`A″ + A` is strictly positive on all of ℝ — NO real zeros — while `deg = 4`, so all four
zeros are non-real: two conjugate pairs, winding 2. Hence the one-sided single-window
shape of the recentered carriers is a NECESSARY hypothesis of (SPUR-R).
-/
import Mathlib

namespace RHTower

open Polynomial

/-- The two-cluster witness: `A = (X(X−100))²`. -/
noncomputable def twoCluster : ℝ[X] := (X * (X - 100)) ^ (2 : ℕ)

theorem twoCluster_expand :
    twoCluster = X ^ (4 : ℕ) - 200 * X ^ (3 : ℕ) + 10000 * X ^ (2 : ℕ) := by
  rw [twoCluster]
  ring

theorem twoCluster_operator_expand :
    derivative (derivative twoCluster) + twoCluster
      = X ^ (4 : ℕ) - 200 * X ^ (3 : ℕ) + 10012 * X ^ (2 : ℕ) - 1200 * X + 20000 := by
  rw [twoCluster_expand]
  simp only [derivative_sub, derivative_add, derivative_mul, derivative_X_pow,
    derivative_ofNat, zero_mul, zero_add, Nat.cast_ofNat, map_ofNat]
  norm_num
  simp only [show (C (3 : ℝ) : ℝ[X]) = 3 from map_ofNat C 3,
    show (C (2 : ℝ) : ℝ[X]) = 2 from map_ofNat C 2]
  ring

/-- **The no-go (doc 28 §4)**: `(D² + 1)` applied to the hyperbolic `(X(X−100))²` is
strictly positive on ℝ — the operator output has no real zeros at all, so its four
zeros form two non-real conjugate pairs. -/
theorem twoCluster_operator_pos (y : ℝ) :
    0 < eval y (derivative (derivative twoCluster) + twoCluster) := by
  have hval : eval y (derivative (derivative twoCluster) + twoCluster)
      = y ^ (4 : ℕ) - 200 * y ^ (3 : ℕ) + 10012 * y ^ (2 : ℕ) - 1200 * y + 20000 := by
    rw [twoCluster_operator_expand]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat]
  rw [hval]
  nlinarith [sq_nonneg (y * (y - 100)), sq_nonneg (y - 50), sq_nonneg ((y - 50) ^ (2 : ℕ) - 2450),
    sq_nonneg (y ^ (2 : ℕ) - 100 * y + 50), sq_nonneg (y * (y - 100) + 50)]

/-- The witness is genuinely a two-pair configuration: the operator output has degree 4
and no real roots. -/
theorem twoCluster_operator_no_real_root :
    (derivative (derivative twoCluster) + twoCluster).natDegree = 4 ∧
      ∀ y : ℝ, eval y (derivative (derivative twoCluster) + twoCluster) ≠ 0 := by
  refine ⟨?_, fun y => ne_of_gt (twoCluster_operator_pos y)⟩
  rw [twoCluster_operator_expand]
  compute_degree!

end RHTower
