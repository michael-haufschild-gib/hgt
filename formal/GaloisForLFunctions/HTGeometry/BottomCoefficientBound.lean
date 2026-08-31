import GaloisForLFunctions.HTGeometry.PointwiseDerivativeBound

/-!
# The dual pointwise bound

Reading the relation `∑ C_k(F)(F′)^k = 0` from the bottom instead of the top gives

```text
‖C_0(F z)‖ ≤ (∑_{k ≥ 1} ‖C_k(F z)‖) · ‖F′ z‖^m       whenever ‖F′ z‖ ≥ 1,
```

a *lower* bound on the derivative once the coefficient magnitudes are compared.  Like the upper
bound it involves no branch choice: the bottom term is compared against all the others at once.

Together the two pointwise bounds sandwich `‖F′‖` between fixed powers of `‖F‖`, and at a
Wiman–Valiron radius they sandwich `ν(r)/r` between fixed powers of the maximum modulus.  When the
lower exponent exceeds one the growth wall applies; when the upper exponent is at most one the
central index is `O(r)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The dual pointwise bound.**  Where `‖F′ z‖ ≥ 1`, the bottom coefficient of the relation is
dominated by the others times `‖F′ z‖^m`: a *lower* bound on the derivative in terms of the
coefficients, again with no branch choice. -/
theorem norm_bottom_le_of_relation {m : ℕ} {C : ℕ → Polynomial ℂ} {F : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (F z) * (deriv F z) ^ k = 0)
    {z : ℂ} (hw : 1 ≤ ‖deriv F z‖) :
    ‖(C 0).eval (F z)‖
      ≤ (∑ k ∈ Finset.range m, ‖(C (k + 1)).eval (F z)‖) * ‖deriv F z‖ ^ m := by
  classical
  have hsplit : (C 0).eval (F z)
      = -∑ k ∈ Finset.range m, (C (k + 1)).eval (F z) * (deriv F z) ^ (k + 1) := by
    have h := hrel z
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one] at h
    linear_combination h
  rw [hsplit, norm_neg]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine pow_le_pow_right₀ hw ?_
  have := Finset.mem_range.mp hk
  omega

end GaloisForLFunctions.HTGeometry
