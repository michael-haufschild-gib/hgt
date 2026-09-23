import Mathlib

/-!
# Absolute summability of a diagonal from a Hilbert–Schmidt factorization

A trace-class operator is a product of two Hilbert–Schmidt operators, `T = S ∘ U`.  In any
orthonormal basis its diagonal is then

```text
⟪T e_i, e_i⟫ = ⟪U e_i, S† e_i⟫ ,      |⟪T e_i, e_i⟫| ≤ ‖U e_i‖ · ‖S† e_i‖ ,
```

and both factors are square-summable because `U` and `S†` are Hilbert–Schmidt.  Absolute
summability of the diagonal therefore needs nothing spectral — no Lidskii theorem and no eigenvalue
theory — only that a product of two square-summable nonnegative families is summable, which is
`ab ≤ (a² + b²)/2`.

This is the wiring the CCM source-lock composition needs: the arithmetic perturbation is trace class
in this tree, and what the secular-tail estimate consumes is summability of its diagonal.
-/

namespace GaloisForLFunctions

/-- **A product of two square-summable nonnegative families is summable.**  By `ab ≤ (a²+b²)/2`. -/
theorem summable_mul_of_summable_sq {ι : Type*} {a c : ι → ℝ}
    (hnna : ∀ i, 0 ≤ a i) (hnnc : ∀ i, 0 ≤ c i)
    (ha : Summable fun i => a i ^ (2 : ℕ)) (hc : Summable fun i => c i ^ (2 : ℕ)) :
    Summable fun i => a i * c i := by
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (hnna i) (hnnc i)) ?_
    (((ha.add hc).mul_left (1 / 2 : ℝ)))
  intro i
  have h := sq_nonneg (a i - c i)
  nlinarith [h]

/-- **Domination transfer.**  A nonnegative family dominated by such a product is summable. -/
theorem summable_of_le_mul_of_summable_sq {ι : Type*} {f a c : ι → ℝ}
    (hnnf : ∀ i, 0 ≤ f i) (hnna : ∀ i, 0 ≤ a i) (hnnc : ∀ i, 0 ≤ c i)
    (hbound : ∀ i, f i ≤ a i * c i)
    (ha : Summable fun i => a i ^ (2 : ℕ)) (hc : Summable fun i => c i ^ (2 : ℕ)) :
    Summable f :=
  Summable.of_nonneg_of_le hnnf hbound (summable_mul_of_summable_sq hnna hnnc ha hc)

/-- **The diagonal of a factored operator is absolutely summable.**  Stated with the factorization
bound as the interface, so it applies to any `T = S ∘ U` with `U` and `S†` Hilbert–Schmidt: take
`a i = ‖U e_i‖` and `c i = ‖S† e_i‖`. -/
theorem summable_diagonal_of_factors {ι : Type*} {diag a c : ι → ℝ}
    (hbound : ∀ i, |diag i| ≤ a i * c i)
    (hnna : ∀ i, 0 ≤ a i) (hnnc : ∀ i, 0 ≤ c i)
    (ha : Summable fun i => a i ^ (2 : ℕ)) (hc : Summable fun i => c i ^ (2 : ℕ)) :
    Summable fun i => |diag i| :=
  summable_of_le_mul_of_summable_sq (fun _ => abs_nonneg _) hnna hnnc hbound ha hc

/-- The signed diagonal is then summable too. -/
theorem summable_diagonal_signed {ι : Type*} {diag a c : ι → ℝ}
    (hbound : ∀ i, |diag i| ≤ a i * c i)
    (hnna : ∀ i, 0 ≤ a i) (hnnc : ∀ i, 0 ≤ c i)
    (ha : Summable fun i => a i ^ (2 : ℕ)) (hc : Summable fun i => c i ^ (2 : ℕ)) :
    Summable diag :=
  (summable_diagonal_of_factors hbound hnna hnnc ha hc).of_abs

end GaloisForLFunctions
