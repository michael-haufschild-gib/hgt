import GaloisForLFunctions.HTGeometry.SiegelWeightedIsometry

/-!
# Columns of a weighted isometry

The congruence `Mᵀ D M = D'` is not merely an inequality on entries: it is an exact identity on
columns, `∑ₖ dₖ Mₖᵢ² = d'ᵢ`, together with `D`-orthogonality of distinct columns.  When `M` is
integral, every nonzero entry of a column contributes at least the whole of its weight, so the
weights of the support of a column already sum to at most `d'ᵢ`.

That exactness is what the inequality `dₖ Mₖᵢ² ≤ d'ᵢ` loses, and it is what forces entries to
vanish: in a two-dimensional example with `d = d' = (ε, 1/ε)` the inequality permits an off-diagonal
entry as large as `1/ε`, while the identity forces it to be zero.

* `weightedIsometry_col_sq` : **the column identity.**
* `weightedIsometry_col_orth` : `D`-orthogonality of distinct columns.
* `weightedIsometry_support_sum_le` : **the weights of a column's support sum to at most `d'ᵢ`.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

theorem transpose_mul_diagonal_apply (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (a b : Fin n) : (Mᵀ * Matrix.diagonal d) a b = M b a * d b := by
  classical
  rw [Matrix.mul_apply,
    Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
      (fun hcon => absurd (Finset.mem_univ b) hcon),
    Matrix.transpose_apply, Matrix.diagonal_apply_eq]

/-- **The column identity of a weighted isometry.** -/
theorem weightedIsometry_col_sq {M : Matrix (Fin n) (Fin n) ℝ} {d d' : Fin n → ℝ}
    (h : Mᵀ * Matrix.diagonal d * M = Matrix.diagonal d') (i : Fin n) :
    (∑ k, d k * (M k i) ^ 2) = d' i := by
  classical
  have hii := congrFun (congrFun h i) i
  rw [Matrix.mul_apply, Matrix.diagonal_apply_eq] at hii
  rw [← hii]
  exact Finset.sum_congr rfl fun m _ => by rw [transpose_mul_diagonal_apply]; ring

/-- **Distinct columns of a weighted isometry are `D`-orthogonal.** -/
theorem weightedIsometry_col_orth {M : Matrix (Fin n) (Fin n) ℝ} {d d' : Fin n → ℝ}
    (h : Mᵀ * Matrix.diagonal d * M = Matrix.diagonal d') {i j : Fin n} (hij : i ≠ j) :
    (∑ k, d k * (M k i) * (M k j)) = 0 := by
  classical
  have hij' := congrFun (congrFun h i) j
  rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ hij] at hij'
  rw [← hij']
  exact Finset.sum_congr rfl fun m _ => by rw [transpose_mul_diagonal_apply]; ring

/-- **For an integral weighted isometry the weights of a column's support sum to at most `d'ᵢ`.** -/
theorem weightedIsometry_support_sum_le {M : Matrix (Fin n) (Fin n) ℝ} {J J' : JacobiData n}
    (h : Mᵀ * Matrix.diagonal J.d * M = Matrix.diagonal J'.d)
    {g : Matrix (Fin n) (Fin n) ℤ} (hg : ∀ a b, M a b = (g a b : ℝ)) (i : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => M k i ≠ 0), J.d k) ≤ J'.d i := by
  classical
  rw [← weightedIsometry_col_sq h i]
  calc (∑ k ∈ Finset.univ.filter (fun k : Fin n => M k i ≠ 0), J.d k)
      ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n => M k i ≠ 0), J.d k * (M k i) ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter] at hk
        have hsq : (1 : ℝ) ≤ (M k i) ^ 2 := one_le_sq_of_int_ne_zero (hg k i) hk.2
        nlinarith [hsq, (J.pos k).le]
    _ ≤ ∑ k, J.d k * (M k i) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => mul_nonneg (J.pos k).le (sq_nonneg _))

end GaloisForLFunctions.HTGeometry
