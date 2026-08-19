import GaloisForLFunctions.HTGeometry.SiegelFinitenessInputs

/-!
# The weighted isometry normal form

Stripping the unipotent factors from both sides of a congruence `A' = γᵀAγ` leaves a matrix that
carries one diagonal to the other:

`M = U γ (U')⁻¹`,  `Mᵀ D M = D'`.

The unipotent factors are bounded — `U'` by size reduction and `U⁻¹` by compactness — so bounding
`γ` is exactly bounding `M`, and `M` is constrained by `∑ₖ dₖ Mₖᵢ² = d'ᵢ`.

This isolates what Siegel's finiteness still needs: control of a weighted isometry between two
Siegel-ordered diagonals.

* `weightedIsometry_congr` : **the normal form.**
* `weightedIsometry_entry_le` : the entry constraint it satisfies.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- **The weighted isometry normal form.** -/
theorem weightedIsometry_congr {J J' : JacobiData n} {γ : Matrix (Fin n) (Fin n) ℝ}
    (hform : J'.form = γᵀ * J.form * γ) :
    (J.U * γ * (J'.U)⁻¹)ᵀ * Matrix.diagonal J.d * (J.U * γ * (J'.U)⁻¹)
      = Matrix.diagonal J'.d := by
  have hU' : IsUnit (J'.U).det := by rw [J'.det_eq_one]; exact isUnit_one
  have hmid : (J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ)
      = (J'.U)ᵀ * Matrix.diagonal J'.d * J'.U := by
    have hA : γᵀ * J.form * γ = (J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ) := by
      show γᵀ * (J.Uᵀ * Matrix.diagonal J.d * J.U) * γ = _
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have hB : J'.form = (J'.U)ᵀ * Matrix.diagonal J'.d * J'.U := rfl
    rw [← hA, ← hform, hB]
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  calc ((J'.U)ᵀ)⁻¹ * (J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ * (J'.U)⁻¹)
      = ((J'.U)ᵀ)⁻¹ * ((J.U * γ)ᵀ * Matrix.diagonal J.d * (J.U * γ)) * (J'.U)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = ((J'.U)ᵀ)⁻¹ * ((J'.U)ᵀ * Matrix.diagonal J'.d * J'.U) * (J'.U)⁻¹ := by rw [hmid]
    _ = Matrix.diagonal J'.d := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.mul_nonsing_inv _ hU', Matrix.mul_one, ← Matrix.mul_assoc,
          Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hU'), Matrix.one_mul]

/-- The entry constraint satisfied by a weighted isometry. -/
theorem weightedIsometry_entry_le {M : Matrix (Fin n) (Fin n) ℝ} {J J' : JacobiData n}
    (h : Mᵀ * Matrix.diagonal J.d * M = Matrix.diagonal J'.d) (k i : Fin n) :
    J.d k * (M k i) ^ 2 ≤ J'.d i := by
  classical
  have hmul : ∀ a b : Fin n, (Mᵀ * Matrix.diagonal J.d) a b = M b a * J.d b := by
    intro a b
    rw [Matrix.mul_apply,
      Finset.sum_eq_single b (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ hp, mul_zero])
        (fun hcon => absurd (Finset.mem_univ b) hcon),
      Matrix.transpose_apply, Matrix.diagonal_apply_eq]
  have hsum : (∑ m, J.d m * (M m i) ^ 2) = J'.d i := by
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Matrix.diagonal_apply_eq] at hii
    rw [← hii]
    exact Finset.sum_congr rfl fun m _ => by rw [hmul]; ring
  rw [← hsum]
  exact Finset.single_le_sum (f := fun m => J.d m * (M m i) ^ 2)
    (fun m _ => mul_nonneg (J.pos m).le (sq_nonneg _)) (Finset.mem_univ k)

end GaloisForLFunctions.HTGeometry
