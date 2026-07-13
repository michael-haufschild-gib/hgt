import Mathlib

/-!
# Gram–Schmidt norms and the Gram determinant (toward the Szegő determinant ratio)

Foundational identities relating the Gram–Schmidt vectors to distances, used to express the
consecutive Toeplitz/Gram determinant ratio `det Gₙ₊₁ / det Gₙ` as the squared distance
`dist²(vₙ₊₁, span{v₀,…,vₙ})` — the monic-orthogonal-polynomial norm at the heart of the first
Szegő limit theorem.

`gramSchmidt_inner_left_self` — `⟪gsᵢ, vᵢ⟫ = ⟪gsᵢ, gsᵢ⟫` (the Gram–Schmidt vector is orthogonal
to the correction terms, so its inner product with the original vector is its own squared length,
the increment in the Gram determinant recursion).
-/

open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The `i`-th Gram–Schmidt vector is orthogonal to the lower correction terms, so its inner
product with the original vector `vᵢ` equals its own squared length. -/
theorem gramSchmidt_inner_left_self {n : ℕ} (v : Fin n → E) (i : Fin n) :
    ⟪gramSchmidt ℂ v i, v i⟫_ℂ = ⟪gramSchmidt ℂ v i, gramSchmidt ℂ v i⟫_ℂ := by
  conv_lhs => rw [gramSchmidt_def'' ℂ v i]
  rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
  intro j hj
  have hij : i ≠ j := ((Finset.mem_Iio.mp hj).ne).symm
  rw [inner_smul_right, gramSchmidt_orthogonal ℂ v hij, mul_zero]

open Submodule in
/-- A later Gram–Schmidt vector is orthogonal to an earlier original vector: `⟪gsⱼ, vᵢ⟫ = 0` for
`i < j`.  Since `vᵢ ∈ span{gs₀,…,gsᵢ}` and `gsⱼ` is orthogonal to that span, the change-of-basis
matrix `⟪gsⱼ, vᵢ⟫/‖gsⱼ‖²` is lower-triangular; with unit diagonal (`gramSchmidt_inner_left_self`)
its determinant is `1`. -/
theorem inner_gramSchmidt_left_eq_zero_of_lt {n : ℕ} (v : Fin n → E) {i j : Fin n} (hij : i < j) :
    ⟪gramSchmidt ℂ v j, v i⟫_ℂ = 0 := by
  refine Submodule.inner_left_of_mem_orthogonal (mem_span_gramSchmidt ℂ v (le_refl i)) ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have hkj : k ≠ j := (lt_of_le_of_lt (Set.mem_Iic.mp hk) hij).ne
    exact gramSchmidt_orthogonal ℂ v hkj
  | zero => rw [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **Change of basis to the Gram–Schmidt vectors.**  Each original vector expands as
`vᵢ = ∑ⱼ (⟪gsⱼ, vᵢ⟫/‖gsⱼ‖²) • gsⱼ`.  The coefficient matrix is lower-triangular with unit diagonal,
so its determinant is `1`; this is the transition making `det(gram v) = ∏‖gsⱼ‖²`. -/
theorem eq_sum_gramSchmidt {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) (i : Fin n) :
    v i = ∑ j, (⟪gramSchmidt ℂ v j, v i⟫_ℂ / (‖gramSchmidt ℂ v j‖ : ℂ) ^ 2) • gramSchmidt ℂ v j := by
  have hzero : ∀ j ∈ Finset.univ, j ∉ Finset.Iic i →
      (⟪gramSchmidt ℂ v j, v i⟫_ℂ / (‖gramSchmidt ℂ v j‖ : ℂ) ^ 2) • gramSchmidt ℂ v j = 0 := by
    intro j _ hj
    have hij : i < j := by simpa [Finset.mem_Iic] using hj
    rw [inner_gramSchmidt_left_eq_zero_of_lt v hij, zero_div, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic i)) hzero,
    ← Finset.add_sum_Iio_eq_sum_Iic i]
  have hcoef : ⟪gramSchmidt ℂ v i, v i⟫_ℂ / (‖gramSchmidt ℂ v i‖ : ℂ) ^ 2 = 1 := by
    rw [gramSchmidt_inner_left_self]
    have h : ⟪gramSchmidt ℂ v i, gramSchmidt ℂ v i⟫_ℂ = ((‖gramSchmidt ℂ v i‖ ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [inner_self_eq_norm_sq, inner_self_im]
    rw [h, ← Complex.ofReal_pow, div_self]
    exact Complex.ofReal_ne_zero.mpr
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)))
  rw [hcoef, one_smul]
  exact gramSchmidt_def'' ℂ v i

open Matrix in
/-- **Gram entry via Gram–Schmidt.**  The Gram inner product `⟪vᵢ, vⱼ⟫` expands over the
orthogonal Gram–Schmidt vectors as `∑ₖ conj(Bᵢₖ) Bⱼₖ ‖gsₖ‖²`, with `Bᵢₖ = ⟪gsₖ, vᵢ⟫/‖gsₖ‖²`.
This is the entrywise form of the factorization `gram v = (conj B) · diag ‖gs‖² · Bᵀ`, whose
determinant (with `det B = 1`, since `B` is lower-triangular with unit diagonal) is `∏ₖ ‖gsₖ‖²`. -/
theorem gram_entry_eq {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) (i j : Fin n) :
    ⟪v i, v j⟫_ℂ = ∑ k, (starRingEnd ℂ) (⟪gramSchmidt ℂ v k, v i⟫_ℂ / (‖gramSchmidt ℂ v k‖ : ℂ) ^ 2)
      * (⟪gramSchmidt ℂ v k, v j⟫_ℂ / (‖gramSchmidt ℂ v k‖ : ℂ) ^ 2)
      * ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v k⟫_ℂ := by
  conv_lhs => rw [eq_sum_gramSchmidt v hv i, eq_sum_gramSchmidt v hv j]
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_left, inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right]; ring
  · intro l _ hlk
    rw [inner_smul_right, gramSchmidt_orthogonal ℂ v (Ne.symm hlk), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

end GaloisForLFunctions.HTGeometry
