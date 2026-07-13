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

end GaloisForLFunctions.HTGeometry
