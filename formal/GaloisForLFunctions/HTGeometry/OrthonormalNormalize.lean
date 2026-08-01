import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Normalizing a pairwise orthogonal family

A family of nonzero pairwise orthogonal vectors becomes orthonormal on dividing each member by its
norm: scaling changes an inner product by a scalar, so orthogonality survives, and the diagonal
becomes one by construction.

This is the step between "the packets sit on disjoint annuli" and "the packets are an orthonormal
family", which is what mode counting consumes.
-/

noncomputable section

namespace RHTower

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Normalization.**  A nonzero pairwise orthogonal family is orthonormal after dividing by
norms. -/
theorem orthonormal_normalize {ι : Type*} {v : ι → E} (hne : ∀ i, v i ≠ 0)
    (horth : ∀ i j, i ≠ j → (inner 𝕜 (v i) (v j)) = 0) :
    Orthonormal 𝕜 fun i => ((‖v i‖ : 𝕜))⁻¹ • v i := by
  constructor
  · intro i
    have hpos : (0 : ℝ) < ‖v i‖ := norm_pos_iff.mpr (hne i)
    rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hpos,
      inv_mul_cancel₀ hpos.ne']
  · intro i j hij
    rw [inner_smul_left, inner_smul_right, horth i j hij, mul_zero, mul_zero]

end RHTower
