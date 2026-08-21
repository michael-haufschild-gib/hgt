import GaloisForLFunctions.HTGeometry.SeparatingGramLocus

/-!
# Positive definiteness of the period Gram matrix

Proposition 5.1 (3) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), needs the two matrices

```text
B = ( √−1 ∫_{Ỹ₀} ν*ω_i ∧ ν*\overline{ω_j} )     and     A = ( a_{ij} )
```

to be positive definite.  For `B` the reason is the general one: `B` is the Gram matrix of the
linearly independent holomorphic 1-forms `ν*ω_1, …, ν*ω_k` for the `L²` inner product, and the Gram
matrix of any linearly independent family in an inner product space is positive definite.

That general statement is proved here.  The corpus already owns the Gram *criterion*
(`det ≠ 0 ↔ LinearIndependent`); positive definiteness is the sharper fact, and it follows from the
same identity `star c ⬝ᵥ G *ᵥ c = ⟪Σ cᵢ vᵢ, Σ cⱼ vⱼ⟫`.
-/

open Matrix
open scoped ComplexOrder

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The Gram matrix is Hermitian. -/
theorem gramMatrix_isHermitian {n : ℕ} (v : Fin n → E) :
    (GaloisForLFunctions.HTGeometry.gramMatrix v).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, GaloisForLFunctions.HTGeometry.gramMatrix,
    Matrix.of_apply]
  exact inner_conj_symm _ _

/-- The Gram quadratic form is the squared norm of the corresponding combination. -/
theorem dotProduct_gramMatrix_mulVec {n : ℕ} (v : Fin n → E) (c : Fin n → ℂ) :
    star c ⬝ᵥ (GaloisForLFunctions.HTGeometry.gramMatrix v).mulVec c
      = inner ℂ (∑ i, c i • v i) (∑ j, c j • v j) := by
  rw [← GaloisForLFunctions.HTGeometry.sum_conj_mul_gramMatrix_mulVec v c]
  simp [dotProduct, Pi.star_apply, RCLike.star_def]

/-- **The Gram matrix of a linearly independent family is positive definite.**

This is the general fact behind Proposition 5.1 (3) of Dai–Yoshikawa. -/
theorem gramMatrix_posDef_of_linearIndependent {n : ℕ} {v : Fin n → E}
    (h : LinearIndependent ℂ v) :
    (GaloisForLFunctions.HTGeometry.gramMatrix v).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gramMatrix_isHermitian v) fun c hc => ?_
  have hw : (∑ i, c i • v i) ≠ 0 := by
    intro hzero
    refine hc ?_
    funext i
    exact Fintype.linearIndependent_iff.mp h c hzero i
  have hnorm : (0 : ℝ) < ‖(∑ i, c i • v i)‖ := norm_pos_iff.mpr hw
  have hre : (inner ℂ (∑ i, c i • v i) (∑ i, c i • v i) : ℂ)
      = ((‖(∑ i, c i • v i)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [dotProduct_gramMatrix_mulVec, hre]
  exact Complex.zero_lt_real.mpr (by positivity)

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
