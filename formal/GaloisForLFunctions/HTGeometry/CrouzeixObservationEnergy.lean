import GaloisForLFunctions.HTGeometry.CrouzeixGramEnergy
import GaloisForLFunctions.HTGeometry.SeparatingGramLocus


/-!
# Positive-block energy for Hilbert-space observations

A joint finite Gram factorization transports the positive-block inequality from matrices to
finite vector and operator families in arbitrary complex Hilbert spaces. The factorization
retains both self-Grams and the full cross-Gram, with no independence or dimension assumptions.
-/

open Matrix
open scoped BigOperators ComplexConjugate MatrixOrder ComplexOrder Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E x y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype x] [Fintype y] [DecidableEq x] [DecidableEq y]

/-- Two finite vector families admit a joint finite matrix realization of all their inner products,
even when their ambient Hilbert space is infinite-dimensional. -/
theorem exists_joint_gram_factor (u : x → E) (v : y → E) :
    ∃ (A : Matrix (x ⊕ y) x ℂ) (B : Matrix (x ⊕ y) y ℂ),
      Aᴴ * A = Matrix.gram ℂ u ∧ Bᴴ * B = Matrix.gram ℂ v ∧
        Aᴴ * B = fun i j => inner ℂ (u i) (v j) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (Matrix.posSemidef_gram ℂ (Sum.elim u v)).nonneg
  let A : Matrix (x ⊕ y) x ℂ := fun i j => C i (Sum.inl j)
  let B : Matrix (x ⊕ y) y ℂ := fun i j => C i (Sum.inr j)
  refine ⟨A, B, ?_, ?_, ?_⟩
  · ext i j
    have he := congrArg (fun M : Matrix (x ⊕ y) (x ⊕ y) ℂ =>
      M (Sum.inl i) (Sum.inl j)) hC
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.gram_apply, Sum.elim_inl, A] using he.symm
  · ext i j
    have he := congrArg (fun M : Matrix (x ⊕ y) (x ⊕ y) ℂ =>
      M (Sum.inr i) (Sum.inr j)) hC
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.gram_apply, Sum.elim_inr, B] using he.symm
  · ext i j
    have he := congrArg (fun M : Matrix (x ⊕ y) (x ⊕ y) ℂ =>
      M (Sum.inl i) (Sum.inr j)) hC
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.gram_apply, Sum.elim_inl, Sum.elim_inr, A, B] using he.symm

/-- The positive-block bound holds for finite observations in an arbitrary complex Hilbert space. -/
theorem crouzeix_hilbert_family_energy_bound (u : x → E) (v : y → E) :
    2 * finiteMatrixHilbertSchmidtSq (fun i j => inner ℂ (u i) (v j)) ≤
      finiteMatrixHilbertSchmidtSq (Matrix.gram ℂ u) +
        finiteMatrixHilbertSchmidtSq (Matrix.gram ℂ v) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_joint_gram_factor u v
  rw [← hA, ← hB, ← hAB]
  exact crouzeix_gram_energy_bound A B

/-- Cross-energy between two finite observations is bounded by their existing separating Grams. -/
theorem crouzeix_separating_gram_energy_bound {n m : ℕ} (u : Fin n → E) (v : Fin m → E) :
    2 * finiteMatrixHilbertSchmidtSq (fun i j => inner ℂ (u i) (v j)) ≤
      finiteMatrixHilbertSchmidtSq (gramMatrix u) + finiteMatrixHilbertSchmidtSq (gramMatrix v) :=
  crouzeix_hilbert_family_energy_bound u v

/-- Two operator families can be compared at unrelated input vectors without independence or
separation assumptions. -/
theorem crouzeix_operator_observation_energy_bound {n m : ℕ}
    (A : Fin n → E →L[ℂ] E) (B : Fin m → E →L[ℂ] E) (z w : E) :
    2 * finiteMatrixHilbertSchmidtSq (fun i j => inner ℂ (A i z) (B j w)) ≤
      finiteMatrixHilbertSchmidtSq (gramMatrix fun i => A i z) +
        finiteMatrixHilbertSchmidtSq (gramMatrix fun j => B j w) :=
  crouzeix_separating_gram_energy_bound _ _

end

end GaloisForLFunctions.HTGeometry
