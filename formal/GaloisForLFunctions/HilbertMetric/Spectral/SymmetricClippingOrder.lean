import GaloisForLFunctions.HilbertMetric.Spectral.SymmetricClippingInertia

/-!
# Sign rigidity of bounded spectral regularization

At positive cutoff, symmetric clipping preserves positive and negative
semidefiniteness in both directions. Bounded regularization cannot repair
an indefinite matrix by reducing large eigenvalue magnitudes.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.SymmetricClipping
open HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem negIndex_zero_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    hermNegIndex A = 0 ↔ A.PosSemidef := by
  classical
  rw [negIndex_eq_card_neg_eigenvalues hA, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff, hA.posSemidef_iff_eigenvalues_nonneg]
  simp only [Finset.mem_univ, forall_const, not_lt, Pi.le_def, Pi.zero_apply]

/-- Positive semidefiniteness is unchanged by any positive symmetric cutoff. -/
theorem matrix_posSemidef_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) : (matrix hA c).PosSemidef ↔ A.PosSemidef := by
  rw [← negIndex_zero_iff (matrix_hermitian hA c), (matrix_inertia hA c hc).2.1,
    negIndex_zero_iff hA]

/-- Negative semidefiniteness is unchanged as well. -/
theorem matrix_neg_posSemidef_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (c : ℝ≥0) (hc : 0 < c) : (-(matrix hA c)).PosSemidef ↔ (-A).PosSemidef := by
  rw [← negIndex_zero_iff (matrix_hermitian hA c).neg, ← negIndex_zero_iff hA.neg]
  simp only [hermNegIndex, neg_neg]
  rw [(matrix_inertia hA c hc).1]

#print axioms matrix_posSemidef_iff
#print axioms matrix_neg_posSemidef_iff

end
end GaloisForLFunctions.HilbertMetric.SymmetricClipping
