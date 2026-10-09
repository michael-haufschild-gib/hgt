import GaloisForLFunctions.HTGeometry.QKrawtchoukFiniteOrthogonalTransform
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Finite quadrature operators on the common sequence space

The columns of the actual quadrature transform become orthonormal vectors
in ℓ². They span exactly the first `n+1` coordinate vectors. Multiplying
these spectral vectors by their real quadrature nodes gives an actual
finite-rank self-adjoint operator, extended by zero on the remaining space.
This supplies finite operators on the same Hilbert space as the selected
infinite Jacobi operator from arXiv:2609.24149.
-/

noncomputable section
open scoped BigOperators Matrix LinearPMap ComplexConjugate

namespace HTGeometry

private theorem coordinate_orthonormal (n : ℕ) :
    Orthonormal ℂ (fun i : Fin (n + 1) =>
      (lp.single 2 (i : ℕ) (1 : ℂ) : lp (fun _ : ℕ => ℂ) 2)) := by
  rw [orthonormal_iff_ite]
  intro i k
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply, RCLike.inner_apply,
    Fin.val_inj]

private theorem column_gram (t u : ℝ) (n : ℕ) (τ : ℝ) (j k : Fin (n + 1)) :
    (∑ i : Fin (n + 1), (inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) *
      (inverseQHermiteQuadratureMatrix t u n τ i k : ℂ)) = if j = k then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M j k)
    (inverseQHermiteQuadratureMatrix_transpose_mul t u n τ)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  by_cases hjk : j = k <;> simpa only [hjk, if_true, if_false,
    Complex.ofReal_one, Complex.ofReal_zero] using hc

private theorem row_gram (t u : ℝ) (n : ℕ) (τ : ℝ) (i k : Fin (n + 1)) :
    (∑ j : Fin (n + 1), (inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) *
      (inverseQHermiteQuadratureMatrix t u n τ k j : ℂ)) = if i = k then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => M i k)
    (inverseQHermiteQuadratureMatrix_mul_transpose t u n τ)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
  have hc := congrArg Complex.ofReal h
  push_cast at hc
  by_cases hik : i = k <;> simpa only [hik, if_true, if_false,
    Complex.ofReal_one, Complex.ofReal_zero] using hc

/-- The actual finite spectral vectors, embedded in the common ℓ² space. -/
def inverseQHermiteFiniteVector (t u : ℝ) (n : ℕ) (τ : ℝ) (j : Fin (n + 1)) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ∑ i : Fin (n + 1), (inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) •
    lp.single 2 (i : ℕ) (1 : ℂ)

/-- The finite spectral vectors have exactly the weighted polynomial coordinates. -/
theorem inverseQHermiteFiniteVector_coordinate_inner (t u : ℝ) (n : ℕ) (τ : ℝ)
    (i j : Fin (n + 1)) :
    inner ℂ (lp.single 2 (i : ℕ) (1 : ℂ)) (inverseQHermiteFiniteVector t u n τ j) =
      (inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) :=
  (coordinate_orthonormal n).inner_right_fintype _ i

/-- The finite spectral vectors are orthonormal in the same space as the limit. -/
theorem inverseQHermiteFiniteVector_orthonormal (t u : ℝ) (n : ℕ) (τ : ℝ) :
    Orthonormal ℂ (inverseQHermiteFiniteVector t u n τ) := by
  rw [orthonormal_iff_ite]
  intro j k
  unfold inverseQHermiteFiniteVector
  rw [(coordinate_orthonormal n).inner_sum]
  simp only [Complex.conj_ofReal]
  exact column_gram t u n τ j k

/-- Every vector in the finite coordinate block has its exact spectral expansion. -/
theorem inverseQHermiteFiniteVector_reconstruct (t u : ℝ) (n : ℕ) (τ : ℝ)
    (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), (inverseQHermiteQuadratureMatrix t u n τ i j : ℂ) •
      inverseQHermiteFiniteVector t u n τ j) = lp.single 2 (i : ℕ) (1 : ℂ) := by
  unfold inverseQHermiteFiniteVector
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, row_gram]
  simp

/-- The finite spectral operator, zero on the complementary coordinate tail. -/
def inverseQHermiteFiniteJacobiCLM (t u : ℝ) (n : ℕ) (τ : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  ∑ j : Fin (n + 1), (inverseQHermiteQuadratureNode t u n τ j : ℂ) •
    InnerProductSpace.rankOne ℂ (inverseQHermiteFiniteVector t u n τ j)
      (inverseQHermiteFiniteVector t u n τ j)

private theorem finiteJacobiCLM_selfAdjoint (t u : ℝ) (n : ℕ) (τ : ℝ) :
    IsSelfAdjoint (inverseQHermiteFiniteJacobiCLM t u n τ) := by
  apply isSelfAdjoint_sum
  intro j _
  have hc : IsSelfAdjoint (inverseQHermiteQuadratureNode t u n τ j : ℂ) :=
    Complex.conj_ofReal _
  apply hc.smul
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact InnerProductSpace.adjoint_rankOne _ _

/-- The eigenvalues are precisely the actual finite quadrature nodes. -/
theorem inverseQHermiteFiniteJacobiCLM_eigenvector (t u : ℝ) (n : ℕ) (τ : ℝ)
    (j : Fin (n + 1)) :
    inverseQHermiteFiniteJacobiCLM t u n τ (inverseQHermiteFiniteVector t u n τ j) =
      (inverseQHermiteQuadratureNode t u n τ j : ℂ) • inverseQHermiteFiniteVector t u n τ j := by
  rw [inverseQHermiteFiniteJacobiCLM, sum_apply]
  change (∑ k : Fin (n + 1), (inverseQHermiteQuadratureNode t u n τ k : ℂ) •
    (inner ℂ (inverseQHermiteFiniteVector t u n τ k) (inverseQHermiteFiniteVector t u n τ j) •
      inverseQHermiteFiniteVector t u n τ k)) = _
  simp [orthonormal_iff_ite.mp (inverseQHermiteFiniteVector_orthonormal t u n τ)]

/-- The same finite operator as a partial linear map with full domain. -/
def inverseQHermiteFiniteJacobi (t u : ℝ) (n : ℕ) (τ : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →ₗ.[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (inverseQHermiteFiniteJacobiCLM t u n τ).toPMap ⊤

/-- The finite operators and the selected infinite operator are self-adjoint
partial maps on exactly the same Hilbert space. -/
theorem inverseQHermiteFiniteJacobi_isSelfAdjoint (t u : ℝ) (n : ℕ) (τ : ℝ) :
    IsSelfAdjoint (inverseQHermiteFiniteJacobi t u n τ) := by
  rw [LinearPMap.isSelfAdjoint_def]
  change ((inverseQHermiteFiniteJacobiCLM t u n τ).toPMap ⊤).adjoint = _
  rw [(inverseQHermiteFiniteJacobiCLM t u n τ).toPMap_adjoint_eq_adjoint_toPMap_of_dense (by simp)]
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp (finiteJacobiCLM_selfAdjoint t u n τ)]
  rfl

end HTGeometry
