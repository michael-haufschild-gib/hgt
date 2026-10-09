import GaloisForLFunctions.HTGeometry.QKrawtchoukJacobiRealization
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# Finite inverse-q Hermite spectral transforms

The quasi-orthogonal quadrature rules supply actual finite spectral models
for the Jacobi approximants in arXiv:2609.24149. Enumerating their nodes in
increasing order gives a square matrix with entries `√wⱼ Pᵢ(ξⱼ)`.
Quadrature exactness proves that this matrix is orthogonal. Positivity and
the exact number of nodes follow from the concrete inverse-q Hermite moment
form; neither is an input premise.
-/

noncomputable section
open scoped BigOperators Matrix

namespace HTGeometry

/-- Increasing enumeration of the actual quadrature nodes. -/
def inverseQHermiteQuadratureNode (t u : ℝ) (n : ℕ) (τ : ℝ) : Fin (n + 1) ↪o ℝ :=
  (quasiNodes (inverseQHermiteMoment t u) n τ).orderEmbOfFin
    (quasiNodes_card (inverseQHermiteMoment_positive t u) n τ)

/-- Positive spectral weight at an enumerated node. -/
def inverseQHermiteQuadratureWeight (t u : ℝ) (n : ℕ) (τ : ℝ) (j : Fin (n + 1)) : ℝ :=
  quasiWeight (inverseQHermiteMoment t u) n τ (inverseQHermiteQuadratureNode t u n τ j)

theorem inverseQHermiteQuadratureWeight_pos (t u : ℝ) (n : ℕ) (τ : ℝ)
    (j : Fin (n + 1)) : 0 < inverseQHermiteQuadratureWeight t u n τ j :=
  quasiWeight_pos (inverseQHermiteMoment_positive t u) n τ
    (Finset.orderEmbOfFin_mem _ _ j)

/-- The weighted polynomial transform of the actual finite quadrature rule. -/
def inverseQHermiteQuadratureMatrix (t u : ℝ) (n : ℕ) (τ : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun i j =>
  Real.sqrt (inverseQHermiteQuadratureWeight t u n τ j) *
    (orthonormalPoly (inverseQHermiteMoment t u) i).eval
      (inverseQHermiteQuadratureNode t u n τ j)

private theorem sum_nodes (t u : ℝ) (n : ℕ) (τ : ℝ) (f : ℝ → ℝ) :
    (∑ j : Fin (n + 1), f (inverseQHermiteQuadratureNode t u n τ j)) =
      ∑ y ∈ quasiNodes (inverseQHermiteMoment t u) n τ, f y := by
  have hsum := Finset.sum_map Finset.univ
    ((quasiNodes (inverseQHermiteMoment t u) n τ).orderEmbOfFin
      (quasiNodes_card (inverseQHermiteMoment_positive t u) n τ)).toEmbedding f
  rw [Finset.map_orderEmbOfFin_univ] at hsum
  exact hsum.symm

private theorem quadrature_polynomial_product (t u : ℝ) (n : ℕ) (τ : ℝ)
    (i k : Fin (n + 1)) :
    (∑ y ∈ quasiNodes (inverseQHermiteMoment t u) n τ,
      quasiWeight (inverseQHermiteMoment t u) n τ y *
        ((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
          (orthonormalPoly (inverseQHermiteMoment t u) k).eval y)) =
      if i = k then 1 else 0 := by
  let h := inverseQHermiteMoment_positive t u
  have hdeg : ((orthonormalPoly (inverseQHermiteMoment t u) i) *
      (orthonormalPoly (inverseQHermiteMoment t u) k)).degree ≤
      ((2 * n : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, orthonormalPoly_degree h, orthonormalPoly_degree h]
    exact_mod_cast (show (i : ℕ) + (k : ℕ) ≤ 2 * n by omega)
  have heq := momentFunctional_eq_quasiSum h n τ
    ((orthonormalPoly (inverseQHermiteMoment t u) i) *
      (orthonormalPoly (inverseQHermiteMoment t u) k)) hdeg
  rw [← momentInner_def, orthonormalPoly_inner h] at heq
  simpa only [Polynomial.eval_mul, Fin.val_inj] using heq.symm

/-- Exact finite orthogonality of the weighted polynomial rows. -/
theorem inverseQHermiteQuadratureMatrix_mul_transpose (t u : ℝ) (n : ℕ) (τ : ℝ) :
    inverseQHermiteQuadratureMatrix t u n τ *
      (inverseQHermiteQuadratureMatrix t u n τ)ᵀ = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, inverseQHermiteQuadratureMatrix]
  trans ∑ j : Fin (n + 1), inverseQHermiteQuadratureWeight t u n τ j *
    ((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ j) *
      (orthonormalPoly (inverseQHermiteMoment t u) k).eval (inverseQHermiteQuadratureNode t u n τ j))
  · apply Finset.sum_congr rfl
    intro j _
    have hs := Real.sq_sqrt (inverseQHermiteQuadratureWeight_pos t u n τ j).le
    calc
      _ = Real.sqrt (inverseQHermiteQuadratureWeight t u n τ j) ^ 2 *
          ((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ j) *
            (orthonormalPoly (inverseQHermiteMoment t u) k).eval (inverseQHermiteQuadratureNode t u n τ j)) := by ring
      _ = _ := by rw [hs]
  · change (∑ j : Fin (n + 1), quasiWeight (inverseQHermiteMoment t u) n τ
      (inverseQHermiteQuadratureNode t u n τ j) *
        ((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ j) *
          (orthonormalPoly (inverseQHermiteMoment t u) k).eval (inverseQHermiteQuadratureNode t u n τ j))) = _
    rw [sum_nodes t u n τ (fun y => quasiWeight (inverseQHermiteMoment t u) n τ y *
      ((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
        (orthonormalPoly (inverseQHermiteMoment t u) k).eval y))]
    exact quadrature_polynomial_product t u n τ i k

/-- The spectral columns are orthogonal as well: the finite transform is onto. -/
theorem inverseQHermiteQuadratureMatrix_transpose_mul (t u : ℝ) (n : ℕ) (τ : ℝ) :
    (inverseQHermiteQuadratureMatrix t u n τ)ᵀ *
      inverseQHermiteQuadratureMatrix t u n τ = 1 :=
  mul_eq_one_comm.mp (inverseQHermiteQuadratureMatrix_mul_transpose t u n τ)

end HTGeometry
