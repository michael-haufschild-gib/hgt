import GaloisForLFunctions.HTGeometry.ExpandedMatrixDistinctNodes
import GaloisForLFunctions.HTGeometry.AffineReachabilityGenericity

/-!
# Genericity of full expanded rank in a reachable jet family

With the nodes held fixed, the determinant of the expanded evaluation matrix is a polynomial in the
jet coordinates alone.  Choosing the nodes supplied by the distinct-node theorem makes that
polynomial nonzero, since there is a jet vector at which it does not vanish.

A nonzero polynomial in the jets is precisely what the affine-reachability criterion consumes.  So
whenever the jets reachable from a parameter contain an affine image of a ball under a surjective
map — which the multiplicative gauge provides exactly, with no linearization error — the parameters
carrying full expanded rank are dense.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- The expanded evaluation matrix with fixed numeric nodes and indeterminate jet coordinates. -/
def expandedJetPolyMatrix {κ : Type} (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ) :
    Matrix (κ × Fin (q + 1)) (κ × Fin (q + 1))
      (MvPolynomial ((κ × Fin (q + 1)) × Fin n) ℂ) :=
  fun r c => MvPolynomial.C (z r ^ (c.2 : ℕ)) *
    (exponent c.1).prod fun k e => MvPolynomial.X (r, k) ^ e

/-- Evaluating the jet-indeterminate matrix recovers the numeric evaluation matrix. -/
theorem map_eval_expandedJetPolyMatrix {κ : Type} (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ)
    (y : (κ × Fin (q + 1)) × Fin n → ℂ) :
    (expandedJetPolyMatrix q n exponent z).map (MvPolynomial.eval y) =
      expandedDifferentialEvaluationMatrix q n z exponent y := by
  funext r c
  simp [expandedJetPolyMatrix, expandedDifferentialEvaluationMatrix, Matrix.map_apply,
    MvPolynomial.eval_monomial, Finsupp.prod, map_prod]

/-- The determinant of the jet-indeterminate matrix evaluates to the numeric determinant. -/
theorem eval_det_expandedJetPolyMatrix {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ)
    (y : (κ × Fin (q + 1)) × Fin n → ℂ) :
    MvPolynomial.eval y (expandedJetPolyMatrix q n exponent z).det =
      (expandedDifferentialEvaluationMatrix q n z exponent y).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_eval_expandedJetPolyMatrix]

/-- **A node choice making the jet determinant a nonzero polynomial.**  There are pairwise distinct
nodes for which the determinant, as a polynomial in the jet coordinates, is not the zero
polynomial. -/
theorem exists_injective_nodes_expandedJetDet_ne_zero
    {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧ (expandedJetPolyMatrix q n exponent z).det ≠ 0 := by
  obtain ⟨z, y, hz, hinj⟩ :=
    exists_injective_nodes_expandedMatrix_mulVec_injective q n exponent hexp
  refine ⟨z, hz, ?_⟩
  intro hzero
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero] at hinj
  apply hinj
  rw [← eval_det_expandedJetPolyMatrix q n exponent z y, hzero, map_zero]

/-- **Density of full expanded rank under affine jet reachability.**  If the jets reachable from
every parameter contain an affine image of a ball under a surjective continuous linear map, then
there are pairwise distinct nodes at which the parameters carrying full expanded column rank are
dense.

No differentiability of the jet map is used: the multiplicative gauge supplies the affine image
exactly. -/
theorem exists_nodes_dense_expandedMatrix_mulVec_injective
    {κ X : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (F : X → ((κ × Fin (q + 1)) × Fin n → ℂ))
    (hreach : ∀ u₀ : X, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
        ∃ L : X →L[ℝ] ((κ × Fin (q + 1)) × Fin n → ℂ), Function.Surjective L ∧
          ∀ h : X, ‖h‖ < δ → ∃ u : X, dist u u₀ < ε ∧ F u = F u₀ + L h) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      Dense {u : X | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent (F u)).mulVec} := by
  classical
  obtain ⟨z, hz, hpoly⟩ := exists_injective_nodes_expandedJetDet_ne_zero q n exponent hexp
  refine ⟨z, hz, ?_⟩
  have hdense := dense_nondegenerate_of_affine_reachability F
    (expandedJetPolyMatrix q n exponent z).det hpoly hreach
  refine hdense.mono ?_
  intro u hu
  have hdet : (expandedDifferentialEvaluationMatrix q n z exponent (F u)).det ≠ 0 := by
    rw [← eval_det_expandedJetPolyMatrix q n exponent z (F u)]
    exact hu
  rw [Set.mem_setOf_eq, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]
  exact hdet

end

end GaloisForLFunctions.HTGeometry
