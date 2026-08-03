import GaloisForLFunctions.HTGeometry.ExpandedMatrixDistinctNodes

/-!
# One determinant polynomial per relation shape

A differential relation of a fixed shape -- a fixed finite set of expanded monomials and a fixed
degree in the spectral variable -- says that its coefficient vector is annihilated by the expanded
evaluation matrix at every packet of nodes.  If that matrix is invertible at one packet, the
coefficient vector is zero.

Invertibility at a packet is the nonvanishing of a *single* polynomial in the jet coordinates, once
the nodes are fixed: the determinant of the indeterminate evaluation matrix, specialised at those
nodes.  So an uncountable family of coefficient vectors is replaced by one polynomial per shape,
which is what a Baire argument over shapes consumes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The determinant of the expanded evaluation matrix with the nodes fixed: a polynomial in the jet
coordinates alone. -/
def shapeDeterminant {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ) :
    MvPolynomial ((κ × Fin (q + 1)) × Fin n) ℂ :=
  MvPolynomial.bind₁ (Sum.elim (fun r => MvPolynomial.C (z r)) MvPolynomial.X)
    (expandedPolyMatrix q n exponent).det

theorem eval_bind₁_sumElim {κ : Type} (q n : ℕ) (z : κ × Fin (q + 1) → ℂ)
    (Q : MvPolynomial ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) ℂ)
    (y : (κ × Fin (q + 1)) × Fin n → ℂ) :
    MvPolynomial.eval y
        (MvPolynomial.bind₁ (Sum.elim (fun r => MvPolynomial.C (z r)) MvPolynomial.X) Q)
      = MvPolynomial.eval (Sum.elim z y) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [map_add, hp, hr]
  | mul_X p s hp =>
      cases s with
      | inl r => simp [map_mul, hp]
      | inr t => simp [map_mul, hp]

/-- **The shape determinant evaluates to the numeric determinant.** -/
theorem eval_shapeDeterminant {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ)
    (y : (κ × Fin (q + 1)) × Fin n → ℂ) :
    MvPolynomial.eval y (shapeDeterminant q n exponent z)
      = (expandedDifferentialEvaluationMatrix q n z exponent y).det := by
  rw [shapeDeterminant, eval_bind₁_sumElim, eval_det_expandedPolyMatrix]
  rfl

/-- **A shape has a node packet whose determinant polynomial is nonzero.**  The nodes are pairwise
distinct, and the determinant is a nonzero polynomial in the jet coordinates alone. -/
theorem exists_injective_nodes_shapeDeterminant_ne_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ, Function.Injective z ∧ shapeDeterminant q n exponent z ≠ 0 := by
  obtain ⟨z, y, hz, hinj⟩ :=
    exists_injective_nodes_expandedMatrix_mulVec_injective q n exponent hexp
  refine ⟨z, hz, ?_⟩
  intro hzero
  have hdet : (expandedDifferentialEvaluationMatrix q n z exponent y).det ≠ 0 := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero] at hinj
    exact hinj
  refine hdet ?_
  rw [← eval_shapeDeterminant q n exponent z y, hzero, map_zero]

/-- **A nonvanishing determinant kills every coefficient vector of that shape.** -/
theorem coeff_eq_zero_of_shapeDeterminant_ne_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (z : κ × Fin (q + 1) → ℂ)
    (y : (κ × Fin (q + 1)) × Fin n → ℂ)
    (hdet : MvPolynomial.eval y (shapeDeterminant q n exponent z) ≠ 0)
    (c : κ × Fin (q + 1) → ℂ)
    (hrel : (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec c = 0) :
    c = 0 := by
  rw [eval_shapeDeterminant] at hdet
  have hunit : IsUnit (expandedDifferentialEvaluationMatrix q n z exponent y) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  have hzero : (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec c
      = (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec 0 := by
    rw [hrel, Matrix.mulVec_zero]
  exact hinj hzero

end

end GaloisForLFunctions.HTGeometry
