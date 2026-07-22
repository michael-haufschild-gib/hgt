import GaloisForLFunctions.HTGeometry.ExpandedMatrixFullRankNodes

/-!
# Nonsingular sample points with pairwise distinct nodes

Full column rank of the expanded evaluation matrix is available at some node/jet sample points, but
a row packet additionally requires the nodes to be pairwise distinct.

Both conditions are nonvanishing of polynomials in the sample coordinates: the determinant of the
matrix with indeterminate entries, and the product of node differences.  Neither polynomial is zero
— the first because it is nonzero at the known sample point, the second because it is a product of
nonzero factors in a domain — so their product is nonzero and admits a nonvanishing point.  There
the matrix is nonsingular and the nodes are distinct.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- A nonzero polynomial over `ℂ` does not vanish everywhere. -/
theorem exists_eval_ne_zero {σ : Type*} {Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0) :
    ∃ p : σ → ℂ, MvPolynomial.eval p Q ≠ 0 := by
  by_contra h
  push Not at h
  exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])

/-- Distinct indeterminates have a nonzero difference. -/
theorem X_sub_X_ne_zero {σ : Type*} [DecidableEq σ] {a b : σ} (hab : a ≠ b) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial σ ℂ) ≠ 0 := by
  intro h
  have hev := congrArg (MvPolynomial.eval (fun v => if v = a then (1 : ℂ) else 0)) h
  simp only [map_sub, MvPolynomial.eval_X, map_zero,
    if_neg (Ne.symm hab), sub_zero] at hev
  exact one_ne_zero hev

/-- The expanded evaluation matrix with indeterminate node and jet coordinates. -/
def expandedPolyMatrix {κ : Type} (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) :
    Matrix (κ × Fin (q + 1)) (κ × Fin (q + 1))
      (MvPolynomial ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) ℂ) :=
  fun r c => MvPolynomial.X (Sum.inl r) ^ (c.2 : ℕ) *
    (exponent c.1).prod fun k e => MvPolynomial.X (Sum.inr (r, k)) ^ e

/-- Evaluating the indeterminate matrix recovers the numeric evaluation matrix. -/
theorem map_eval_expandedPolyMatrix {κ : Type} (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ))
    (p : ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) → ℂ) :
    (expandedPolyMatrix q n exponent).map (MvPolynomial.eval p) =
      expandedDifferentialEvaluationMatrix q n (fun r => p (Sum.inl r)) exponent
        (fun x => p (Sum.inr x)) := by
  funext r c
  simp [expandedPolyMatrix, expandedDifferentialEvaluationMatrix, Matrix.map_apply,
    MvPolynomial.eval_monomial, Finsupp.prod, map_prod]

/-- The determinant of the indeterminate matrix evaluates to the numeric determinant. -/
theorem eval_det_expandedPolyMatrix {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ))
    (p : ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) → ℂ) :
    MvPolynomial.eval p (expandedPolyMatrix q n exponent).det =
      (expandedDifferentialEvaluationMatrix q n (fun r => p (Sum.inl r)) exponent
        (fun x => p (Sum.inr x))).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_eval_expandedPolyMatrix]

/-- **Full column rank at distinct nodes.**  There are node/jet sample points with pairwise distinct
nodes at which the expanded differential evaluation matrix has injective `mulVec`. -/
theorem exists_injective_nodes_expandedMatrix_mulVec_injective
    {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent) :
    ∃ (z : κ × Fin (q + 1) → ℂ) (y : (κ × Fin (q + 1)) × Fin n → ℂ),
      Function.Injective z ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec := by
  classical
  set row := κ × Fin (q + 1)
  set V := row ⊕ (row × Fin n)
  set D : MvPolynomial V ℂ := (expandedPolyMatrix q n exponent).det with hD
  -- The determinant is not the zero polynomial: it is nonzero at the known sample point.
  obtain ⟨z₀, y₀, _, hinj₀⟩ :=
    exists_nodes_jets_expandedMatrix_mulVec_injective q n exponent hexp
  have hDne : D ≠ 0 := by
    intro hzero
    set p₀ : V → ℂ := Sum.elim z₀ y₀ with hp₀
    have hdet0 : (expandedDifferentialEvaluationMatrix q n z₀ exponent y₀).det = 0 := by
      have heval := eval_det_expandedPolyMatrix q n exponent p₀
      rw [← hD, hzero, map_zero] at heval
      exact heval.symm
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero] at hinj₀
    exact hinj₀ hdet0
  -- The product of node differences is not the zero polynomial either.
  set W : MvPolynomial V ℂ :=
    ∏ s ∈ Finset.univ.offDiag, (MvPolynomial.X (Sum.inl s.1) - MvPolynomial.X (Sum.inl s.2))
    with hW
  have hWne : W ≠ 0 := by
    rw [hW]
    refine Finset.prod_ne_zero_iff.2 ?_
    intro s hs
    have hne : s.1 ≠ s.2 := (Finset.mem_offDiag.1 hs).2.2
    exact X_sub_X_ne_zero (by simpa using hne)
  obtain ⟨p, hp⟩ := exists_eval_ne_zero (mul_ne_zero hDne hWne)
  rw [map_mul] at hp
  refine ⟨fun r => p (Sum.inl r), fun x => p (Sum.inr x), ?_, ?_⟩
  · -- Distinct nodes, from nonvanishing of the difference product.
    intro a b hab
    by_contra hne
    have hmem : (a, b) ∈ Finset.univ.offDiag := Finset.mem_offDiag.2 ⟨by simp, by simp, hne⟩
    have hWzero : MvPolynomial.eval p W = 0 := by
      rw [hW, map_prod]
      refine Finset.prod_eq_zero hmem ?_
      simp only [map_sub, MvPolynomial.eval_X]
      exact sub_eq_zero.2 hab
    exact (mul_ne_zero_iff.1 hp).2 hWzero
  · -- Nonsingularity, from nonvanishing of the determinant.
    have hdet : (expandedDifferentialEvaluationMatrix q n (fun r => p (Sum.inl r)) exponent
        (fun x => p (Sum.inr x))).det ≠ 0 := by
      rw [← eval_det_expandedPolyMatrix q n exponent p, ← hD]
      exact (mul_ne_zero_iff.1 hp).1
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hdet

end

end GaloisForLFunctions.HTGeometry
