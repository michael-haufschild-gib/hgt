import GaloisForLFunctions.HTGeometry.ExpandedMatrixDistinctNodes
import GaloisForLFunctions.HTGeometry.PolynomialJetEscape

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

/-! ## Admissible nodes in the upper half plane -/

/-- **A shape has an admissible node packet above the real axis.**  The determinant and the product
of node differences are both nonzero polynomials, so their product is nonzero on a dense set, which
meets the open set of packets with all nodes in the upper half plane. -/
theorem exists_upper_injective_nodes_shapeDeterminant_ne_zero {κ : Type} [Fintype κ]
    [DecidableEq κ] (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent) :
    ∃ z : κ × Fin (q + 1) → ℂ, Function.Injective z ∧ (∀ r, 0 < (z r).im) ∧
      shapeDeterminant q n exponent z ≠ 0 := by
  classical
  obtain ⟨z₀, y₀, -, hinj₀⟩ :=
    exists_injective_nodes_expandedMatrix_mulVec_injective q n exponent hexp
  set D : MvPolynomial ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) ℂ :=
    (expandedPolyMatrix q n exponent).det with hDdef
  have hDne : D ≠ 0 := by
    intro hzero
    have hdet0 : (expandedDifferentialEvaluationMatrix q n z₀ exponent y₀).det = 0 := by
      have heval := eval_det_expandedPolyMatrix q n exponent (Sum.elim z₀ y₀)
      rw [← hDdef, hzero, map_zero] at heval
      exact heval.symm
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero] at hinj₀
    exact hinj₀ hdet0
  set W : MvPolynomial ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) ℂ :=
    ∏ s ∈ Finset.univ.offDiag, (MvPolynomial.X (Sum.inl s.1) - MvPolynomial.X (Sum.inl s.2))
    with hWdef
  have hWne : W ≠ 0 := by
    rw [hWdef]
    refine Finset.prod_ne_zero_iff.2 fun s hs => ?_
    exact X_sub_X_ne_zero (by simpa using (Finset.mem_offDiag.1 hs).2.2)
  set U : Set (((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) → ℂ) :=
    {p | ∀ r, 0 < (p (Sum.inl r)).im} with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun r => ?_
    have hpre : {p : ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) → ℂ |
          0 < (p (Sum.inl r)).im}
        = (fun p : ((κ × Fin (q + 1)) ⊕ ((κ × Fin (q + 1)) × Fin n)) → ℂ => p (Sum.inl r)) ⁻¹'
          {b : ℂ | 0 < b.im} := rfl
    rw [hpre]
    exact IsOpen.preimage (continuous_apply _)
      (isOpen_lt continuous_const Complex.continuous_im)
  have hUne : U.Nonempty := by
    refine ⟨fun _ => Complex.I, ?_⟩
    intro r
    simp
  obtain ⟨p, hpne, hpU⟩ :=
    (mvPolynomial_nonzero_eval_dense (D * W) (mul_ne_zero hDne hWne)).exists_mem_open hUopen hUne
  simp only [Set.mem_setOf_eq] at hpne
  rw [map_mul] at hpne
  obtain ⟨hpD, hpW⟩ := mul_ne_zero_iff.1 hpne
  refine ⟨fun r => p (Sum.inl r), ?_, fun r => hpU r, ?_⟩
  · intro a b hab
    by_contra hne
    have hmem : (a, b) ∈ Finset.univ.offDiag := Finset.mem_offDiag.2 ⟨by simp, by simp, hne⟩
    have hWzero : MvPolynomial.eval p W = 0 := by
      rw [hWdef, map_prod]
      refine Finset.prod_eq_zero hmem ?_
      simp only [map_sub, MvPolynomial.eval_X]
      have hab' : p (Sum.inl a) = p (Sum.inl b) := hab
      rw [hab', sub_self]
    exact hpW hWzero
  · intro hzero
    have heval := eval_shapeDeterminant q n exponent (fun r => p (Sum.inl r))
      (fun t => p (Sum.inr t))
    rw [hzero, map_zero] at heval
    refine hpD ?_
    rw [hDdef, eval_det_expandedPolyMatrix]
    exact heval.symm

end

end GaloisForLFunctions.HTGeometry
