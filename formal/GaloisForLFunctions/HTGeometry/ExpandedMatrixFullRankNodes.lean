import GaloisForLFunctions.HTGeometry.MonomialPowerIndependence
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

/-!
# Sample points making the expanded evaluation matrix nonsingular

The rank condition behind the freeness predicate asks for a packet at which the expanded
differential evaluation matrix has injective `mulVec`, i.e. full column rank.

Its entries are `z r ^ d * M β (y r)`, and that family of functions of the pair `(z r, y r)` is
linearly independent.  A linearly independent family of scalar functions is separated by finitely
many sample points, so such points exist: the resulting matrix is a square nonsingular minor,
transported along the enumeration of the column index.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Full column rank at suitable sample points.**  With one row per column, there are node/jet
sample points at which the expanded differential evaluation matrix has injective `mulVec`.

The row chart `r ↦ (z r, y (r, ·))` is injective; distinctness of the nodes alone is a further
condition, not asserted here. -/
theorem exists_nodes_jets_expandedMatrix_mulVec_injective
    {κ : Type} [Fintype κ] [DecidableEq κ] (q n : ℕ)
    (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent) :
    ∃ (z : κ × Fin (q + 1) → ℂ) (y : (κ × Fin (q + 1)) × Fin n → ℂ),
      Function.Injective (fun r : κ × Fin (q + 1) => (z r, fun k => y (r, k))) ∧
      Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec := by
  classical
  set row := κ × Fin (q + 1)
  set E : row ≃ Fin (Fintype.card row) := Fintype.equivFin row with hE
  -- The column family, re-indexed by a canonical enumeration.
  set f : row → (ℂ × (Fin n → ℂ)) → ℂ := fun c p =>
    p.1 ^ (c.2 : ℕ) *
      MvPolynomial.eval p.2 (MvPolynomial.monomial (exponent c.1) (1 : ℂ)) with hf
  have hLI : LinearIndependent ℂ f := linearIndependent_pow_mul_monomial q exponent hexp
  have hLI' : LinearIndependent ℂ (f ∘ E.symm) := hLI.comp E.symm E.symm.injective
  obtain ⟨e, P, he, hPdet, hPeq⟩ :=
    exists_injective_evaluation_minor_of_linearIndependent (f ∘ E.symm) hLI'
  refine ⟨fun r => (e (E r)).1, fun p => (e (E p.1)).2 p.2, ?_, ?_⟩
  · intro a b hab
    have : e (E a) = e (E b) := by
      have h1 : (e (E a)).1 = (e (E b)).1 := congrArg Prod.fst hab
      have h2 : (e (E a)).2 = (e (E b)).2 := congrArg Prod.snd hab
      exact Prod.ext h1 h2
    exact E.injective (he this)
  · -- The matrix is `P` pulled back along the enumeration, so it inherits nonsingularity.
    have hsub : expandedDifferentialEvaluationMatrix q n
        (fun r : row => (e (E r)).1) exponent (fun p => (e (E p.1)).2 p.2) =
        P.submatrix E E := by
      funext r c
      rw [Matrix.submatrix_apply, hPeq]
      simp only [expandedDifferentialEvaluationMatrix, hf, Function.comp_apply,
        Equiv.symm_apply_apply]
    rw [hsub, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      Matrix.det_submatrix_equiv_self]
    exact hPdet

end

end GaloisForLFunctions.HTGeometry
