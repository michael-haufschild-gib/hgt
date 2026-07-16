import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reindexing both axes of a finite matrix preserves injectivity of its column map. -/
theorem matrix_mulVec_injective_reindex_iff
    {row row' col col' : Type*}
    [Fintype row] [Fintype row'] [Fintype col] [Fintype col']
    (eRow : row ≃ row') (eCol : col ≃ col') (M : Matrix row col ℂ) :
    Function.Injective (M.reindex eRow eCol).mulVec ↔
      Function.Injective M.mulVec := by
  change Function.Injective (M.reindex eRow eCol).mulVecLin ↔
    Function.Injective M.mulVecLin
  rw [Matrix.mulVecLin_reindex]
  let Eout : (row → ℂ) ≃ₗ[ℂ] (row' → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ eRow.symm
  let Ein : (col' → ℂ) ≃ₗ[ℂ] (col → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ eCol
  constructor
  · intro h x y hxy
    obtain ⟨x', hx⟩ := Ein.surjective x
    obtain ⟨y', hy⟩ := Ein.surjective y
    have hcomp : Eout (M.mulVecLin (Ein x')) =
        Eout (M.mulVecLin (Ein y')) := by
      rw [hx, hy, hxy]
    have hxy' : x' = y' := by
      apply h
      simpa [Eout, Ein, LinearMap.comp_apply] using hcomp
    calc
      x = Ein x' := hx.symm
      _ = Ein y' := congrArg Ein hxy'
      _ = y := hy
  · intro h
    exact Eout.injective.comp (h.comp Ein.injective)

/-- Lift one row block's exponent vector into the full packet-coordinate polynomial ring. -/
def expandedBlockExponent {row : Type*} {n : ℕ} (b : row) (e : Fin n →₀ ℕ) :
    (row × Fin n) →₀ ℕ :=
  e.embDomain ⟨fun j => (b, j), fun _ _ h => Prod.mk.inj h |>.2⟩

/-- The expanded evaluation matrix before packet-coordinate evaluation. -/
def expandedDifferentialEvaluationPolynomialMatrixOfFintype
    {row κ : Type*} [Fintype row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    Matrix (Fin (Fintype.card row))
      (Fin (Fintype.card (κ × Fin (q + 1))))
      (MvPolynomial (row × Fin n) ℂ) :=
  fun ib jc =>
    let b := (Fintype.equivFin row).symm ib
    let c := (Fintype.equivFin (κ × Fin (q + 1))).symm jc
    MvPolynomial.C (z b ^ (c.2 : ℕ)) *
      MvPolynomial.monomial (expandedBlockExponent b (exponent c.1)) 1

theorem eval_expandedDifferentialEvaluationPolynomialMatrixOfFintype
    {row κ : Type*} [Fintype row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (y : row × Fin n → ℂ) :
    mvPolynomialMatrixEval
      (expandedDifferentialEvaluationPolynomialMatrixOfFintype q n z exponent) y =
      (expandedDifferentialEvaluationMatrix q n z exponent y).submatrix
        (Fintype.equivFin row).symm
        (Fintype.equivFin (κ × Fin (q + 1))).symm := by
  funext ib jc
  let b := (Fintype.equivFin row).symm ib
  let c := (Fintype.equivFin (κ × Fin (q + 1))).symm jc
  change MvPolynomial.eval y
      (MvPolynomial.C (z b ^ (c.2 : ℕ)) *
        MvPolynomial.monomial (expandedBlockExponent b (exponent c.1)) 1) = _
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_monomial]
  rw [Matrix.submatrix_apply]
  change z b ^ (c.2 : ℕ) *
      (1 * (expandedBlockExponent b (exponent c.1)).prod fun a e => y a ^ e) =
    expandedDifferentialEvaluationMatrix q n z exponent y b c
  rw [expandedDifferentialEvaluationMatrix_apply]
  simp [expandedBlockExponent, Finsupp.prod_embDomain, b, c]

theorem injective_expandedDifferentialEvaluationPolynomialMatrixOfFintype_eval_iff
    {row κ : Type*} [Fintype row] [Fintype κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (y : row × Fin n → ℂ) :
    Function.Injective
      (mvPolynomialMatrixEval
        (expandedDifferentialEvaluationPolynomialMatrixOfFintype q n z exponent) y).mulVec ↔
    Function.Injective
      (expandedDifferentialEvaluationMatrix q n z exponent y).mulVec := by
  rw [eval_expandedDifferentialEvaluationPolynomialMatrixOfFintype]
  exact matrix_mulVec_injective_reindex_iff
    (Fintype.equivFin row)
    (Fintype.equivFin (κ × Fin (q + 1)))
    (expandedDifferentialEvaluationMatrix q n z exponent y)

/-- The literal expanded rank defect is the determinantal locus of its polynomial matrix. -/
theorem expandedDifferentialEvaluationRankDefect_eq_polynomialMatrixRankDefect
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    expandedDifferentialEvaluationRankDefect q n z exponent =
      mvPolynomialMatrixColumnRankDefect
        (expandedDifferentialEvaluationPolynomialMatrixOfFintype q n z exponent) := by
  ext y
  simp only [expandedDifferentialEvaluationRankDefect,
    Set.mem_preimage, mem_rectangularRankDefect_iff_not_injective,
    mvPolynomialMatrixColumnRankDefect, Set.mem_setOf_eq]
  exact not_congr
    (injective_expandedDifferentialEvaluationPolynomialMatrixOfFintype_eval_iff
      q n z exponent y).symm

/-- Expanded evaluation rank loss is affine algebraic, directly by maximal minors. -/
theorem isComplexAffineAlgebraicSet_expandedDifferentialEvaluationRankDefect
    {row κ : Type*} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ)) :
    IsComplexAffineAlgebraicSet
      (expandedDifferentialEvaluationRankDefect q n z exponent) := by
  rw [expandedDifferentialEvaluationRankDefect_eq_polynomialMatrixRankDefect]
  exact isComplexAffineAlgebraicSet_mvPolynomialMatrixColumnRankDefect _

end

end GaloisForLFunctions.HTGeometry
