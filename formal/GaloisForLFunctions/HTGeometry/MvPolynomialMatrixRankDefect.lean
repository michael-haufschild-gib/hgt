import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv
import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicOperations

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A rectangular complex matrix is injective exactly when it has a nonsingular maximal minor. -/
theorem matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero
    {r c : ℕ} (A : Matrix (Fin r) (Fin c) ℂ) :
    Function.Injective A.mulVec ↔
      ∃ rows : Fin c → Fin r, (A.submatrix rows id).det ≠ 0 := by
  rw [Matrix.mulVec_injective_iff]
  constructor
  · intro hcols
    have hrows : LinearIndependent ℂ A.transpose.row := by
      simpa [Matrix.row, Matrix.col] using hcols
    have hsurj :=
      (matrix_mulVec_surjective_iff_linearIndependent_rows A.transpose).mpr hrows
    obtain ⟨rows, hrows⟩ :=
      matrix_exists_submatrix_det_ne_zero_of_mulVec_surjective A.transpose hsurj
    refine ⟨rows, ?_⟩
    have heq : (A.transpose).submatrix id rows =
        (A.submatrix rows id).transpose := by
      ext i j
      rfl
    rw [heq, Matrix.det_transpose] at hrows
    exact hrows
  · rintro ⟨rows, hrows⟩
    have hrows' : ((A.transpose).submatrix id rows).det ≠ 0 := by
      have heq : (A.transpose).submatrix id rows =
          (A.submatrix rows id).transpose := by
        ext i j
        rfl
      rw [heq, Matrix.det_transpose]
      exact hrows
    have hsurj := matrix_mulVec_surjective_of_submatrix_det_ne_zero
      A.transpose rows hrows'
    have hLI :=
      (matrix_mulVec_surjective_iff_linearIndependent_rows A.transpose).mp hsurj
    simpa [Matrix.row, Matrix.col] using hLI

/-- Evaluation of a matrix of multivariate polynomials. -/
def mvPolynomialMatrixEval {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ))
    (x : σ → ℂ) : Matrix (Fin r) (Fin c) ℂ :=
  fun i j => MvPolynomial.eval x (A i j)

def mvPolynomialMatrixColumnMinor {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ))
    (rows : Fin c → Fin r) : MvPolynomial σ ℂ :=
  (A.submatrix rows id).det

theorem eval_mvPolynomialMatrixColumnMinor {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ))
    (rows : Fin c → Fin r) (x : σ → ℂ) :
    MvPolynomial.eval x (mvPolynomialMatrixColumnMinor A rows) =
      ((mvPolynomialMatrixEval A x).submatrix rows id).det := by
  have h := (MvPolynomial.aeval x).toRingHom.map_det (A.submatrix rows id)
  simpa [mvPolynomialMatrixColumnMinor, mvPolynomialMatrixEval,
    MvPolynomial.aeval_def] using! h

/-- The pointwise loss-of-column-rank locus of a polynomial matrix. -/
def mvPolynomialMatrixColumnRankDefect {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ)) :
    Set (σ → ℂ) :=
  {x | ¬ Function.Injective (mvPolynomialMatrixEval A x).mulVec}

theorem mvPolynomialMatrixColumnRankDefect_eq_zeroLocus_minors
    {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ)) :
    mvPolynomialMatrixColumnRankDefect A =
      {x | ∀ rows : Fin c → Fin r,
        MvPolynomial.eval x (mvPolynomialMatrixColumnMinor A rows) = 0} := by
  ext x
  simp only [mvPolynomialMatrixColumnRankDefect, Set.mem_setOf_eq]
  rw [matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero]
  simp only [not_exists, not_ne_iff]
  constructor
  · intro h rows
    rw [eval_mvPolynomialMatrixColumnMinor]
    exact h rows
  · intro h rows
    rw [← eval_mvPolynomialMatrixColumnMinor]
    exact h rows

/-- Column-rank loss of a finite complex polynomial matrix is affine algebraic. -/
theorem isComplexAffineAlgebraicSet_mvPolynomialMatrixColumnRankDefect
    {r c : ℕ} {σ : Type*}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial σ ℂ)) :
    IsComplexAffineAlgebraicSet (mvPolynomialMatrixColumnRankDefect A) := by
  rw [mvPolynomialMatrixColumnRankDefect_eq_zeroLocus_minors]
  exact isComplexAffineAlgebraicSet_zeroLocus_family
    (fun rows : Fin c → Fin r => mvPolynomialMatrixColumnMinor A rows)

theorem isComplexAffineAlgebraic_mvPolynomialMatrixColumnRankDefect {r c n : ℕ}
    (A : Matrix (Fin r) (Fin c) (MvPolynomial (Fin n) ℂ)) :
    IsComplexAffineAlgebraic (mvPolynomialMatrixColumnRankDefect A) := by
  obtain ⟨I, hI⟩ :=
    isComplexAffineAlgebraicSet_mvPolynomialMatrixColumnRankDefect A
  exact ⟨I, hI⟩

end

end GaloisForLFunctions.HTGeometry
