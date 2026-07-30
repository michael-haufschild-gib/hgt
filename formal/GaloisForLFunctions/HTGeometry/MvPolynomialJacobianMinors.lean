import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicOperations
import GaloisForLFunctions.HTGeometry.MvPolynomialSmoothEvaluation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complex Jacobian matrix of a finite multivariate polynomial family. -/
def complexMvPolynomialFamilyJacobian {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (P i))

/-- A maximal row-rank minor of the symbolic Jacobian. -/
def complexMvPolynomialFamilyJacobianMinor {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (cols : Fin m → Fin n) :
    MvPolynomial (Fin n) ℂ :=
  (Matrix.of fun i j => MvPolynomial.pderiv (cols j) (P i)).det

theorem eval_complexMvPolynomialFamilyJacobianMinor {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) (cols : Fin m → Fin n)
    (x : Fin n → ℂ) :
    MvPolynomial.eval x (complexMvPolynomialFamilyJacobianMinor P cols) =
      ((complexMvPolynomialFamilyJacobian P x).submatrix id cols).det := by
  have h := (MvPolynomial.aeval x).toRingHom.map_det
    (Matrix.of fun i j => MvPolynomial.pderiv (cols j) (P i))
  simpa [complexMvPolynomialFamilyJacobianMinor,
    complexMvPolynomialFamilyJacobian, MvPolynomial.aeval_def] using! h

/-- The locus where every maximal Jacobian minor vanishes. -/
def complexMvPolynomialFamilyJacobianRankDefect {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | ∀ cols : Fin m → Fin n,
    MvPolynomial.eval x (complexMvPolynomialFamilyJacobianMinor P cols) = 0}

/-- Maximal Jacobian-rank loss is a complex affine algebraic condition. -/
theorem isComplexAffineAlgebraic_complexMvPolynomialFamilyJacobianRankDefect
    {n m : ℕ} (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsComplexAffineAlgebraic (complexMvPolynomialFamilyJacobianRankDefect P) := by
  exact isComplexAffineAlgebraic_zeroLocus_finite_family
    (fun cols : Fin m → Fin n => complexMvPolynomialFamilyJacobianMinor P cols)

end

end GaloisForLFunctions.HTGeometry
