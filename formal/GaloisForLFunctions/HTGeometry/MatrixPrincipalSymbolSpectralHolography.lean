import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDeterminantHorizon
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Matrix principal-symbol spectral holography

The determinant horizon is only the zero-eigenvalue shadow of a stronger rigidity law.  Relative
to one everywhere-invertible reference direction, flat consecutive matrix symbols are conjugate.
Consequently their complete characteristic polynomials, not merely their determinant zero sets,
are independent of the filtration layer.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- A matrix symbol normalized on the left by an invertible reference law direction. -/
def normalizedMatrixPrincipalSymbol
    (symbol : ℕ → g → Matrix ι ι K) (A₀ : g) (n : ℕ) (A : g) :
    Matrix ι ι K :=
  (symbol n A₀)⁻¹ * symbol n A

/-- The characteristic polynomial of the normalized matrix principal symbol at one layer. -/
def matrixPrincipalSpectralPolynomial
    (symbol : ℕ → g → Matrix ι ι K) (A₀ : g) (n : ℕ) (A : g) : Polynomial K :=
  (normalizedMatrixPrincipalSymbol symbol A₀ n A).charpoly

/-- **Normalized transport law.**  Flatness makes the next normalized symbol conjugate to the
current one by the current reference symbol. -/
theorem normalizedMatrixPrincipalSymbol_succ_eq_conj
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (n : ℕ) (A : g) :
    normalizedMatrixPrincipalSymbol symbol A₀ (n + 1) A =
      symbol n A₀ * normalizedMatrixPrincipalSymbol symbol A₀ n A *
        (symbol n A₀)⁻¹ := by
  have hunitn : IsUnit (symbol n A₀).det :=
    (isUnit_iff_ne_zero.mpr (hA₀ n))
  have hunitnext : IsUnit (symbol (n + 1) A₀).det :=
    (isUnit_iff_ne_zero.mpr (hA₀ (n + 1)))
  have hcross := hflat n A A₀
  unfold normalizedMatrixPrincipalSymbol
  calc
    (symbol (n + 1) A₀)⁻¹ * symbol (n + 1) A =
        (symbol (n + 1) A₀)⁻¹ *
          (symbol (n + 1) A * symbol n A₀) * (symbol n A₀)⁻¹ := by
            simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunitn, Matrix.mul_one]
    _ = (symbol (n + 1) A₀)⁻¹ *
          (symbol (n + 1) A₀ * symbol n A) * (symbol n A₀)⁻¹ := by
            rw [hcross]
    _ = symbol n A * (symbol n A₀)⁻¹ := by
            simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunitnext,
              Matrix.one_mul]
    _ = symbol n A₀ * ((symbol n A₀)⁻¹ * symbol n A) *
          (symbol n A₀)⁻¹ := by
            simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunitn,
              Matrix.one_mul]

/-- **One-step spectral holography.**  The complete normalized characteristic polynomial is
unchanged from one filtration layer to the next. -/
theorem matrixPrincipalSpectralPolynomial_succ
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (n : ℕ) (A : g) :
    matrixPrincipalSpectralPolynomial symbol A₀ (n + 1) A =
      matrixPrincipalSpectralPolynomial symbol A₀ n A := by
  rw [matrixPrincipalSpectralPolynomial, matrixPrincipalSpectralPolynomial,
    normalizedMatrixPrincipalSymbol_succ_eq_conj symbol hflat A₀ hA₀ n A,
    Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA₀ n)), Matrix.one_mul]

/-- **Full spectral holography.**  Every normalized layer has exactly the first layer's
characteristic polynomial.  All spectral multiplicity data visible to the characteristic
polynomial is therefore a first-horizon invariant. -/
theorem matrixPrincipalSpectralPolynomial_eq_first
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0) :
    ∀ n A,
      matrixPrincipalSpectralPolynomial symbol A₀ n A =
        matrixPrincipalSpectralPolynomial symbol A₀ 0 A := by
  intro n
  induction n with
  | zero => intro A; rfl
  | succ n ih =>
      intro A
      exact (matrixPrincipalSpectralPolynomial_succ
        symbol hflat A₀ hA₀ n A).trans (ih A)

end

end GaloisForLFunctions.HTGeometry
