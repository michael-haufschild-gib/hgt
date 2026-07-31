import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolDeterminantHorizon

/-!
# Coefficient-oriented matrix principal-symbol flatness

For a column of source elements written as `D(u_n) = S_n u_(n+1) + lower`, coefficient matrices
compose in row order: applying `B` and then `A` produces `S_n(B) S_(n+1)(A)`.  This is the transpose
of the geometric-arrow convention used by `MatrixPrincipalSymbolFlat`.  The distinction is
invisible to determinants but essential for commutator curvature.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The two-step coefficient curvature of consecutive matrix principal symbols. -/
def matrixCoefficientPrincipalCurvature
    (symbol : ℕ → g → Matrix ι ι K) (n : ℕ) (A B : g) : Matrix ι ι K :=
  symbol n B * symbol (n + 1) A -
    symbol n A * symbol (n + 1) B

/-- Flatness in coefficient-row convention, the convention produced by iterated derivations of a
column of source elements. -/
def MatrixCoefficientPrincipalSymbolFlat
    (symbol : ℕ → g → Matrix ι ι K) : Prop :=
  ∀ n A B,
    symbol n B * symbol (n + 1) A =
      symbol n A * symbol (n + 1) B

omit [DecidableEq ι] in
/-- Coefficient flatness is exactly vanishing of the matrix coefficient curvature. -/
theorem matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero
    (symbol : ℕ → g → Matrix ι ι K) :
    MatrixCoefficientPrincipalSymbolFlat symbol ↔
      ∀ n A B, matrixCoefficientPrincipalCurvature symbol n A B = 0 := by
  simp only [MatrixCoefficientPrincipalSymbolFlat, matrixCoefficientPrincipalCurvature,
    sub_eq_zero]

omit [DecidableEq ι] in
/-- Coefficient-row flatness is geometric-arrow flatness after transposing every symbol. -/
theorem matrixCoefficientPrincipalSymbolFlat_iff_transpose_flat
    (symbol : ℕ → g → Matrix ι ι K) :
    MatrixCoefficientPrincipalSymbolFlat symbol ↔
      MatrixPrincipalSymbolFlat (fun n A ↦ Matrix.transpose (symbol n A)) := by
  constructor
  · intro h n A B
    have hAB := congrArg Matrix.transpose (h n A B)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hAB
  · intro h n A B
    have hAB := congrArg Matrix.transpose (h n A B)
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using hAB

/-- Coefficient flatness gives the same consecutive determinant cross law as geometric flatness. -/
theorem matrixCoefficientPrincipalSymbol_det_cross
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (n : ℕ) (A B : g) :
    (symbol (n + 1) A).det * (symbol n B).det =
      (symbol (n + 1) B).det * (symbol n A).det := by
  have hdet := congrArg Matrix.det (hflat n A B)
  simpa [Matrix.det_mul, mul_comm] using hdet

/-- In the nonempty regular phase, coefficient flatness also collapses the complete determinant
characteristic set to the first layer. -/
theorem matrixSymbolCharacteristicSet_eq_firstSingularSet_of_coefficientFlat
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0) :
    matrixSymbolCharacteristicSet symbol = matrixSymbolSingularSet symbol 0 := by
  have hflatT : MatrixPrincipalSymbolFlat
      (fun n A ↦ Matrix.transpose (symbol n A)) :=
    (matrixCoefficientPrincipalSymbolFlat_iff_transpose_flat symbol).mp hflat
  have hA₀T : ∀ n, (Matrix.transpose (symbol n A₀)).det ≠ 0 := by
    simpa using hA₀
  have h := matrixSymbolCharacteristicSet_eq_firstSingularSet
    (fun n A ↦ Matrix.transpose (symbol n A)) hflatT A₀ hA₀T
  simpa [matrixSymbolCharacteristicSet, matrixSymbolSingularSet] using h

/-- Exact all-singular/common-horizon dichotomy in the coefficient convention forced by iterated
derivation composition. -/
theorem matrixCoefficientPrincipalSymbolFlat_characteristicSet_dichotomy
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol) :
    matrixSymbolCharacteristicSet symbol = Set.univ ∨
      ∃ A₀ : g, (∀ n, (symbol n A₀).det ≠ 0) ∧
        matrixSymbolCharacteristicSet symbol = matrixSymbolSingularSet symbol 0 := by
  classical
  by_cases hex : ∃ A₀ : g, ∀ n, (symbol n A₀).det ≠ 0
  · right
    obtain ⟨A₀, hA₀⟩ := hex
    exact ⟨A₀, hA₀,
      matrixSymbolCharacteristicSet_eq_firstSingularSet_of_coefficientFlat
        symbol hflat A₀ hA₀⟩
  · left
    exact matrixSymbolCharacteristicSet_eq_univ_of_no_regularDirection symbol hex

end

end GaloisForLFunctions.HTGeometry
