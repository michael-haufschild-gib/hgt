import GaloisForLFunctions.HTGeometry.GradedPrincipalSymbolHorizon
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Matrix principal-symbol determinant horizon

A flat sequence of square matrix symbols cannot have independently varying determinant horizons.
If one law direction is invertible at every layer, the singular locus of every layer equals the
first determinantal locus.  If no such direction exists, the union of the singular loci is the
whole law space.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Flatness of consecutive square matrix symbols: every two law directions form a commuting
square between adjacent graded layers. -/
def MatrixPrincipalSymbolFlat
    (symbol : ℕ → g → Matrix ι ι K) : Prop :=
  ∀ n A B,
    symbol (n + 1) A * symbol n B =
      symbol (n + 1) B * symbol n A

/-- The singular law directions at one matrix-symbol layer. -/
def matrixSymbolSingularSet
    (symbol : ℕ → g → Matrix ι ι K) (n : ℕ) : Set g :=
  {A | (symbol n A).det = 0}

/-- The complete matrix characteristic set, before imposing flatness. -/
def matrixSymbolCharacteristicSet
    (symbol : ℕ → g → Matrix ι ι K) : Set g :=
  {A | ∃ n, (symbol n A).det = 0}

/-- Flatness gives an exact multiplicative cross-ratio law for consecutive determinants. -/
theorem matrixPrincipalSymbol_det_cross
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (n : ℕ) (A B : g) :
    (symbol (n + 1) A).det * (symbol n B).det =
      (symbol (n + 1) B).det * (symbol n A).det := by
  have h := congrArg Matrix.det (hflat n A B)
  simpa [Matrix.det_mul] using h

/-- Relative to one everywhere-invertible law, consecutive layer determinants have exactly the
same zero set. -/
theorem matrixPrincipalSymbol_det_succ_eq_zero_iff
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0)
    (n : ℕ) (A : g) :
    (symbol (n + 1) A).det = 0 ↔ (symbol n A).det = 0 := by
  have hdet := matrixPrincipalSymbol_det_cross symbol hflat n A A₀
  constructor
  · intro hnext
    have hprod : (symbol (n + 1) A₀).det * (symbol n A).det = 0 := by
      rw [← hdet, hnext, zero_mul]
    exact (mul_eq_zero.mp hprod).resolve_left (hA₀ (n + 1))
  · intro hn
    have hprod : (symbol (n + 1) A).det * (symbol n A₀).det = 0 := by
      rw [hdet, hn, mul_zero]
    exact (mul_eq_zero.mp hprod).resolve_right (hA₀ n)

/-- Every layer determinant has the same zero set as the first layer whenever one direction is
invertible at every layer. -/
theorem matrixPrincipalSymbol_det_eq_zero_iff_first
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0) :
    ∀ n A, (symbol n A).det = 0 ↔ (symbol 0 A).det = 0 := by
  intro n
  induction n with
  | zero => intro A; rfl
  | succ n ih =>
      intro A
      exact (matrixPrincipalSymbol_det_succ_eq_zero_iff
        symbol hflat A₀ hA₀ n A).trans (ih A)

/-- **Common determinant horizon.** In the nonempty regular phase, the complete countable union of
matrix-symbol singular loci is one determinantal locus. -/
theorem matrixSymbolCharacteristicSet_eq_firstSingularSet
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol)
    (A₀ : g) (hA₀ : ∀ n, (symbol n A₀).det ≠ 0) :
    matrixSymbolCharacteristicSet symbol = matrixSymbolSingularSet symbol 0 := by
  ext A
  constructor
  · rintro ⟨n, hn⟩
    exact (matrixPrincipalSymbol_det_eq_zero_iff_first
      symbol hflat A₀ hA₀ n A).mp hn
  · intro hzero
    exact ⟨0, hzero⟩

/-- If there is no direction invertible at every layer, every law direction meets some matrix
symbol horizon. -/
theorem matrixSymbolCharacteristicSet_eq_univ_of_no_regularDirection
    (symbol : ℕ → g → Matrix ι ι K)
    (hnone : ¬ ∃ A : g, ∀ n, (symbol n A).det ≠ 0) :
    matrixSymbolCharacteristicSet symbol = Set.univ := by
  ext A
  simp only [matrixSymbolCharacteristicSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  by_contra hA
  push Not at hA
  exact hnone ⟨A, hA⟩

/-- **Flat determinant-horizon dichotomy.** A flat square matrix-symbol system has either an empty
regular phase, so every direction is singular somewhere, or a nonempty regular phase whose entire
characteristic set is the single first determinantal locus. -/
theorem matrixPrincipalSymbolFlat_characteristicSet_dichotomy
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixPrincipalSymbolFlat symbol) :
    matrixSymbolCharacteristicSet symbol = Set.univ ∨
      ∃ A₀ : g, (∀ n, (symbol n A₀).det ≠ 0) ∧
        matrixSymbolCharacteristicSet symbol = matrixSymbolSingularSet symbol 0 := by
  classical
  by_cases hex : ∃ A₀ : g, ∀ n, (symbol n A₀).det ≠ 0
  · right
    obtain ⟨A₀, hA₀⟩ := hex
    exact ⟨A₀, hA₀,
      matrixSymbolCharacteristicSet_eq_firstSingularSet symbol hflat A₀ hA₀⟩
  · left
    exact matrixSymbolCharacteristicSet_eq_univ_of_no_regularDirection symbol hex

end

end GaloisForLFunctions.HTGeometry
