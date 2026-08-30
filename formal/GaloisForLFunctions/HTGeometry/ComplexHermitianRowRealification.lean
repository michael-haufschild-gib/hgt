import GaloisForLFunctions.HTGeometry.ComplexHermitianRealification
import GaloisForLFunctions.HTGeometry.FiniteMatrixOrthogonalSum

/-!
# Row-convention Hermitian realification

The archimedean cone action uses row congruence `A ↦ G A Gᴴ`.  Its natural quadratic energy is
`Re (z A z*)`.  Conjugating the standard doubled-real model by the real involution
`(x, y) ↦ (x, -y)` realizes exactly this row-convention energy and preserves positive
definiteness.  This removes every conjugation mismatch between primitive integral rows and the
existing special-linear cone action.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped Classical ComplexOrder Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Real matrix implementing complex conjugation on doubled coordinates. -/
def doubledRealConjugation : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- Doubled-real conjugation fixes real channels and negates imaginary channels. -/
theorem doubledRealConjugation_mulVec (x : n ⊕ n → ℝ) :
    (doubledRealConjugation (n := n)).mulVec x = fun i =>
      match i with
      | Sum.inl j => x (Sum.inl j)
      | Sum.inr j => -x (Sum.inr j) := by
  funext i
  rcases i with i | i
  · simp [doubledRealConjugation, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂]
    change (1 : Matrix n n ℝ).mulVec (fun j => x (Sum.inl j)) i = _
    rw [Matrix.one_mulVec]
  · simp [doubledRealConjugation, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
    change (1 : Matrix n n ℝ).mulVec (fun j => x (Sum.inr j)) i = _
    rw [Matrix.one_mulVec]

/-- Doubled-real conjugation is injective. -/
theorem doubledRealConjugation_mulVec_injective :
    Function.Injective (doubledRealConjugation (n := n)).mulVec := by
  intro x y hxy
  rw [doubledRealConjugation_mulVec, doubledRealConjugation_mulVec] at hxy
  funext i
  rcases i with i | i
  · exact congrFun hxy (Sum.inl i)
  · have h := congrFun hxy (Sum.inr i)
    simpa using congrArg Neg.neg h

/-- Realification of the row-convention Hermitian quadratic form `Re (z A z*)`. -/
def complexMatrixRowRealification (A : Matrix n n ℂ) :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  let C := doubledRealConjugation (n := n)
  Cᴴ * complexMatrixRealification A * C

/-- Doubled-real conjugation recombines as ordinary complex conjugation. -/
theorem complexOfDoubledReal_conjugation (x : n ⊕ n → ℝ) :
    complexOfDoubledReal ((doubledRealConjugation (n := n)).mulVec x) =
      star (complexOfDoubledReal x) := by
  rw [doubledRealConjugation_mulVec]
  funext i
  apply Complex.ext <;> rfl

/-- Row realification has exactly the real row-Hermitian quadratic value. -/
theorem complexMatrixRowRealification_quadratic
    (A : Matrix n n ℂ) (x : n ⊕ n → ℝ) :
    x ⬝ᵥ (complexMatrixRowRealification A).mulVec x =
      ((complexOfDoubledReal x) ⬝ᵥ
        A.mulVec (star (complexOfDoubledReal x))).re := by
  rw [complexMatrixRowRealification]
  calc
    _ = star ((doubledRealConjugation (n := n)).mulVec x) ⬝ᵥ
        (complexMatrixRealification A).mulVec
          ((doubledRealConjugation (n := n)).mulVec x) := by
      simpa only [star_trivial] using
        (star_dotProduct_real_congr_mulVec
          (complexMatrixRealification A)
          (doubledRealConjugation (n := n)) x)
    _ = ((star (complexOfDoubledReal
          ((doubledRealConjugation (n := n)).mulVec x))) ⬝ᵥ
        A.mulVec (complexOfDoubledReal
          ((doubledRealConjugation (n := n)).mulVec x))).re := by
      exact complexMatrixRealification_quadratic A _
    _ = _ := by
      rw [complexOfDoubledReal_conjugation]
      simp

/-- Positive-definite Hermitian matrices have positive-definite row realifications. -/
theorem complexMatrixRowRealification_posDef
    {A : Matrix n n ℂ} (hA : A.PosDef) :
    (complexMatrixRowRealification A).PosDef := by
  exact (complexMatrixRealification_posDef hA).conjTranspose_mul_mul_same
    doubledRealConjugation_mulVec_injective

end

end GaloisForLFunctions.HTGeometry
