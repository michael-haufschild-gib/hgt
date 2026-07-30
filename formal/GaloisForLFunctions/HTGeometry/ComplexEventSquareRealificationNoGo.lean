import GaloisForLFunctions.HTGeometry.EventSquarePolarization
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Block

/-!
# Complex event squares have faithful doubled-real models

Every finite complex matrix has the standard real block representation

`X ↦ [[re X, -im X], [im X, re X]]`.

This file proves that the representation is injective and preserves addition, multiplication,
adjoint as transpose, event squares, and ordered cross-Gram records.  Complex phase becomes a
distinguished real complex structure `J` with `J² = -1`, and every realified complex matrix
intertwines the source and target copies of `J`.

Consequently, static finite event-square algebra cannot by itself select complex scalars over a
faithful doubled-real presentation.  Any physical distinction must use extra structure not
discarded by this representation, such as a source-generated orientation law for independent
composition.  That scientific interpretation is not asserted as a Lean theorem.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {m n p : Type*}

/-- Entrywise real part of a complex matrix. -/
def complexMatrixRealPart (X : Matrix m n ℂ) : Matrix m n ℝ :=
  fun i j => (X i j).re

/-- Entrywise imaginary part of a complex matrix. -/
def complexMatrixImagPart (X : Matrix m n ℂ) : Matrix m n ℝ :=
  fun i j => (X i j).im

/-- Standard faithful doubled-real block representation of a complex matrix. -/
def complexMatrixRealification (X : Matrix m n ℂ) :
    Matrix (m ⊕ m) (n ⊕ n) ℝ :=
  Matrix.fromBlocks
    (complexMatrixRealPart X) (-complexMatrixImagPart X)
    (complexMatrixImagPart X) (complexMatrixRealPart X)

/-- Real parts turn complex matrix multiplication into the usual two-channel difference. -/
theorem complexMatrixRealPart_mul [Fintype n]
    (X : Matrix m n ℂ) (Y : Matrix n p ℂ) :
    complexMatrixRealPart (X * Y) =
      complexMatrixRealPart X * complexMatrixRealPart Y -
        complexMatrixImagPart X * complexMatrixImagPart Y := by
  ext i j
  simp [complexMatrixRealPart, complexMatrixImagPart, Matrix.mul_apply,
    Complex.mul_re, Finset.sum_sub_distrib]

/-- Imaginary parts turn complex matrix multiplication into the usual two-channel sum. -/
theorem complexMatrixImagPart_mul [Fintype n]
    (X : Matrix m n ℂ) (Y : Matrix n p ℂ) :
    complexMatrixImagPart (X * Y) =
      complexMatrixRealPart X * complexMatrixImagPart Y +
        complexMatrixImagPart X * complexMatrixRealPart Y := by
  ext i j
  simp [complexMatrixRealPart, complexMatrixImagPart, Matrix.mul_apply,
    Complex.mul_im, Finset.sum_add_distrib]

/-- Real parts of the conjugate transpose are ordinary transposes. -/
theorem complexMatrixRealPart_conjTranspose (X : Matrix m n ℂ) :
    complexMatrixRealPart Xᴴ = (complexMatrixRealPart X)ᵀ := by
  ext i j
  simp [complexMatrixRealPart, Matrix.conjTranspose_apply]

/-- Imaginary parts of the conjugate transpose are negative ordinary transposes. -/
theorem complexMatrixImagPart_conjTranspose (X : Matrix m n ℂ) :
    complexMatrixImagPart Xᴴ = -(complexMatrixImagPart X)ᵀ := by
  ext i j
  simp [complexMatrixImagPart, Matrix.conjTranspose_apply]

/-- Doubled-real representation is faithful. -/
theorem complexMatrixRealification_injective :
    Function.Injective (complexMatrixRealification :
      Matrix m n ℂ → Matrix (m ⊕ m) (n ⊕ n) ℝ) := by
  intro X Y h
  ext i j
  apply Complex.ext
  · have hre := congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
    simpa [complexMatrixRealification, complexMatrixRealPart] using hre
  · have him := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
    simpa [complexMatrixRealification, complexMatrixImagPart] using him

/-- Doubled-real representation preserves addition. -/
theorem complexMatrixRealification_add (X Y : Matrix m n ℂ) :
    complexMatrixRealification (X + Y) =
      complexMatrixRealification X + complexMatrixRealification Y := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexMatrixRealification, complexMatrixRealPart, complexMatrixImagPart,
      add_comm]

/-- Doubled-real representation preserves matrix composition. -/
theorem complexMatrixRealification_mul [Fintype n]
    (X : Matrix m n ℂ) (Y : Matrix n p ℂ) :
    complexMatrixRealification (X * Y) =
      complexMatrixRealification X * complexMatrixRealification Y := by
  rw [complexMatrixRealification, complexMatrixRealification,
    complexMatrixRealification, complexMatrixRealPart_mul,
    complexMatrixImagPart_mul, Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [Matrix.mul_apply] <;> ring

/-- Complex conjugate transpose becomes real transpose. -/
theorem complexMatrixRealification_conjTranspose (X : Matrix m n ℂ) :
    complexMatrixRealification Xᴴ =
      (complexMatrixRealification X)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexMatrixRealification, complexMatrixRealPart, complexMatrixImagPart,
      Matrix.conjTranspose_apply]

/-- Complex event squares are exactly real Gram squares after faithful doubling. -/
theorem complexMatrixRealification_eventSquare [Fintype m]
    (X : Matrix m n ℂ) :
    complexMatrixRealification (eventSquare X) =
      (complexMatrixRealification X)ᵀ * complexMatrixRealification X := by
  rw [eventSquare, complexMatrixRealification_mul,
    complexMatrixRealification_conjTranspose]

/-- Ordered complex cross-Gram records are exactly doubled-real cross-Gram products. -/
theorem complexMatrixRealification_eventCrossGram [Fintype m]
    (X Y : Matrix m n ℂ) :
    complexMatrixRealification (eventCrossGram X Y) =
      (complexMatrixRealification X)ᵀ * complexMatrixRealification Y := by
  rw [eventCrossGram, complexMatrixRealification_mul,
    complexMatrixRealification_conjTranspose]

/-- Realification neither identifies nor separates any two complex event-square records. -/
theorem complexMatrixRealification_eventSquare_eq_iff [Fintype m]
    (X Y : Matrix m n ℂ) :
    complexMatrixRealification (eventSquare X) =
        complexMatrixRealification (eventSquare Y) ↔
      eventSquare X = eventSquare Y := by
  constructor
  · intro h
    exact complexMatrixRealification_injective h
  · intro h
    exact congrArg complexMatrixRealification h

/-- Canonical quarter-turn on the doubled real coordinate space. -/
def doubledRealComplexStructure [DecidableEq n] :
    Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The distinguished doubled-real quarter-turn squares to negative identity. -/
theorem doubledRealComplexStructure_sq [Fintype n] [DecidableEq n] :
    doubledRealComplexStructure (n := n) * doubledRealComplexStructure (n := n) = -1 := by
  rw [doubledRealComplexStructure, Matrix.fromBlocks_multiply]
  simp only [zero_mul, neg_mul, one_mul, add_zero, zero_add, neg_zero]
  simpa only [Matrix.fromBlocks_neg, neg_zero] using
    congrArg Neg.neg
      (Matrix.fromBlocks_one (l := n) (m := n) (α := ℝ))

/-- Multiplication by complex `I` becomes a real block quarter-turn. -/
theorem complexMatrixRealification_I_smul (X : Matrix m n ℂ) :
    complexMatrixRealification (Complex.I • X) =
      Matrix.fromBlocks
        (-complexMatrixImagPart X) (-complexMatrixRealPart X)
        (complexMatrixRealPart X) (-complexMatrixImagPart X) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [complexMatrixRealification, complexMatrixRealPart, complexMatrixImagPart]

/-- Acting by the target complex structure realizes complex multiplication by `I`. -/
theorem doubledRealComplexStructure_mul_realification
    [Fintype m] [DecidableEq m] (X : Matrix m n ℂ) :
    doubledRealComplexStructure (n := m) * complexMatrixRealification X =
      complexMatrixRealification (Complex.I • X) := by
  rw [doubledRealComplexStructure, complexMatrixRealification,
    Matrix.fromBlocks_multiply, complexMatrixRealification_I_smul]
  congr 1 <;> ext i j <;> simp

/-- Acting by the source complex structure also realizes complex multiplication by `I`. -/
theorem realification_mul_doubledRealComplexStructure
    [Fintype n] [DecidableEq n] (X : Matrix m n ℂ) :
    complexMatrixRealification X * doubledRealComplexStructure (n := n) =
      complexMatrixRealification (Complex.I • X) := by
  rw [doubledRealComplexStructure, complexMatrixRealification,
    Matrix.fromBlocks_multiply, complexMatrixRealification_I_smul]
  congr 1 <;> ext i j <;> simp

/-- Every realified complex matrix intertwines canonical complex structures. -/
theorem complexMatrixRealification_intertwines_complexStructure
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) :
    doubledRealComplexStructure (n := m) * complexMatrixRealification X =
      complexMatrixRealification X * doubledRealComplexStructure (n := n) := by
  rw [doubledRealComplexStructure_mul_realification,
    realification_mul_doubledRealComplexStructure]

end GaloisForLFunctions.HTGeometry
