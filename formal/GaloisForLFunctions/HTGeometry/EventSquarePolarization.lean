import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Matrix-valued event-square polarization

For a finite complex matrix `X`, its event square is the positive Gram record `Xᴴ X`.
Evaluating this one quadratic map on the four superpositions `X ± Y` and `X ± iY`
recovers the complete ordered cross-Gram matrix `Xᴴ Y`.

This is the standard complex polarization identity with a matrix-valued codomain. It does not
identify amplitudes with physical events, Gram matrices with spacetime, or their symmetries with
forces.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {m n : Type*} [Fintype m]

/-- Positive quadratic Gram record associated with a finite complex matrix. -/
def eventSquare (X : Matrix m n ℂ) : Matrix n n ℂ :=
  Xᴴ * X

/-- Ordered sesquilinear cross-Gram record of two finite complex matrices. -/
def eventCrossGram (X Y : Matrix m n ℂ) : Matrix n n ℂ :=
  Xᴴ * Y

/-- The real-polarization difference recovers twice the Hermitian cross term. -/
theorem eventSquare_add_sub_polarization (X Y : Matrix m n ℂ) :
    eventSquare (X + Y) - eventSquare (X - Y) =
      (2 : ℂ) • (eventCrossGram X Y + eventCrossGram Y X) := by
  rw [two_smul ℂ]
  ext i j
  simp only [eventSquare, eventCrossGram, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hstarAdd :
      star (X x i + Y x i) = star (X x i) + star (Y x i) :=
    (starAddEquiv : ℂ ≃+ ℂ).map_add _ _
  rw [hstarAdd, star_sub]
  ring

/-- The imaginary-polarization difference recovers twice `i` times the skew cross term. -/
theorem eventSquare_i_add_sub_polarization (X Y : Matrix m n ℂ) :
    eventSquare (X + Complex.I • Y) -
        eventSquare (X - Complex.I • Y) =
      (2 * Complex.I) • (eventCrossGram X Y - eventCrossGram Y X) := by
  rw [eventSquare_add_sub_polarization]
  simp [eventCrossGram, Matrix.conjTranspose_smul, Matrix.mul_smul,
    Matrix.smul_mul, sub_eq_add_neg, smul_smul]

/-- Full matrix-valued complex polarization: four event-square evaluations recover `Xᴴ Y`. -/
theorem eventCrossGram_eq_eventSquare_polarization (X Y : Matrix m n ℂ) :
    eventCrossGram X Y =
      (1 / 4 : ℂ) •
        ((eventSquare (X + Y) - eventSquare (X - Y)) -
          Complex.I •
            (eventSquare (X + Complex.I • Y) -
              eventSquare (X - Complex.I • Y))) := by
  rw [eventSquare_add_sub_polarization,
    eventSquare_i_add_sub_polarization]
  simp [smul_smul, sub_eq_add_neg]
  ring_nf
  rw [Complex.I_sq]
  ext i j
  simp
  ring

end GaloisForLFunctions.HTGeometry
