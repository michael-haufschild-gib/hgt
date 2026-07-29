import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Polarized defect of two square-zero directions

For a bilinear square `q ↦ B q q`, the square of a sum is the two endpoint squares plus
the polarized cross term.  Hence two individually square-zero directions remain square-zero
under addition exactly when their cross defect vanishes.  If `B` is symmetric, that defect is
twice `B q r`.

This is unconditional standard algebra.  It does not identify square-zero directions with
quantum possibilities, the cross defect with an event, or the target module with spacetime.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R S V : Type*}
variable [CommRing R] [AddCommGroup S] [Module R S]
variable [AddCommGroup V] [Module R V]

/-- The quadratic square associated with a bilinear map. -/
def bilinearSquare (B : S →ₗ[R] S →ₗ[R] V) (q : S) : V :=
  B q q

/-- The polarized cross defect of two directions. -/
def squareCompatibilityDefect
    (B : S →ₗ[R] S →ₗ[R] V) (q r : S) : V :=
  B q r + B r q

/-- Exact polarization identity for a bilinear square. -/
theorem bilinearSquare_add
    (B : S →ₗ[R] S →ₗ[R] V) (q r : S) :
    bilinearSquare B (q + r) =
      bilinearSquare B q + squareCompatibilityDefect B q r +
        bilinearSquare B r := by
  simp [bilinearSquare, squareCompatibilityDefect]
  ac_rfl

/-- For individually square-zero directions, the square of their sum is exactly their
polarized cross defect. -/
theorem bilinearSquare_add_of_square_zero
    (B : S →ₗ[R] S →ₗ[R] V) (q r : S)
    (hq : bilinearSquare B q = 0)
    (hr : bilinearSquare B r = 0) :
    bilinearSquare B (q + r) = squareCompatibilityDefect B q r := by
  rw [bilinearSquare_add B q r, hq, hr]
  simp

/-- Two individually square-zero directions have a square-zero sum exactly when their
polarized cross defect vanishes. -/
theorem bilinearSquare_add_eq_zero_iff_compatibilityDefect_eq_zero
    (B : S →ₗ[R] S →ₗ[R] V) (q r : S)
    (hq : bilinearSquare B q = 0)
    (hr : bilinearSquare B r = 0) :
    bilinearSquare B (q + r) = 0 ↔
      squareCompatibilityDefect B q r = 0 := by
  rw [bilinearSquare_add_of_square_zero B q r hq hr]

/-- For a symmetric bilinear map, the compatibility defect is twice the cross pairing. -/
theorem squareCompatibilityDefect_eq_two_smul_of_symmetric
    (B : S →ₗ[R] S →ₗ[R] V)
    (hB : ∀ x y, B x y = B y x)
    (q r : S) :
    squareCompatibilityDefect B q r = (2 : R) • B q r := by
  rw [squareCompatibilityDefect, hB r q]
  exact (two_smul R (B q r)).symm

/-- Symmetric form of the square-zero compatibility law. -/
theorem bilinearSquare_add_of_square_zero_symmetric
    (B : S →ₗ[R] S →ₗ[R] V) (q r : S)
    (hB : ∀ x y, B x y = B y x)
    (hq : bilinearSquare B q = 0)
    (hr : bilinearSquare B r = 0) :
    bilinearSquare B (q + r) = (2 : R) • B q r := by
  rw [bilinearSquare_add_of_square_zero B q r hq hr]
  exact squareCompatibilityDefect_eq_two_smul_of_symmetric B hB q r

end GaloisForLFunctions.HTGeometry
