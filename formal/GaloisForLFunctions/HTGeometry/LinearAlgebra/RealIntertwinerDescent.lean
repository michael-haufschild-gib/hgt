import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.ByContra

/-!
# Real descent of simultaneous matrix intertwiners

Write a complex invertible intertwiner as `U + I V`. Both real matrices `U`
and `V` satisfy every real intertwining equation. The determinant of `U + t V`
is a nonzero real polynomial: its value at `I` is the original determinant.
Some real parameter therefore gives an invertible simultaneous intertwiner.
The family of equations may be infinite.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Matrix Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real polynomial matrix whose value at `I` is the given complex matrix. -/
def realIntertwinerPencil (C : Matrix ι ι ℂ) : Matrix ι ι ℝ[X] :=
  fun i j => Polynomial.C (C i j).re + Polynomial.X * Polynomial.C (C i j).im

/-- Complex evaluation reconstructs the original matrix. -/
theorem realIntertwinerPencil_eval_complex (C : Matrix ι ι ℂ) :
    (Polynomial.eval₂RingHom Complex.ofRealHom Complex.I).mapMatrix (realIntertwinerPencil C) = C := by
  ext i j
  change Polynomial.eval₂ Complex.ofRealHom Complex.I
    (Polynomial.C (C i j).re + Polynomial.X * Polynomial.C (C i j).im) = C i j
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Complex.ofRealHom_eq_coe]
  rw [mul_comm]
  exact Complex.re_add_im (C i j)

/-- Real evaluation gives a real linear combination of real and imaginary parts. -/
theorem realIntertwinerPencil_eval_real (C : Matrix ι ι ℂ) (t : ℝ) :
    (Polynomial.evalRingHom t).mapMatrix (realIntertwinerPencil C) =
      C.map Complex.re + t • C.map Complex.im := by
  ext i j
  change Polynomial.eval t (Polynomial.C (C i j).re +
    Polynomial.X * Polynomial.C (C i j).im) = (C i j).re + t * (C i j).im
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]

/-- An invertible complex matrix has an invertible real combination of its real and imaginary parts. -/
theorem exists_real_invertible_pencil (C : Matrix ι ι ℂ) (hC : IsUnit C) :
    ∃ t : ℝ, IsUnit (C.map Complex.re + t • C.map Complex.im) := by
  have hp : (realIntertwinerPencil C).det ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval₂RingHom Complex.ofRealHom Complex.I) h
    rw [RingHom.map_det, realIntertwinerPencil_eval_complex, map_zero] at hh
    exact (Matrix.isUnit_iff_isUnit_det C).mp hC |>.ne_zero hh
  have hex : ∃ t : ℝ, (realIntertwinerPencil C).det.eval t ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.funext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)⟩
  have he := (Polynomial.evalRingHom t).map_det (realIntertwinerPencil C)
  rw [realIntertwinerPencil_eval_real] at he
  exact he ▸ ht

omit [DecidableEq ι] in
/-- Taking real parts preserves a matrix equation with real coefficients. -/
theorem realPart_intertwines (A B : Matrix ι ι ℝ) (C : Matrix ι ι ℂ)
    (h : C * A.map Complex.ofReal = B.map Complex.ofReal * C) :
    C.map Complex.re * A = B * C.map Complex.re := by
  ext i j
  have hh := congrArg Complex.re (congrFun (congrFun h i) j)
  simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using hh

omit [DecidableEq ι] in
/-- Taking imaginary parts preserves a matrix equation with real coefficients. -/
theorem imagPart_intertwines (A B : Matrix ι ι ℝ) (C : Matrix ι ι ℂ)
    (h : C * A.map Complex.ofReal = B.map Complex.ofReal * C) :
    C.map Complex.im * A = B * C.map Complex.im := by
  ext i j
  have hh := congrArg Complex.im (congrFun (congrFun h i) j)
  simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add] using hh

/-- Simultaneous similarity of real matrix families descends from the complex numbers. -/
theorem exists_real_simultaneous_intertwiner {S : Type*}
    (A B : S → Matrix ι ι ℝ) (C : Matrix ι ι ℂ) (hC : IsUnit C)
    (h : ∀ s, C * (A s).map Complex.ofReal = (B s).map Complex.ofReal * C) :
    ∃ D : Matrix ι ι ℝ, IsUnit D ∧ ∀ s, D * A s = B s * D := by
  obtain ⟨t, ht⟩ := exists_real_invertible_pencil C hC
  refine ⟨C.map Complex.re + t • C.map Complex.im, ht, ?_⟩
  intro s
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    realPart_intertwines _ _ _ (h s), imagPart_intertwines _ _ _ (h s)]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_real_invertible_pencil
#print axioms GaloisForLFunctions.HTGeometry.exists_real_simultaneous_intertwiner
