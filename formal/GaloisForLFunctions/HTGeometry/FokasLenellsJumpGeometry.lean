import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import GaloisForLFunctions.HTGeometry.DispersivePDE.Profiles


/-!
# Exact accretivity geometry of the nonlocal Fokas–Lenells jump

For `J(a,b) = [[1,b],[-a,1-ab]]`, completing a complex square gives the exact
open-disk and closed-disk criteria for positive and nonnegative Hermitian energy.
This sharpens the algebraic mechanism in Proposition 3.4 of Yan–Zhang–Zhu,
*On the global well-posedness for the nonlocal Fokas–Lenells equation*,
arXiv:2607.19649. The coefficients are independent; no Hermitian reduction is assumed.

The corpus's hyperbolic soliton profiles give unconditional examples, with
`sech² x` as the sharp energy constant on the equal-coordinate slice.
-/

namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
open Complex Matrix

def jump (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, b; -a, 1-a*b]
def inverseJump (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1-a*b, -b; a, 1]
def energy (a b u v : ℂ) : ℝ :=
  (star u * (u+b*v) + star v * (-a*u+(1-a*b)*v)).re

theorem det_jump (a b : ℂ) : (jump a b).det = 1 := by
  simp [jump, Matrix.det_fin_two]
  ring

theorem jump_mul_inverse (a b : ℂ) : jump a b * inverseJump a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jump, inverseJump, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem energy_completion (a b u v : ℂ) :
    energy a b u v =
      normSq (u + (b-star a)/2*v) + (1-normSq (a+star b)/4)*normSq v := by
  simp [energy, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem energy_test (a b : ℂ) :
    energy a b (-(b-star a)/2) 1 = 1-normSq (a+star b)/4 := by
  rw [energy_completion]
  simp
  ring

/-- Strict accretivity is exactly a disk condition on the sum of the two independent
reflection coefficients, with conjugation on the second coefficient. -/
theorem positive_iff (a b : ℂ) :
    (∀ u v : ℂ, u ≠ 0 ∨ v ≠ 0 → 0 < energy a b u v) ↔
      ‖a + star b‖ < 2 := by
  constructor
  · intro h
    have he := h (-(b-star a)/2) 1 (Or.inr one_ne_zero)
    rw [energy_test, Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg (a+star b)]
  · intro h u v huv
    have hc : 0 < 1-normSq (a+star b)/4 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg (a+star b)]
    rw [energy_completion]
    by_cases hv : v = 0
    · subst v
      simpa using (Complex.normSq_pos.mpr (huv.resolve_right (not_ne_iff.mpr rfl)))
    · exact add_pos_of_nonneg_of_pos (normSq_nonneg _)
        (mul_pos hc (Complex.normSq_pos.mpr hv))

/-- The closed disk is the exact boundary for nonnegative jump energy. -/
theorem nonnegative_iff (a b : ℂ) :
    (∀ u v : ℂ, 0 ≤ energy a b u v) ↔ ‖a + star b‖ ≤ 2 := by
  constructor
  · intro h
    have he := h (-(b-star a)/2) 1
    rw [energy_test, Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg (a+star b)]
  · intro h u v
    rw [energy_completion]
    apply add_nonneg (normSq_nonneg _)
    apply mul_nonneg _ (normSq_nonneg _)
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (a+star b)]

/-- Real hyperbolic soliton coordinates provide strictly accretive jumps at every
pair of positions, without a smallness premise. -/
theorem soliton_positive (x y : ℝ) :
    ∀ u v : ℂ, u ≠ 0 ∨ v ≠ 0 →
      0 < energy (DispersivePDE.solitonT x) (DispersivePDE.solitonT y) u v := by
  apply (positive_iff _ _).mpr
  simp only [DispersivePDE.solitonT, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_add,
    Complex.norm_real, Real.norm_eq_abs]
  rw [abs_lt]
  constructor <;> linarith [Real.neg_one_lt_tanh x, Real.neg_one_lt_tanh y,
    Real.tanh_lt_one x, Real.tanh_lt_one y]

/-- The equal-coordinate hyperbolic slice has exactly the corpus's sech-squared
soliton as its transverse energy. -/
theorem soliton_energy (x : ℝ) (u v : ℂ) :
    energy (DispersivePDE.solitonT x) (DispersivePDE.solitonT x) u v =
      normSq u + DispersivePDE.solitonQ x * normSq v := by
  rw [energy_completion]
  simp only [DispersivePDE.solitonQ, Complex.star_def, Complex.conj_ofReal,
    sub_self, zero_div, zero_mul, add_zero]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The scalar energy is exactly the real part of the matrix quadratic form. -/
theorem energy_eq_matrix (a b u v : ℂ) :
    energy a b u v = (star ![u,v] ⬝ᵥ (jump a b *ᵥ ![u,v])).re := by
  simp [energy, jump, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The transverse soliton profile is the sharp lower energy constant. -/
theorem soliton_coercivity (x : ℝ) (u v : ℂ) :
    0 < DispersivePDE.solitonQ x ∧
    DispersivePDE.solitonQ x * (normSq u + normSq v) ≤
      energy (DispersivePDE.solitonT x) (DispersivePDE.solitonT x) u v ∧
    energy (DispersivePDE.solitonT x) (DispersivePDE.solitonT x) 0 1 =
      DispersivePDE.solitonQ x := by
  refine ⟨?_, ?_, ?_⟩
  · rw [DispersivePDE.solitonQ_eq_inv_cosh_sq]
    positivity
  · rw [soliton_energy]
    have hle : DispersivePDE.solitonQ x ≤ 1 := by
      unfold DispersivePDE.solitonQ
      nlinarith [sq_nonneg (DispersivePDE.solitonT x)]
    nlinarith [normSq_nonneg u]
  · rw [soliton_energy]
    simp

end
end GaloisForLFunctions.HTGeometry.FokasLenells
