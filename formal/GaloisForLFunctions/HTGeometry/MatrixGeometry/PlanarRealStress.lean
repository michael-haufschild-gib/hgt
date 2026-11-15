import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The real stress of two trace-free planar Hessians

The real and imaginary parts of `[[a,b],[b,-a]]` are symmetric trace-free real
Hessians. Stacking them gives a four-by-two real matrix whose two columns are
orthogonal and have the same squared length. Its target Gram matrix has aperture
one half: subtracting it from half its trace times the identity is another Gram
matrix. This gives the planar target-stress estimate used in Luchese's regularity
argument (https://arxiv.org/abs/2611.17317), with an explicit positive factorization.
-/

open Matrix
open scoped ComplexOrder

namespace HTGeometry.PlanarRealStress

/-- A complex symmetric trace-free planar matrix. -/
def spinMatrix (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a,b; b,-a]

/-- Stack real and imaginary parts, retaining the real two-dimensional domain. -/
def stack (H : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![(H 0 0).re, (H 0 1).re; (H 1 0).re, (H 1 1).re;
      (H 0 0).im, (H 0 1).im; (H 1 0).im, (H 1 1).im]

/-- The two real derivative columns of the complex spin-two matrix. -/
def frame (a b : ℂ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![a.re, b.re; b.re, -a.re; a.im, b.im; b.im, -a.im]

theorem stack_spinMatrix (a b : ℂ) : stack (spinMatrix a b) = frame a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stack, spinMatrix, frame]

/-- The other two columns of the scalar orthogonal completion. -/
def complement (a b : ℂ) : Matrix (Fin 4) (Fin 2) ℝ :=
  !![a.im, b.im; -b.im, a.im; -a.re, -b.re; b.re, -a.re]

/-- Squared length of either real derivative column. -/
def energy (a b : ℂ) : ℝ := a.re^2 + a.im^2 + b.re^2 + b.im^2

theorem energy_eq_normSq (a b : ℂ) : energy a b = Complex.normSq a + Complex.normSq b := by
  simp only [energy, Complex.normSq_apply, pow_two]
  ring

/-- Target stress of the stacked Hessians. -/
def stress (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℝ := frame a b * (frame a b)ᵀ

/-- The frame and its complement resolve a scalar multiple of the identity. -/
theorem frame_complement (a b : ℂ) :
    frame a b * (frame a b)ᵀ + complement a b * (complement a b)ᵀ =
      energy a b • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  all_goals simp [frame, complement, energy]
  all_goals ring

/-- Domain columns are orthogonal with identical squared length. -/
theorem frame_domain_gram (a b : ℂ) :
    (frame a b)ᵀ * frame a b = energy a b • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases i <;> fin_cases j
  all_goals simp [frame, energy]
  all_goals ring

theorem stress_trace (a b : ℂ) : (stress a b).trace = 2 * energy a b := by
  rw [stress, Matrix.trace_mul_comm, frame_domain_gram, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
  ring

theorem stress_posSemidef (a b : ℂ) : (stress a b).PosSemidef := by
  simpa only [stress, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (frame a b)

/-- Exact positive complement behind the one-half aperture bound. -/
theorem stress_complement (a b : ℂ) :
    energy a b • (1 : Matrix (Fin 4) (Fin 4) ℝ) - stress a b =
      complement a b * (complement a b)ᵀ := by
  rw [← frame_complement, stress, add_sub_cancel_left]

/-- The stress is bounded above by half its trace times the identity. -/
theorem stress_aperture_half (a b : ℂ) :
    (((stress a b).trace / 2) • (1 : Matrix (Fin 4) (Fin 4) ℝ) - stress a b).PosSemidef := by
  have he : (stress a b).trace / 2 = energy a b := by rw [stress_trace]; ring
  rw [he, stress_complement]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (complement a b)

/-- Both frame columns satisfy the eigenvector equation at half the stress trace. -/
theorem stress_mul_frame (a b : ℂ) : stress a b * frame a b = energy a b • frame a b := by
  rw [stress, Matrix.mul_assoc, frame_domain_gram, Matrix.mul_smul, Matrix.mul_one]

#print axioms stress_aperture_half
#print axioms stress_mul_frame

end HTGeometry.PlanarRealStress
