import GaloisForLFunctions.HTGeometry.MatrixGeometry.PlanarRealStress
import Mathlib.Tactic.Linarith
/-!
# The exact boundary of complex planar aperture

For a complex symmetric trace-free planar matrix `H`, the half-trace bound on
`H Hᴴ` holds exactly when its two spin coefficients have aligned real phases:
`Im(conj(a) b) = 0`. The real stacked stress has the half-trace bound without
this restriction, by `PlanarRealStress`. Keeping the real domain is therefore
essential when applying the trace-free Hessian aperture argument.
-/

open Matrix
open scoped ComplexOrder
namespace HTGeometry.PlanarRealStress

/-- Signed area of the two spin coefficients in the complex plane. -/
def phase (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

/-- Target stress formed using the complex adjoint. -/
def complexStress (a b : ℂ) := spinMatrix a b * (spinMatrix a b)ᴴ

/-- The entire non-scalar stress is measured by the relative spin phase. -/
theorem complexStress_shape (a b : ℂ) : complexStress a b =
    !![(energy a b : ℂ), -2 * Complex.I * (phase a b : ℂ);
       2 * Complex.I * (phase a b : ℂ), (energy a b : ℂ)] := by
  ext i j
  simp only [complexStress, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  all_goals apply Complex.ext
  all_goals simp [spinMatrix, energy, phase, pow_two, Complex.mul_re, Complex.mul_im]
  all_goals ring

theorem complexStress_trace (a b : ℂ) :
    (complexStress a b).trace = 2 * (energy a b : ℂ) := by
  rw [complexStress_shape]
  simp [Matrix.trace, Fin.sum_univ_two, two_mul]

/-- The half-energy complement vanishes exactly at phase alignment. -/
theorem complexComplement_zero_iff (a b : ℂ) :
    (energy a b : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - complexStress a b = 0 ↔
      phase a b = 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (M 0 1).im) h
    simp [complexStress_shape, Complex.mul_re, Complex.mul_im] at he
    linarith only [he]
  · intro h
    rw [complexStress_shape, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The complex half-trace aperture has precisely the phase-aligned locus. -/
theorem complexStress_aperture_half_iff (a b : ℂ) :
    (((complexStress a b).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
      complexStress a b).PosSemidef ↔ phase a b = 0 := by
  have he : (complexStress a b).trace / 2 = (energy a b : ℂ) := by
    rw [complexStress_trace]; ring
  rw [he]
  constructor
  · intro h
    apply (complexComplement_zero_iff a b).mp
    apply h.trace_eq_zero_iff.mp
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, complexStress_trace]
    simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
    ring
  · intro h
    rw [(complexComplement_zero_iff a b).mpr h]
    exact Matrix.PosSemidef.zero

/-- Orthogonal complex spin phases violate the complex half-trace aperture. -/
theorem complexStress_one_I_not_aperture_half :
    ¬ (((complexStress 1 Complex.I).trace / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ) - complexStress 1 Complex.I).PosSemidef := by
  rw [complexStress_aperture_half_iff]
  simp [phase]

/-- The phase obstruction is the imaginary part of the Hermitian spin pairing. -/
theorem phase_eq_im_conj_mul (a b : ℂ) : phase a b = ((starRingEnd ℂ) a * b).im := by
  simp [phase, Complex.mul_im]
  ring

#print axioms complexStress_aperture_half_iff
#print axioms complexStress_one_I_not_aperture_half

end HTGeometry.PlanarRealStress
