import GaloisForLFunctions.HTGeometry.FokasLenellsJumpGeometry
import Mathlib.LinearAlgebra.Matrix.Trace
import GaloisForLFunctions.HTGeometry.Sl2ProperAdjointNormalForm

/-!
# Fokas–Lenells uniformization and nilpotent normal forms

The matrices in equations (2.6)–(2.8) of Yan–Zhang–Zhu,
*On the global well-posedness for the nonlocal Fokas-Lenells equation with the
weighted Sobolev initial data on the line*, arXiv:2607.19649v1, satisfy an
unconditional polynomial gauge identity. An exact shear conjugation removes
the first-derivative coordinate from all spectral invariants. The resulting
nilpotency classification applies the corpus's `sl₂` Jordan normal form.

These are finite-dimensional identities; no inverse-scattering reconstruction
or nonlinear existence theorem is asserted here.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The effective potential of equation (2.8); u=q_x, v=(qPT)_x, w=q_xx. -/
def effectivePotential (u v w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I*u*v/2, -I*v/2; w+I*u^(2 : ℕ)*v/2, -I*u*v/2]

/-- Lower triangular shear removing q_x from the eigenvalue invariants. -/
def potentialShear (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;u,1]

/-- The gauge matrix in equation (2.6). -/
def uniformizationGauge (u k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;u,-2*k]

def spatialLax (u v k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I*k^(2 : ℕ),I*k*v;I*k*u,-I*k^(2 : ℕ)]

def uniformizedLax (u v w z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I*z,0;0,-I*z]+effectivePotential u v w

/-- Spectral uniformization is a polynomial gauge identity, valid even before
excluding the degenerate gauge at zero. -/
theorem uniformization_identity (u v w k : ℂ) :
    !![0,0;w,0] + uniformizationGauge u k * spatialLax u v k =
      uniformizedLax u v w (k^(2 : ℕ)) * uniformizationGauge u k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizationGauge, spatialLax, uniformizedLax, effectivePotential,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_uniformizationGauge (u k : ℂ) :
    (uniformizationGauge u k).det = -2*k := by
  simp [uniformizationGauge, Matrix.det_fin_two]

/-- The first-derivative coordinate is exactly a similarity parameter. -/
theorem effectivePotential_shear (u v w : ℂ) :
    effectivePotential u v w =
      potentialShear u * effectivePotential 0 v w * potentialShear (-u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [potentialShear, effectivePotential, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem potentialShear_inverse (u : ℂ) : potentialShear u * potentialShear (-u) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [potentialShear, Matrix.mul_apply, Fin.sum_univ_two]

theorem effectivePotential_trace (u v w : ℂ) :
    (effectivePotential u v w).trace = 0 := by
  simp [effectivePotential, Matrix.trace, Fin.sum_univ_two]
  ring

theorem effectivePotential_det (u v w : ℂ) :
    (effectivePotential u v w).det = I*v*w/2 := by
  simp [effectivePotential, Matrix.det_fin_two]
  ring

/-- The full square is a scalar matrix; the nonlinear shear coordinate disappears. -/
theorem effectivePotential_square (u v w : ℂ) :
    effectivePotential u v w ^ (2 : ℕ) = (-I*v*w/2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [effectivePotential, pow_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Exact degeneracy classification in the effective potential, with no side assumptions. -/
theorem effectivePotential_square_zero_iff (u v w : ℂ) :
    effectivePotential u v w ^ (2 : ℕ) = 0 ↔ v = 0 ∨ w = 0 := by
  rw [effectivePotential_square]
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    simp at h00
    simpa using h00
  · rintro (rfl | rfl) <;> simp

/-- Every even matrix moment is independent of the first-derivative shear. -/
theorem effectivePotential_even_power (u v w : ℂ) (n : ℕ) :
    effectivePotential u v w ^ (2*n) =
      (-I*v*w/2)^n • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [pow_mul, effectivePotential_square, smul_pow, one_pow]

/-- Nilpotency has precisely the same boundary as square-zero degeneracy. -/
theorem effectivePotential_isNilpotent_iff (u v w : ℂ) :
    IsNilpotent (effectivePotential u v w) ↔ v = 0 ∨ w = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    have hd := congrArg Matrix.det hn
    simp only [Matrix.det_pow, Matrix.det_zero] at hd
    have hz : (effectivePotential u v w).det = 0 := eq_zero_of_pow_eq_zero hd
    simpa [effectivePotential_det] using hz
  · intro h
    exact ⟨2, (effectivePotential_square_zero_iff u v w).mpr h⟩

/-- Inserting the explicit nonzero exponential coordinate discharges all
side conditions in the corpus's nilpotent Jordan normal-form theorem. -/
theorem effectivePotential_nilpotent_normal_form (u a : ℂ) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) ℂ,
      P * Q = 1 ∧ Q * P = 1 ∧
      Q * effectivePotential u (Complex.exp a) 0 * P = sl2E ℂ := by
  apply exists_conj_eq_E_of_trace_eq_zero_of_det_eq_zero
  · exact effectivePotential_trace _ _ _
  · simp [effectivePotential_det]
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    simp [effectivePotential, Complex.exp_ne_zero] at h01

end
end GaloisForLFunctions.HTGeometry.FokasLenells
