import GaloisForLFunctions.HTGeometry.QNMQuadraticPencil

/-!
# QNMLorentzAuxiliary

The Maxwell--Lorentz auxiliary-field equations of Al Sheikh--Jaramillo,
arXiv:2607.25133, equations (13)--(18), fit the exact quadratic companion
construction. The plane-wave dispersion determinant stays meaningful at
material poles, where eliminating the polarization by division would fail.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def qnmLorentzStiffness (L : E →ₗ[ℂ] E) (g w : ℂ) : E × E →ₗ[ℂ] E × E :=
  schurBlockOperator L 0 (g • LinearMap.id) (-(w ^ 2) • LinearMap.id)

def qnmLorentzDamping (L : E →ₗ[ℂ] E) (d : ℂ) : E × E →ₗ[ℂ] E × E :=
  schurBlockOperator L 0 0 (-d • LinearMap.id)

def qnmLorentzMass (W : E →ₗ[ℂ] E) (mu : ℂ) : E × E →ₗ[ℂ] E × E :=
  schurBlockOperator W (mu • LinearMap.id) 0 LinearMap.id

theorem qnmLorentzQuadratic_residual (L1 L2 W : E →ₗ[ℂ] E)
    (g w d mu z : ℂ) (f p : E) :
    qnmQuadraticPencil (qnmLorentzStiffness L1 g w)
      (qnmLorentzDamping L2 d) (qnmLorentzMass W mu) z (f, p) =
      (L1 f + z • L2 f - z ^ 2 • (W f + mu • p),
        g • f - (z ^ 2 + d * z + w ^ 2) • p) := by
  apply Prod.ext
  · simp [qnmQuadraticPencil, qnmLorentzStiffness, qnmLorentzDamping,
      qnmLorentzMass, Prod.smul_mk]
  · simp [qnmQuadraticPencil, qnmLorentzStiffness, qnmLorentzDamping,
      qnmLorentzMass, Prod.smul_mk]
    module

def qnmLorentzDispersionMatrix (k eps mu g d w z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-k ^ 2 - eps * z ^ 2, -mu * z ^ 2;
    g, -(z ^ 2 + d * z + w ^ 2)]

theorem qnmLorentzDispersionMatrix_det (k eps mu g d w z : ℂ) :
    (qnmLorentzDispersionMatrix k eps mu g d w z).det =
      (k ^ 2 + eps * z ^ 2) * (z ^ 2 + d * z + w ^ 2) + mu * g * z ^ 2 := by
  simp [qnmLorentzDispersionMatrix, Matrix.det_fin_two]
  ring

theorem qnmLorentzDispersion_material_pole (k eps mu g d w z : ℂ) :
    z ^ 2 + d * z + w ^ 2 = 0 ∧
      (qnmLorentzDispersionMatrix k eps mu g d w z).det = 0 ↔
    z ^ 2 + d * z + w ^ 2 = 0 ∧ (mu = 0 ∨ g = 0 ∨ z = 0) := by
  rw [qnmLorentzDispersionMatrix_det]
  constructor
  · rintro ⟨h, hd⟩
    simp only [h, mul_zero, zero_add, mul_eq_zero, sq_eq_zero_iff] at hd
    exact ⟨h, by tauto⟩
  · rintro ⟨h, hd⟩
    refine ⟨h, ?_⟩
    rw [h, mul_zero, zero_add]
    rcases hd with rfl | rfl | rfl <;> simp

theorem qnmLorentz_frequency_dictionary (d w omega : ℂ) :
    (-Complex.I * omega) ^ 2 + d * (-Complex.I * omega) + w ^ 2 =
      -(omega ^ 2 + Complex.I * d * omega - w ^ 2) := by
  have hI := Complex.I_sq
  calc
    _ = Complex.I ^ 2 * omega ^ 2 - Complex.I * d * omega + w ^ 2 := by ring
    _ = _ := by rw [hI]; ring

end GaloisForLFunctions.HTGeometry
