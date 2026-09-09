import GaloisForLFunctions.HTGeometry.GomesJacobiInvariantForms

/-!
# Internal flux and information lost in projective coordinates

Application of the internal-space geometry of https://arxiv.org/abs/2404.10461
and reconstruction limitations of https://arxiv.org/abs/2607.24901.
The Hermitian flux cone projects exactly to the upper half-plane. Jacobi steps
have an exact source-flux balance and Riccati imaginary-part law. Projective
coordinates forget all nonzero scalar rescalings, whereas the full flux tensor
retains the scalar squared norm. All degeneracies are included in closed statements.
-/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Real Hermitian flux of an internal two-component vector. -/
def gomesInternalFlux (v : Fin 2 → ℂ) : ℝ := (star v ⬝ᵥ (gomesJacobiFlux *ᵥ v)).re

/-- The surviving Hermitian tensor is the oriented imaginary pairing of the two components. -/
theorem gomesInternalFlux_pairing (v : Fin 2 → ℂ) :
    gomesInternalFlux v = 2*(v 0*starRingEnd ℂ (v 1)).im := by
  simp [gomesInternalFlux,gomesJacobiFlux,gomesShearAreaMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

/-- Complex rescaling has exactly its squared-norm character on internal flux. -/
theorem gomesInternalFlux_smul (c : ℂ) (v : Fin 2 → ℂ) :
    gomesInternalFlux (c • v) = Complex.normSq c * gomesInternalFlux v := by
  rw [gomesInternalFlux_pairing,gomesInternalFlux_pairing]
  simp [Complex.normSq_apply]
  ring

/-- Passing from an internal vector to its projective coordinate divides flux by its chart weight. -/
theorem gomesInternalFlux_projective (v : Fin 2 → ℂ) :
    gomesInternalFlux v = 2*Complex.normSq (v 1)*(v 0/v 1).im := by
  rw [gomesInternalFlux_pairing]
  by_cases h : v 1 = 0
  · simp [h]
  · have hn := (Complex.normSq_pos.mpr h).ne'
    simp [Complex.div_im,Complex.mul_im]
    field_simp [hn]
    ring

/-- The projective upper half-plane is exactly the positive cone of the internal flux tensor. -/
theorem gomesInternalFlux_pos_iff (v : Fin 2 → ℂ) :
    0 < gomesInternalFlux v ↔ 0 < (v 0/v 1).im := by
  rw [gomesInternalFlux_projective]
  by_cases h : v 1 = 0
  · simp [h]
  · have hp : 0 < 2*Complex.normSq (v 1) := by
      have hn := Complex.normSq_pos.mpr h
      linarith
    exact mul_pos_iff_of_pos_left hp

/-- A complex Jacobi step adds exactly the rank-one source flux to the transported old flux. -/
theorem gomesInternalFlux_jacobi_balance (a b : ℝ) (z : ℂ) (v : Fin 2 → ℂ) :
    gomesInternalFlux (gomesJacobiComplexStep a b z *ᵥ v) =
      b*gomesInternalFlux v+2*z.im*Complex.normSq (v 0) := by
  rw [gomesInternalFlux_pairing,gomesInternalFlux_pairing]
  simp [gomesJacobiComplexStep,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,Complex.normSq_apply]
  ring

/-- The induced Riccati coordinate has an exact imaginary-part balance, including zero denominators. -/
theorem gomesJacobiRiccati_im (a b : ℝ) (z w : ℂ) :
    (z-a-(b : ℂ)/w).im = z.im+b*w.im/Complex.normSq w := by
  simp [Complex.div_im]

/-- Every nonzero scalar is forgotten by all projective chart coordinates; zero is detected. -/
theorem gomesProjective_scalar_kernel (c : ℂ) :
    (∀ v : Fin 2 → ℂ, (c*v 0)/(c*v 1) = v 0/v 1) ↔ c ≠ 0 := by
  constructor
  · intro h he
    have hv := h ![1,1]
    simp [he] at hv
  · intro hc v
    by_cases hv : v 1 = 0
    · simp [hv]
    · field_simp

/-- The full flux tensor retains the scalar norm that projective coordinates forget. -/
theorem gomesInternalFlux_scalar_stabilizer (c : ℂ) :
    (∀ v : Fin 2 → ℂ, gomesInternalFlux (c • v) = gomesInternalFlux v) ↔ Complex.normSq c = 1 := by
  constructor
  · intro h
    have hv := h ![Complex.I,1]
    rw [gomesInternalFlux_smul] at hv
    simp [gomesInternalFlux_pairing] at hv
    linarith
  · intro h v
    simp [gomesInternalFlux_smul,h]

end GaloisForLFunctions.HTGeometry
