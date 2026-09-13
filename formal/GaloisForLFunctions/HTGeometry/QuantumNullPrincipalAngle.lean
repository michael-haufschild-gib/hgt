import GaloisForLFunctions.HTGeometry.CollisionQuantumNullActivation

/-!
# Principal-angle diagnostics for transported quantum null spaces

The stable sine correction proposed in arXiv:2609.07645 is realized exactly on the
corpus's rotating null panel. Its squared value equals null-direction activation energy.
For collision features it multiplies the independent fractional-energy Gram determinant.
-/

set_option autoImplicit false
open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Overlap of the old and new unit null directions. -/
def rotatingNullOverlap (s t : ℝ) : ℝ :=
  ∑ i, HTGeometry.rotatingNullDirection s i * HTGeometry.rotatingNullDirection t i

/-- Numerically stable squared sine of the one-dimensional principal angle. -/
def rotatingNullSineDiagnostic (s t : ℝ) : ℝ := 1 - rotatingNullOverlap s t ^ 2

theorem rotatingNullOverlap_eq_cos_sub (s t : ℝ) :
    rotatingNullOverlap s t = Real.cos (t - s) := by
  simp [rotatingNullOverlap, HTGeometry.rotatingNullDirection, Fin.sum_univ_two, Real.cos_sub]
  ring

theorem rotatingNullSineDiagnostic_eq_sin_sq (s t : ℝ) :
    rotatingNullSineDiagnostic s t = Real.sin (t - s) ^ 2 := by
  rw [rotatingNullSineDiagnostic, rotatingNullOverlap_eq_cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq (t - s)]

/-- Stable principal-angle diagnostic is the exact old-null activation energy. -/
theorem rotatingNullSineDiagnostic_eq_activation_energy (s t : ℝ) :
    rotatingNullSineDiagnostic s t =
      ‖HTGeometry.rotatingObservation t (HTGeometry.rotatingNullDirection s)‖ ^ 2 := by
  rw [rotatingNullSineDiagnostic_eq_sin_sq, HTGeometry.rotatingObservation_null_energy]

/-- Collision QGT energy separates null-space rotation from feature distinguishability. -/
theorem collisionRotatingTangent_projective_energy_eq_sineDiagnostic
    (a e x y s t : ℝ) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionRotatingTangent a e y s t) =
      rotatingNullSineDiagnostic s t * (Real.Gamma (Real.exp a) ^ 2 *
        (collisionFractionalKernel a e x x * collisionFractionalKernel a e y y -
          collisionFractionalKernel a e x y ^ 2)) := by
  rw [collisionRotatingTangent_projective_energy,
    rotatingNullSineDiagnostic_eq_sin_sq]

end
end GaloisForLFunctions.HTGeometry
