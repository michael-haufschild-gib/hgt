import GaloisForLFunctions.HTGeometry.QuantumNullSpaceTransport
import GaloisForLFunctions.HTGeometry.PolyatomicHilbertGeometry

/-!
# Null-direction activation in completed collision feature space

The rotating-null mechanism of arXiv:2609.07645 acts on the corpus's
actual Gamma-weighted half-line L² collision features. Its projective
energy is a product of the squared rotation sine and the existing strict
fractional-energy Gram determinant. Thus parameter rotation and distinct
squared collision energies are separate, exact requirements for visibility.
-/

open scoped InnerProductSpace
noncomputable section
namespace HTGeometry

/-- Complex rescaling of a tangent scales projective energy by squared modulus. -/
theorem projectiveGramTangentEnergy_smul_right
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) (c : ℂ) :
    projectiveGramTangentEnergy (𝕜 := ℂ) u (c • v) =
      ‖c‖ ^ 2 * projectiveGramTangentEnergy (𝕜 := ℂ) u v := by
  unfold projectiveGramTangentEnergy
  rw [norm_smul, inner_smul_right, norm_mul]
  ring

end HTGeometry
namespace GaloisForLFunctions.HTGeometry

/-- Image of an old null parameter direction under a rotated collision tangent panel. -/
def collisionRotatingTangent (a e y s t : ℝ) :=
  ((HTGeometry.rotatingObservation t (HTGeometry.rotatingNullDirection s) : ℝ) : ℂ) •
    collisionLaplaceAtom a e y

/-- Exact rotation-times-Gram decomposition in the actual half-line L² space. -/
theorem collisionRotatingTangent_projective_energy (a e x y s t : ℝ) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionRotatingTangent a e y s t) =
      Real.sin (t - s) ^ 2 * (Real.Gamma (Real.exp a) ^ 2 *
        (collisionFractionalKernel a e x x * collisionFractionalKernel a e y y -
          collisionFractionalKernel a e x y ^ 2)) := by
  unfold collisionRotatingTangent
  rw [HTGeometry.projectiveGramTangentEnergy_smul_right,
    HTGeometry.rotatingObservation_null_transport, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := HTGeometry.quantumMetricAreaValue_eq_projectiveGram_add_berry
    (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y)
  rw [collisionLaplaceAtom_berry_zero, collisionLaplaceAtom_metric_area] at h
  have he : HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionLaplaceAtom a e y) =
      Real.Gamma (Real.exp a) ^ 2 *
        (collisionFractionalKernel a e x x * collisionFractionalKernel a e y y -
          collisionFractionalKernel a e x y ^ 2) := by linarith
  rw [he]

/-- Without rotation every such parameter direction is invisible. -/
theorem collisionRotatingTangent_initial_energy (a e x y s : ℝ) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionRotatingTangent a e y s s) = 0 := by
  rw [collisionRotatingTangent_projective_energy]
  simp

/-- A quarter turn exposes precisely the unequal-squared-energy directions. -/
theorem collisionRotatingTangent_quarter_turn_positive_iff (a e x y s : ℝ) :
    0 < HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionRotatingTangent a e y s (s + Real.pi / 2)) ↔
        x ^ 2 ≠ y ^ 2 := by
  rw [collisionRotatingTangent_projective_energy]
  simp only [add_sub_cancel_left, Real.sin_pi_div_two, one_pow, one_mul]
  rw [mul_pos_iff_of_pos_left (sq_pos_of_pos (Real.Gamma_pos_of_pos (Real.exp_pos a))),
    collisionFractionalKernel_det_pos_iff]

/-- Opposite signed collision coordinates stay indistinguishable under every rotation. -/
theorem collisionRotatingTangent_sign_blind (a e x s t : ℝ) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ)
      (collisionLaplaceAtom a e x) (collisionRotatingTangent a e (-x) s t) = 0 := by
  rw [collisionRotatingTangent_projective_energy]
  simp only [collisionFractionalKernel, neg_sq]
  ring

end GaloisForLFunctions.HTGeometry
