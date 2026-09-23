import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticAngularSource
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Helicity factorization of the existing quadratic Einstein source

The separation of angular tensors from physical coefficients in §3 of
arXiv:2608.29825 suggests diagonalizing the angular rotation already present in
the corpus's quadratic source. The two helicities diagonalize that rotation;
the gradient-square tensor carries exactly twice the input rotation angle.
The final identities act on the actual Einstein second variation. Real
exponential coordinates discharge all background nondegeneracy conditions.
-/

open Complex
namespace RHTower.D4BMQuadraticAngularSource
noncomputable section

/-- Positive helicity of the corpus's diagonal-difference/off-diagonal tensor. -/
def collisionHelicityPlus (T : ℂ × ℂ) : ℂ := T.1 + 2 * I * T.2

/-- Negative helicity of the same tensor. -/
def collisionHelicityMinus (T : ℂ × ℂ) : ℂ := T.1 - 2 * I * T.2

/-- Both helicities together retain the entire angular tensor. -/
theorem collisionHelicity_reconstruct (T : ℂ × ℂ) :
    ((collisionHelicityPlus T + collisionHelicityMinus T) / 2,
      (collisionHelicityPlus T - collisionHelicityMinus T) / (4 * I)) = T := by
  ext <;> dsimp [collisionHelicityPlus, collisionHelicityMinus]
  · ring
  · field_simp
    ring

/-- The two circular components diagonalize the existing angular rotation. -/
theorem collisionHelicity_rotate (T : ℂ × ℂ) :
    collisionHelicityPlus (rotatePair T) = -I * collisionHelicityPlus T ∧
    collisionHelicityMinus (rotatePair T) = I * collisionHelicityMinus T := by
  constructor <;> dsimp [collisionHelicityPlus, collisionHelicityMinus, rotatePair] <;>
    ring_nf <;> simp [sub_eq_add_neg]

/-- The gradient-square angular tensor is a pure square in each helicity. -/
theorem collisionHelicity_gradient (x y : ℂ) :
    collisionHelicityPlus (gradientPair x y) = (x + I * y)^(2 : ℕ) ∧
    collisionHelicityMinus (gradientPair x y) = (x - I * y)^(2 : ℕ) := by
  constructor <;> dsimp [collisionHelicityPlus, collisionHelicityMinus, gradientPair] <;>
    ring_nf <;> simp [sub_eq_add_neg]

/-- An actual planar rotation on the two gradient components. -/
def collisionRotateGradient (θ : ℝ) (x y : ℂ) : ℂ × ℂ :=
  (Real.cos θ * x - Real.sin θ * y, Real.sin θ * x + Real.cos θ * y)

/-- The quadratic angular channel carries the square of the spin-one character. -/
theorem collisionHelicity_gradient_rotation (θ : ℝ) (x y : ℂ) :
    collisionHelicityPlus (gradientPair (collisionRotateGradient θ x y).1
      (collisionRotateGradient θ x y).2) =
      ((Real.cos θ : ℂ) + I * Real.sin θ)^(2 : ℕ) * collisionHelicityPlus (gradientPair x y) ∧
    collisionHelicityMinus (gradientPair (collisionRotateGradient θ x y).1
      (collisionRotateGradient θ x y).2) =
      ((Real.cos θ : ℂ) - I * Real.sin θ)^(2 : ℕ) * collisionHelicityMinus (gradientPair x y) := by
  rw [(collisionHelicity_gradient _ _).1, (collisionHelicity_gradient _ _).2,
    (collisionHelicity_gradient x y).1, (collisionHelicity_gradient x y).2]
  dsimp [collisionRotateGradient]
  constructor <;> ring_nf <;> simp <;> ring

/-- Positive helicity factors the actual source into two angular amplitudes,
with all radial/physical coefficients explicit. -/
theorem angularCoefficient_collisionHelicityPlus
    (ρ η : ℝ) (s B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    let r : ℂ := (1 + Real.exp ρ : ℝ)
    let y : ℂ := (Real.exp η : ℝ)
    collisionHelicityPlus
      (angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) =
      B^(2 : ℕ) * ((2*aS^(2 : ℕ)*scalarWeight s r - I*aS*aV*mixedWeight s r) *
        collisionHelicityPlus (hessianPair s y S Sx Sy Sxx Sxy) +
        (aS^(2 : ℕ)*scalarWeight s r - I*aS*aV*mixedWeight s r + aV^(2 : ℕ)*vectorWeight s r) *
          (Sx + I*Sy)^(2 : ℕ)) := by
  dsimp only
  have hr : ((1 + Real.exp ρ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hy : ((Real.exp η : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero η)
  have hf : ((1 + Real.exp ρ : ℝ) : ℂ)^(2 : ℕ) - 1 ≠ 0 := by
    norm_cast
    nlinarith [Real.exp_pos ρ, sq_nonneg (Real.exp ρ)]
  rw [angularCoefficient_decomposition _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf]
  dsimp [collisionHelicityPlus, rotatePair, gradientPair]
  ring_nf
  simp [sub_eq_add_neg]

/-- Negative helicity gives the companion exact factorization of the same source. -/
theorem angularCoefficient_collisionHelicityMinus
    (ρ η : ℝ) (s B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    let r : ℂ := (1 + Real.exp ρ : ℝ)
    let y : ℂ := (Real.exp η : ℝ)
    collisionHelicityMinus
      (angularCoefficient s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) =
      B^(2 : ℕ) * ((2*aS^(2 : ℕ)*scalarWeight s r + I*aS*aV*mixedWeight s r) *
        collisionHelicityMinus (hessianPair s y S Sx Sy Sxx Sxy) +
        (aS^(2 : ℕ)*scalarWeight s r + I*aS*aV*mixedWeight s r + aV^(2 : ℕ)*vectorWeight s r) *
          (Sx - I*Sy)^(2 : ℕ)) := by
  dsimp only
  have hr : ((1 + Real.exp ρ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  have hy : ((Real.exp η : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero η)
  have hf : ((1 + Real.exp ρ : ℝ) : ℂ)^(2 : ℕ) - 1 ≠ 0 := by
    norm_cast
    nlinarith [Real.exp_pos ρ, sq_nonneg (Real.exp ρ)]
  rw [angularCoefficient_decomposition _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hf]
  dsimp [collisionHelicityMinus, rotatePair, gradientPair]
  ring_nf
  simp [sub_eq_add_neg]

end
end RHTower.D4BMQuadraticAngularSource
