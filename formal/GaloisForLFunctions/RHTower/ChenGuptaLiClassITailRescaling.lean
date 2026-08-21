/-
# Chen--Gupta--Li Class-I shifted-tail bounded coefficients

Closed normalization of the exact weighted shifted-tail character block. The
normalization is deterministic and leaves no coefficient-bound premise for
the subsequent large-value layer.
-/
import GaloisForLFunctions.RHTower.ChenGuptaLiClassITailCharacterBlock

open Complex
open scoped InnerProductSpace

noncomputable section
namespace RHTower

/-- Deterministic positive normalization for an exact weighted shifted-tail
dyadic coefficient vector. -/
def cglShiftedTailDyadicCoefficientScale
    (X N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) : ℝ :=
  (1 + ‖cglShiftedTailDyadicCoefficients X N s x‖)⁻¹

/-- The exact CGL shifted-tail dyadic coefficient vector after closed
normalization. -/
def cglShiftedTailDyadicScaledCoefficients
    (X N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    EuclideanSpace ℂ (Fin N) :=
  (cglShiftedTailDyadicCoefficientScale X N s x : ℂ) •
    cglShiftedTailDyadicCoefficients X N s x

/-- The closed normalization puts the entire exact shifted-tail coefficient
vector in the unit ball. -/
theorem norm_cglShiftedTailDyadicScaledCoefficients_le_one
    (X N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    ‖cglShiftedTailDyadicScaledCoefficients X N s x‖ ≤ 1 := by
  let A : ℝ := ‖cglShiftedTailDyadicCoefficients X N s x‖
  have hA : 0 ≤ A := norm_nonneg _
  have hpos : 0 < 1 + A := by linarith
  have hscale : 0 ≤ cglShiftedTailDyadicCoefficientScale X N s x := by
    simp only [cglShiftedTailDyadicCoefficientScale]
    positivity
  change ‖(cglShiftedTailDyadicCoefficientScale X N s x : ℂ) •
    cglShiftedTailDyadicCoefficients X N s x‖ ≤ 1
  rw [norm_smul]
  simp only [Complex.norm_real]
  rw [Real.norm_of_nonneg hscale]
  change cglShiftedTailDyadicCoefficientScale X N s x * A ≤ 1
  rw [cglShiftedTailDyadicCoefficientScale]
  calc
    (1 + A)⁻¹ * A = A / (1 + A) := by ring
    _ ≤ 1 := (div_le_one₀ hpos).mpr (by linarith)

/-- Every normalized exact shifted-tail dyadic coefficient has norm at most
one. -/
theorem norm_cglShiftedTailDyadicScaledCoefficient_le_one
    (X N : ℕ) (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale)
    (j : Fin N) :
    ‖(cglShiftedTailDyadicScaledCoefficients X N s x) j‖ ≤ 1 := by
  have hvector := norm_cglShiftedTailDyadicScaledCoefficients_le_one X N s x
  have hsq : ‖(cglShiftedTailDyadicScaledCoefficients X N s x) j‖ ^ 2 ≤
      ‖cglShiftedTailDyadicScaledCoefficients X N s x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.single_le_sum (fun i hi => sq_nonneg
      ‖(cglShiftedTailDyadicScaledCoefficients X N s x) i‖) (Finset.mem_univ _)
  nlinarith [norm_nonneg ((cglShiftedTailDyadicScaledCoefficients X N s x) j),
    norm_nonneg (cglShiftedTailDyadicScaledCoefficients X N s x)]

/-- The normalized exact weighted shifted-tail character polynomial. -/
def cglShiftedTailDyadicScaledPolynomial
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) : ℂ :=
  cglCharacterDyadicPolynomial N (q + 1) (cglShiftedTailDyadicRow χ s)
    (cglShiftedTailDyadicScaledCoefficients X N s x)

/-- The normalized exact shifted-tail character polynomial is its positive
deterministic scale times the literal finite tail block. -/
theorem cglShiftedTailDyadicScaledPolynomial_eq_scale_mul
    (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : CGLRightHalfPlanePoint) (x : CGLPositiveSmoothingScale) :
    cglShiftedTailDyadicScaledPolynomial X N q χ s x =
      (cglShiftedTailDyadicCoefficientScale X N s x : ℂ) *
        cglCharacterDyadicPolynomial N (q + 1) (cglShiftedTailDyadicRow χ s)
          (cglShiftedTailDyadicCoefficients X N s x) := by
  simp only [cglShiftedTailDyadicScaledPolynomial,
    cglCharacterDyadicPolynomial, cglShiftedTailDyadicScaledCoefficients,
    PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end RHTower
