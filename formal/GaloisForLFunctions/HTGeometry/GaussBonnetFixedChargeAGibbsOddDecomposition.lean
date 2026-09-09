import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPrefactor
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsReciprocal
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanGibbsForce

/-!
# Exact decomposition of the first asymmetric Gibbs force correction

The divided kernel difference separates coefficient drift, radial
reciprocal drift and the stationary-polynomial residual. The identity is
exact for every real coordinate, including totalized singular values.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsLinear (τ φ : ℝ) : ℝ :=
  2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ
def egbFixedChargeAGibbsResidual (τ φ : ℝ) : ℝ :=
  (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
    egbCoexistenceASymmetricRatio τ ^ 2
def egbFixedChargeAGibbsLeadingKernel (w φ t : ℝ) : ℝ :=
  4 * egbFixedChargeAGibbsBarrierCoefficient w φ * (t ^ 2 - 1) * t
def egbFixedChargeAGibbsOddKernel (w φ τ t : ℝ) : ℝ :=
  (egbFixedChargeAGibbsKernel w φ τ t - egbFixedChargeAGibbsLeadingKernel w φ t) / egbCoexistenceASymmetricRatio τ

theorem egbFixedChargeAGibbsLinear_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsLinear τ φ) atBot (𝓝 (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))) :=
  egbFixedChargeAMiddleMeanLinearCombination_limit φ

theorem egbFixedChargeAGibbsLinear_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAGibbsLinear τ φ - 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := egbFixedChargeAMiddleMeanLinearCombination_linear_limit φ

theorem egbFixedChargeAGibbsResidual_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsResidual τ φ) atBot (𝓝 (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5)) :=
  egbFixedChargeAMiddleMeanResidual_critical_limit φ

theorem egbFixedChargeAGibbsCriticalPrefactor_linear_product (w φ : ℝ) :
    egbFixedChargeAGibbsCriticalPrefactor w φ * (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) =
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbFixedChargeAGibbsCriticalPrefactor egbFixedChargeAGibbsCriticalNormalizer egbFixedChargeAGibbsBarrierCoefficient
  field_simp <;> ring

theorem egbFixedChargeAGibbsCriticalPrefactor_residual_product (w φ : ℝ) :
    egbFixedChargeAGibbsCriticalPrefactor w φ * (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) =
      -(egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanGibbsForceCoefficient φ) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  unfold egbFixedChargeAGibbsCriticalPrefactor egbFixedChargeAGibbsCriticalNormalizer egbFixedChargeAMeanGibbsForceCoefficient
  field_simp <;> ring

theorem egbFixedChargeAGibbsKernel_prefactor_formula (w φ τ t : ℝ) :
    egbFixedChargeAGibbsKernel w φ τ t = (t ^ 2 - 1) * egbFixedChargeAGibbsPrefactor w φ τ *
      egbFixedChargeAGibbsReciprocal τ t * (egbFixedChargeAGibbsLinear τ φ * t +
        egbCoexistenceASymmetricRatio τ * (egbFixedChargeAMeanPressureNumerator τ φ * t ^ 2 + egbFixedChargeAGibbsResidual τ φ)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hpoly : egbFixedChargeAGibbsLinear τ φ * t + egbCoexistenceASymmetricRatio τ *
      (egbFixedChargeAMeanPressureNumerator τ φ * t ^ 2 + egbFixedChargeAGibbsResidual τ φ) =
      egbFixedChargeABarrierPolynomial τ φ t := by
    unfold egbFixedChargeAGibbsLinear egbFixedChargeAGibbsResidual egbFixedChargeABarrierPolynomial
    field_simp <;> ring
  rw [hpoly]
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have h2 : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 := by positivity
  by_cases hv : 1 + egbCoexistenceASymmetricRatio τ * t = 0
  · simp only [egbFixedChargeAGibbsKernel, egbFixedChargeAGibbsReciprocal, hv,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, div_zero, zero_mul]
  · unfold egbFixedChargeAGibbsKernel egbFixedChargeAGibbsPrefactor egbFixedChargeAGibbsNormalizer egbFixedChargeAGibbsReciprocal
    field_simp [hv] <;> ring

theorem egbFixedChargeAGibbsOddKernel_decomposition (w φ τ t : ℝ) :
    egbFixedChargeAGibbsOddKernel w φ τ t = (t ^ 2 - 1) *
      (((egbFixedChargeAGibbsPrefactor w φ τ - egbFixedChargeAGibbsCriticalPrefactor w φ) / egbCoexistenceASymmetricRatio τ) *
          egbFixedChargeAGibbsReciprocal τ t * egbFixedChargeAGibbsLinear τ φ * t +
        egbFixedChargeAGibbsCriticalPrefactor w φ *
          ((egbFixedChargeAGibbsLinear τ φ - 4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) / egbCoexistenceASymmetricRatio τ) *
          egbFixedChargeAGibbsReciprocal τ t * t +
        egbFixedChargeAGibbsCriticalPrefactor w φ * (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ)) * t *
          ((egbFixedChargeAGibbsReciprocal τ t - 1) / egbCoexistenceASymmetricRatio τ) +
        egbFixedChargeAGibbsPrefactor w φ τ * egbFixedChargeAGibbsReciprocal τ t *
          (egbFixedChargeAMeanPressureNumerator τ φ * t ^ 2 + egbFixedChargeAGibbsResidual τ φ)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAGibbsOddKernel egbFixedChargeAGibbsLeadingKernel
  rw [egbFixedChargeAGibbsKernel_prefactor_formula, ← egbFixedChargeAGibbsCriticalPrefactor_linear_product]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
