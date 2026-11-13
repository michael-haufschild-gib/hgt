import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningFixedTrialLimit
import GaloisForLFunctions.HTGeometry.HardyBoundary.FourierNegativeLogarithmicTail

/-!
# Coercivity of the soft logarithmic half-line form

The negative logarithmic Fourier part costs at most four physical first
moments plus a fixed mass term. The linear potential retains four first
moments and the entire positive logarithmic Fourier energy.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri

theorem SoftLogarithmicHalfLineDomain.integrable_positiveLogarithm {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Integrable (fun ξ => max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) := by
  have hft := RHTower.continuous_fourier_of_integrable (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
  have hm : Measurable (fun ξ => max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) := by fun_prop
  apply hF.logarithmic.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (max_le (le_abs_self _) (abs_nonneg _)) (sq_nonneg ‖𝓕 (cx F) ξ‖)

theorem SoftLogarithmicHalfLineDomain.integrable_negativeLogarithm {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    Integrable (fun ξ => max (-Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) := by
  have hft := RHTower.continuous_fourier_of_integrable (f := cx F) (hF.integrable.ofReal (𝕜 := ℂ))
  have hm : Measurable (fun ξ => max (-Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) := by fun_prop
  apply hF.logarithmic.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (max_le (neg_le_abs _) (abs_nonneg _)) (sq_nonneg ‖𝓕 (cx F) ξ‖)

/-- Absolute logarithmic integrability permits the exact positive-minus-negative decomposition. -/
theorem SoftLogarithmicHalfLineDomain.logarithmicEnergy_eq_parts {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) :
    logarithmicFourierEnergy F =
      (∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) -
        ∫ ξ, max (-Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 := by
  change (∫ ξ, Real.log |ξ| * ‖𝓕 (cx F) ξ‖ ^ 2) = _
  calc
    _ = ∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 -
        max (-Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        by_cases hξ : 0 ≤ Real.log |ξ|
        · rw [max_eq_left hξ, max_eq_right (neg_nonpos.mpr hξ), zero_mul, sub_zero]
        · rw [max_eq_right (lt_of_not_ge hξ).le,
            max_eq_left (neg_nonneg.mpr (lt_of_not_ge hξ).le), zero_mul]
          ring
    _ = _ := integral_sub hF.integrable_positiveLogarithm hF.integrable_negativeLogarithm

/-- The limiting energy jointly controls physical confinement and positive logarithmic energy. -/
theorem SoftLogarithmicHalfLineDomain.coercive {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1) :
    (∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) +
      4 * criticalHalfLineFirstMoment F ≤ softLogarithmicHalfLineEnergy F + 16 := by
  have hmc : (∫ u, ‖cx F u‖ ^ 2) = 1 := by
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hm
  have hnegative := integral_negativeLog_fourier_le_firstMoment
    (f := cx F) (M := criticalHalfLineFirstMoment F)
    (hF.integrable.ofReal (𝕜 := ℂ)) hF.memLp_complex hmc hF.integrable_absMoment
    (le_of_eq hF.integral_absMoment)
  rw [softLogarithmicHalfLineEnergy, hF.logarithmicEnergy_eq_parts]
  linarith only [hnegative]

/-- Each nonnegative part is bounded on a unit Rayleigh sublevel. -/
theorem SoftLogarithmicHalfLineDomain.sublevel_bounds {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (hm : (∫ u, F u ^ 2) = 1)
    {E : ℝ} (hE : softLogarithmicHalfLineEnergy F ≤ E) :
    4 * criticalHalfLineFirstMoment F ≤ E + 16 ∧
      (∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2) ≤ E + 16 := by
  have hp : 0 ≤ ∫ ξ, max (Real.log |ξ|) 0 * ‖𝓕 (cx F) ξ‖ ^ 2 :=
    integral_nonneg fun ξ => mul_nonneg (le_max_right _ _) (sq_nonneg ‖𝓕 (cx F) ξ‖)
  have hM : 0 ≤ criticalHalfLineFirstMoment F := by
    rw [criticalHalfLineFirstMoment, ← hF.integral_absMoment]
    exact integral_nonneg fun u => mul_nonneg (abs_nonneg u) (sq_nonneg ‖cx F u‖)
  have hc := hF.coercive hm
  constructor <;> linarith only [hc, hE, hp, hM]

#print axioms SoftLogarithmicHalfLineDomain.logarithmicEnergy_eq_parts
#print axioms SoftLogarithmicHalfLineDomain.coercive
#print axioms SoftLogarithmicHalfLineDomain.sublevel_bounds
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
