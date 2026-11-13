import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningFixedTrialLimit
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier

/-!
# Real scaling of soft logarithmic trials

Real scalar multiplication preserves the trial domain. Square mass,
physical first moment, and the full logarithmic energy are homogeneous
of degree two, permitting normalization of compact recovery profiles.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri


private theorem fourier_cx_const_mul (c : ℝ) (F : ℝ → ℝ) (ξ : ℝ) :
    𝓕 (cx (fun u => c * F u)) ξ = (c : ℂ) * 𝓕 (cx F) ξ := by
  have he : cx (fun u => c * F u) = fun u => (c : ℂ) * cx F u := by
    funext u
    exact Complex.ofReal_mul c (F u)
  rw [he]
  exact HTGeometry.fourier_const_mul_apply (c : ℂ) (cx F) ξ

/-- The trial domain is stable under real scalar multiplication. -/
theorem SoftLogarithmicHalfLineDomain.const_mul {F : ℝ → ℝ}
    (hF : SoftLogarithmicHalfLineDomain F) (c : ℝ) :
    SoftLogarithmicHalfLineDomain (fun u => c * F u) := by
  refine ⟨measurable_const.mul hF.meas, hF.integrable.const_mul c, ?_, ?_, ?_, ?_⟩
  · apply (hF.sq.const_mul (c ^ 2)).congr
    exact Eventually.of_forall fun u => (mul_pow c (F u) 2).symm
  · intro u hu
    rw [hF.support u hu, mul_zero]
  · obtain ⟨β, hβ, hi⟩ := hF.exponential
    refine ⟨β, hβ, (hi.const_mul (c ^ 2)).congr ?_⟩
    exact Eventually.of_forall fun u => by dsimp only; ring
  · apply (hF.logarithmic.const_mul (c ^ 2)).congr
    exact Eventually.of_forall fun ξ => by
      change c ^ 2 * (|Real.log (|ξ|)| * ‖𝓕 (cx F) ξ‖ ^ 2) =
        |Real.log (|ξ|)| * ‖𝓕 (cx (fun u => c * F u)) ξ‖ ^ 2
      rw [fourier_cx_const_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring

/-- Square mass is homogeneous of degree two. -/
theorem integral_sq_const_mul_real (c : ℝ) (F : ℝ → ℝ) :
    (∫ u, (c * F u) ^ 2) = c ^ 2 * ∫ u, F u ^ 2 := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => mul_pow c (F u) 2

/-- The physical first moment is homogeneous of degree two. -/
theorem criticalHalfLineFirstMoment_const_mul (c : ℝ) (F : ℝ → ℝ) :
    criticalHalfLineFirstMoment (fun u => c * F u) = c ^ 2 * criticalHalfLineFirstMoment F := by
  unfold criticalHalfLineFirstMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by dsimp only; ring

/-- The full soft logarithmic energy is homogeneous of degree two. -/
theorem softLogarithmicHalfLineEnergy_const_mul (c : ℝ) (F : ℝ → ℝ) :
    softLogarithmicHalfLineEnergy (fun u => c * F u) =
      c ^ 2 * softLogarithmicHalfLineEnergy F := by
  have hl : logarithmicFourierEnergy (fun u => c * F u) =
      c ^ 2 * logarithmicFourierEnergy F := by
    unfold logarithmicFourierEnergy
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      change Real.log |ξ| * ‖𝓕 (cx (fun u => c * F u)) ξ‖ ^ 2 =
        c ^ 2 * (Real.log |ξ| * ‖𝓕 (cx F) ξ‖ ^ 2)
      rw [fourier_cx_const_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
  rw [softLogarithmicHalfLineEnergy, softLogarithmicHalfLineEnergy,
    criticalHalfLineFirstMoment_const_mul, hl]
  ring

#print axioms SoftLogarithmicHalfLineDomain.const_mul
#print axioms integral_sq_const_mul_real
#print axioms criticalHalfLineFirstMoment_const_mul
#print axioms softLogarithmicHalfLineEnergy_const_mul
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

