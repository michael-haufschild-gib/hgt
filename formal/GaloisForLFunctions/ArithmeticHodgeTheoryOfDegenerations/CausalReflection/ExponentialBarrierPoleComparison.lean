import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ConfiningHalfLineWeakEquation

/-!
# Polar terms against nonnegative half-line tests

On the negative half-line both hyperbolic kernels are bounded by the
same positive half-exponential. The polar mixed form therefore has a
lower bound proportional to this weighted ordinary test mass.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open _root_.RHTower
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- The actual exponential domain pairs integrably with the polar half-exponential. -/
theorem CriticalHalfLineEnergyDomain.integrable_polarExponential {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    Integrable (fun u => G u * Real.exp (-(u / 2))) := by
  apply (abs_integral_mul_kernel_le (k := fun u : ℝ => Real.exp (-(u / 2)))
    hG.weighted (by fun_prop) ?_).1
  intro u
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  linarith only [neg_le_abs u]

/-- Nonnegative tests turn the polar kernel bound into a bound by their literal weighted mass. -/
theorem CriticalHalfLineEnergyDomain.abs_polarKernel_pairing_le {G k : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hG0 : ∀ u, 0 ≤ G u)
    (hk : Continuous k) (hb : ∀ u, |k u| ≤ Real.exp (|u| / 2)) :
    |∫ u, G u * k u| ≤ ∫ u, G u * Real.exp (-(u / 2)) := by
  have hi := (abs_integral_mul_kernel_le hG.weighted hk hb).1
  calc
    _ ≤ ∫ u, |G u * k u| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => G u * k u)
    _ ≤ _ := by
      apply integral_mono hi.abs hG.integrable_polarExponential
      intro u
      rw [abs_mul, abs_of_nonneg (hG0 u)]
      by_cases hu : u ≤ 0
      · have hh := hb u
        rw [abs_of_nonpos hu, neg_div] at hh
        exact mul_le_mul_of_nonneg_left hh (hG0 u)
      · rw [hG.support u (lt_of_not_ge hu).le]
        simp only [zero_mul, le_refl]

/-- Absolute size of the two polar coefficients of a real profile. -/
def halfLinePoleReadoutSize (F : ℝ → ℝ) : ℝ :=
  2 * (|coshHalfMoment F| + |sinhHalfMoment F|)

theorem halfLinePoleReadoutSize_nonneg (F : ℝ → ℝ) : 0 ≤ halfLinePoleReadoutSize F :=
  mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Both polar contributions have a common lower bound against a nonnegative actual-domain test. -/
theorem halfLine_polarMixedForm_lower (F : ℝ → ℝ) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hG0 : ∀ u, 0 ≤ G u) :
    -halfLinePoleReadoutSize F * (∫ u, G u * Real.exp (-(u / 2))) ≤
      2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G := by
  have hc : |coshHalfMoment G| ≤ ∫ u, G u * Real.exp (-(u / 2)) :=
    hG.abs_polarKernel_pairing_le (k := fun u => Real.cosh (u / 2))
      hG0 (by fun_prop) abs_cosh_half_le_exp
  have hs : |sinhHalfMoment G| ≤ ∫ u, G u * Real.exp (-(u / 2)) :=
    hG.abs_polarKernel_pairing_le (k := fun u => Real.sinh (u / 2))
      hG0 (by fun_prop) abs_sinh_half_le_exp
  have htwo : (0 : ℝ) < 2 := by norm_num
  have h₁ : |2 * coshHalfMoment F * coshHalfMoment G| ≤
      2 * |coshHalfMoment F| * (∫ u, G u * Real.exp (-(u / 2))) := by
    simpa only [abs_mul, abs_of_pos htwo] using
      mul_le_mul_of_nonneg_left hc (mul_nonneg htwo.le (abs_nonneg (coshHalfMoment F)))
  have h₂ : |2 * sinhHalfMoment F * sinhHalfMoment G| ≤
      2 * |sinhHalfMoment F| * (∫ u, G u * Real.exp (-(u / 2))) := by
    simpa only [abs_mul, abs_of_pos htwo] using
      mul_le_mul_of_nonneg_left hs (mul_nonneg htwo.le (abs_nonneg (sinhHalfMoment F)))
  have hsum := (abs_sub (2 * coshHalfMoment F * coshHalfMoment G)
    (2 * sinhHalfMoment F * sinhHalfMoment G)).trans (add_le_add h₁ h₂)
  calc
    _ = -(2 * |coshHalfMoment F| * (∫ u, G u * Real.exp (-(u / 2))) +
        2 * |sinhHalfMoment F| * (∫ u, G u * Real.exp (-(u / 2)))) := by
      dsimp only [halfLinePoleReadoutSize]
      ring
    _ ≤ -|2 * coshHalfMoment F * coshHalfMoment G -
        2 * sinhHalfMoment F * sinhHalfMoment G| := neg_le_neg hsum
    _ ≤ _ := neg_abs_le _

#print axioms CriticalHalfLineEnergyDomain.integrable_polarExponential
#print axioms halfLine_polarMixedForm_lower
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
