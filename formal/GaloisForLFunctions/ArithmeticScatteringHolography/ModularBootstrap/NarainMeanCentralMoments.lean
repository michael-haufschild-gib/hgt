import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanSchwartzSource
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful

/-!
# Physical logarithmic moments of the Narain remainder

The logarithmic Jacobian identifies all physical central moments with Schwartz clock moments and gives the vanishing zeroth sum rule.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The physical logarithmic moment density at the central Mellin boundary. -/
def narainMeanMomentDensity (Y Z : Height) (n : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (-3 / 2 : ℂ) * (Real.log y : ℂ) ^ n *
    ((y : ℂ) * narainScalarHeatAverage Y Z y +
      (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)

/-- The logarithmic Jacobian converts the physical density to its Schwartz clock moment. -/
theorem exp_smul_narainMeanMomentDensity (Y Z : Height) (n : ℕ) (u : ℝ) :
    Real.exp u • narainMeanMomentDensity Y Z n (Real.exp u) =
      (u : ℂ) ^ n * narainMeanClockSchwartz Y Z (-u) := by
  have hy : (Real.exp u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos u).ne'
  have hcoef : (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-3 / 2 : ℂ) =
      (Real.exp (-u / 2) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hy, ← Complex.ofReal_log (Real.exp_pos u).le,
      Real.log_exp, Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [narainMeanMomentDensity, Real.log_exp, Complex.real_smul,
    narainMeanClockSchwartz_apply, neg_neg]
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add]
  calc
    _ = ((Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-3 / 2 : ℂ)) *
        ((u : ℂ) ^ n * ((Real.exp u : ℂ) * narainScalarHeatAverage Y Z (Real.exp u) +
          (3 / (Real.pi : ℂ)) * (u : ℂ) - narainAverageConstant Y Z)) := by ring
    _ = _ := by rw [hcoef]; ring

/-- Every absolute logarithmic moment of the actual remainder exists on the full positive axis. -/
theorem integrableOn_narainMeanMomentDensity (Y Z : Height) (n : ℕ) :
    IntegrableOn (narainMeanMomentDensity Y Z n) (Ioi (0 : ℝ)) := by
  rw [integrableOn_Ioi_iff_integrable_exp_smul]
  have hmoment : Integrable (fun L : ℝ => ((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L) := by
    apply ((narainMeanClockSchwartz Y Z).integrable_pow_mul volume n).mono'
      (((continuous_ofReal.comp continuous_neg).pow n).mul
        (narainMeanClockSchwartz Y Z).continuous).aestronglyMeasurable
    filter_upwards [] with L
    change ‖((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L‖ ≤
      ‖L‖ ^ n * ‖narainMeanClockSchwartz Y Z L‖
    simp only [norm_mul, norm_pow, Complex.norm_real, norm_neg, le_refl]
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hmoment
  change Integrable (fun u : ℝ => ((-(-u) : ℝ) : ℂ) ^ n *
    narainMeanClockSchwartz Y Z (-u)) at hneg
  simpa only [neg_neg, exp_smul_narainMeanMomentDensity] using hneg

/-- The physical and logarithmic-clock moments agree, including the reflection sign. -/
theorem integral_narainMeanMomentDensity_eq_clock (Y Z : Height) (n : ℕ) :
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity Y Z n y) =
      ∫ L : ℝ, ((-L : ℝ) : ℂ) ^ n * narainMeanClockSchwartz Y Z L := by
  rw [integral_Ioi_eq_integral_exp_smul]
  simp_rw [exp_smul_narainMeanMomentDensity]
  simpa only [neg_neg] using
    (integral_neg_eq_self (fun u : ℝ => (u : ℂ) ^ n * narainMeanClockSchwartz Y Z (-u)) volume).symm

/-- The removable central zero gives an absolutely convergent physical sum rule. -/
theorem integral_narainMeanMomentDensity_zero (Y Z : Height) :
    (∫ y in Ioi (0 : ℝ), narainMeanMomentDensity Y Z 0 y) = 0 := by
  rw [integral_narainMeanMomentDensity_eq_clock]
  simpa only [pow_zero, one_mul] using integral_narainMeanClockSchwartz Y Z

/-- The literal vacuum-subtracted average has zero central weighted integral. -/
theorem integral_narainScalarHeatAverage_central_remainder (Y Z : Height) :
    (∫ y in Ioi (0 : ℝ), (y : ℂ) ^ (-3 / 2 : ℂ) *
      ((y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z)) = 0 := by
  simpa only [narainMeanMomentDensity, pow_zero, mul_one] using integral_narainMeanMomentDensity_zero Y Z

#print axioms exp_smul_narainMeanMomentDensity
#print axioms integrableOn_narainMeanMomentDensity
#print axioms integral_narainMeanMomentDensity_eq_clock
#print axioms integral_narainScalarHeatAverage_central_remainder
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
