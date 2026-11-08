import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralSymmetry
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralCubicJet
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralCurvature
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralLogJet
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

/-!
# The unique exceptional Narain height

The first central jet vanishes at exactly one positive height. Its third jet is nonzero by the strict logarithmic xi curvature at one.
-/

open Complex RHTower
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The unique target height at which the first filled-numerator jet vanishes. -/
def narainExceptionalHeight : Height :=
  ⟨Real.exp (2 - 4 * (deriv xi 1).re), Real.exp_pos _⟩

private theorem xi_deriv_one_real : ((deriv xi 1).re : ℂ) = deriv xi 1 := by
  have h := congrArg Complex.im (xi_deriv_conj 1)
  simp only [map_one, Complex.conj_im] at h
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    linarith only [h]

theorem narainExceptionalHeight_log :
    Complex.log (narainExceptionalHeight.val : ℂ) = 2 - 4 * deriv xi 1 := by
  rw [← Complex.ofReal_log narainExceptionalHeight.property.le]
  change ((Real.log (Real.exp (2 - 4 * (deriv xi 1).re))) : ℂ) = _
  rw [Real.log_exp]
  push_cast
  rw [xi_deriv_one_real]

/-- There is exactly one exceptional height, with no arithmetic assumption. -/
theorem filledNumeratorMean_deriv_zero_eq_zero_iff (Y : Height) :
    deriv (filledNumeratorMean Y) 0 = 0 ↔ Y = narainExceptionalHeight := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hp : (Y.val : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hY]
    exact Complex.exp_ne_zero _
  rw [filledNumeratorMean_deriv_zero, mul_eq_zero, or_iff_right hp]
  constructor
  · intro h
    have hr := congrArg Complex.re h
    rw [← Complex.ofReal_log Y.property.le] at hr
    norm_num [Complex.sub_re, Complex.mul_re] at hr
    apply Subtype.ext
    change Y.val = Real.exp (2 - 4 * (deriv xi 1).re)
    rw [← Real.exp_log Y.property]
    congr 1
    linarith only [hr]
  · intro h
    subst Y
    rw [narainExceptionalHeight_log]
    ring

/-- The exceptional cubic jet is controlled by the strict third logarithmic xi jet. -/
theorem filledNumeratorMean_exceptional_third_jet :
    iteratedDeriv 3 (filledNumeratorMean narainExceptionalHeight) 0 =
      8 * (narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) := by
  rw [filledNumeratorMean_third_jet, narainExceptionalHeight_log, narainCentralXiCurvature_eq]
  ring

/-- Strict xi logarithmic curvature excludes higher central degeneracy at the exceptional height. -/
theorem filledNumeratorMean_exceptional_third_jet_ne_zero :
    iteratedDeriv 3 (filledNumeratorMean narainExceptionalHeight) 0 ≠ 0 := by
  have hY : (narainExceptionalHeight.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr narainExceptionalHeight.property.ne'
  have hp : (narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hY]
    exact Complex.exp_ne_zero _
  rw [filledNumeratorMean_exceptional_third_jet]
  refine mul_ne_zero (mul_ne_zero (by norm_num) hp) ?_
  intro h
  have hr := congrArg Complex.re h
  norm_num [Complex.sub_re] at hr
  linarith only [hr, narainCentralXiCurvature_neg]

#print axioms filledNumeratorMean_deriv_zero_eq_zero_iff
#print axioms filledNumeratorMean_exceptional_third_jet_ne_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
