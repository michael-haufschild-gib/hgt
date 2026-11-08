import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageDecay
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# Rigidity of the averaged scalar constant

A positive-power remainder makes its Mellin transform analytic at the
main pole. Differentiating the cleared identity forces the constant
term to equal the derivative of the averaged main-pole numerator.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Any positive power remainder fixes the constant term of the actual average. -/
theorem narainAverageRate_constant_coefficient
    (Y Z : Height) {α : ℝ} {a b : ℂ} (hα : 0 < α)
    (hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (a * (Real.log y : ℂ) + b)) =O[𝓝[>] 0] (fun y : ℝ => y ^ α)) :
    b = narainAverageConstant Y Z := by
  let g := narainAverageRemainder Y Z a b
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainAverageRemainder_exp Y Z a b
  have hdiff : DifferentiableAt ℂ (mellin g) (1 / 2 + (1 / 2 : ℂ)) :=
    mellin_differentiableAt_of_isBigO_rpow_exp hc
      (locallyIntegrableOn_narainAverageRemainder Y Z a b) htop
      (isBigO_narainAverageRemainder_bot Y Z hrate) (by norm_num; linarith only [hα])
  let K := fun u : ℂ => (u - 1 / 2) ^ 2 * mellin g (1 / 2 + u) - a + b * (u - 1 / 2)
  have hm := hdiff.hasDerivAt.comp (1 / 2)
    ((hasDerivAt_id (1 / 2 : ℂ)).const_add (1 / 2))
  have hw := (hasDerivAt_id (1 / 2 : ℂ)).sub_const (1 / 2)
  have hK : HasDerivAt K b (1 / 2) := by
    convert! ((((hw.pow 2).mul hm).sub_const a).add (hw.const_mul b)) using 1
    simp
  have hC : Continuous (fun u : ℂ => (u * (1 + 2 * u)) * xi (1 + 2 * u)) :=
    ((by fun_prop : Differentiable ℂ (fun u : ℂ => u * (1 + 2 * u))).mul
      differentiable_xi_shift).continuous
  have hne : ∀ᶠ u : ℂ in 𝓝 (1 / 2),
      (u * (1 + 2 * u)) * xi (1 + 2 * u) ≠ 0 :=
    (isOpen_ne_fun hC continuous_const).mem_nhds (by norm_num [xi_two_ne_zero])
  have heq : K =ᶠ[𝓝 (1 / 2 : ℂ)] narainMeanMainPoleNumerator Y Z := by
    filter_upwards [hne, (isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 / 2 - α < (1 / 2 : ℂ).re by norm_num; linarith only [hα])] with u hcu hu
    have h := narainAverageRemainder_mellin_cleared Y Z hα hrate hu
    change K u = filledNumeratorMean Y u * filledNumeratorMean Z u /
      (2 * (u * (1 + 2 * u)) * xi (1 + 2 * u))
    apply (eq_div_iff (by rw [mul_assoc]; exact mul_ne_zero two_ne_zero hcu)).mpr
    change (u * (1 + 2 * u)) * xi (1 + 2 * u) * K u = _ at h
    linear_combination 2 * h
  exact ((hK.congr_of_eventuallyEq heq.symm).deriv).symm

#print axioms narainAverageRate_constant_coefficient
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
