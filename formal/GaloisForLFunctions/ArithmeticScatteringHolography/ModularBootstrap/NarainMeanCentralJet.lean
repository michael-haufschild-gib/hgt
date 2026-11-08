import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralSymmetry

/-!
# Central factorization of the averaged Narain transform

The averaged continuation factors near zero into its universal linear zero, two entire divided target numerators, and a nonvanishing analytic unit. This gives its exact first central jet.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The nonvanishing analytic factor in the central mean decomposition. -/
def narainMeanCentralUnit (u : ℂ) : ℂ :=
  (2 * (1 + 2 * u) * xi (1 + 2 * u) * (u - 1 / 2) ^ 2)⁻¹

/-- The central mean unit is analytic at zero. -/
theorem analyticAt_narainMeanCentralUnit_zero : AnalyticAt ℂ narainMeanCentralUnit 0 := by
  have hd : AnalyticAt ℂ (fun u : ℂ =>
      2 * (1 + 2 * u) * xi (1 + 2 * u) * (u - 1 / 2) ^ 2) 0 :=
    (((by fun_prop : AnalyticAt ℂ (fun u : ℂ => 2 * (1 + 2 * u)) 0).mul
      (differentiable_xi_shift.analyticAt 0)).mul (by fun_prop))
  exact hd.inv (by norm_num [xi_one])

/-- The inverse-Mellin normalization gives central unit value four. -/
theorem narainMeanCentralUnit_zero : narainMeanCentralUnit 0 = 4 := by
  norm_num [narainMeanCentralUnit, xi_one]

/-- The central mean factors into its universal zero, two divided target factors and an analytic unit. -/
theorem narainMellinMean_central_germ (Y Z : Height) :
    narainMellinMean Y Z =ᶠ[𝓝 (0 : ℂ)] fun u =>
      u * dividedFilledNumeratorMean Y u * dividedFilledNumeratorMean Z u * narainMeanCentralUnit u := by
  filter_upwards [isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 / 2 by norm_num)] with u hu
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  have hquot : narainMellinMean Y Z u = narainMeanMainPoleNumerator Y Z u / (u - 1 / 2) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hu))).mpr
    rw [narainMeanMainPoleNumerator_eq Y Z htwo]
    ring
  rw [hquot, narainMeanMainPoleNumerator_eq_reduced]
  simp only [narainReducedMeanMainPoleNumerator, narainMeanCentralUnit, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The first averaged central jet factors into the two explicit target-height defects. -/
theorem narainMellinMean_deriv_zero (Y Z : Height) :
    deriv (narainMellinMean Y Z) 0 =
      4 * (Y.val : ℂ) ^ (1 / 2 : ℂ) * (Z.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - 4 * deriv xi 1 - Complex.log (Y.val : ℂ)) *
          (2 - 4 * deriv xi 1 - Complex.log (Z.val : ℂ)) := by
  have hY := ((differentiable_dividedFilledNumeratorMean Y) 0).hasDerivAt
  have hZ := ((differentiable_dividedFilledNumeratorMean Z) 0).hasDerivAt
  have hq := analyticAt_narainMeanCentralUnit_zero.differentiableAt.hasDerivAt
  have h := ((((hasDerivAt_id (0 : ℂ)).mul hY).mul hZ).mul hq).deriv
  change deriv (fun u : ℂ => u * dividedFilledNumeratorMean Y u *
    dividedFilledNumeratorMean Z u * narainMeanCentralUnit u) 0 =
    ((1 * dividedFilledNumeratorMean Y 0 + 0 * deriv (dividedFilledNumeratorMean Y) 0) *
      dividedFilledNumeratorMean Z 0 + (0 * dividedFilledNumeratorMean Y 0) *
        deriv (dividedFilledNumeratorMean Z) 0) * narainMeanCentralUnit 0 +
      ((0 * dividedFilledNumeratorMean Y 0) * dividedFilledNumeratorMean Z 0) *
        deriv narainMeanCentralUnit 0 at h
  rw [(narainMellinMean_central_germ Y Z).deriv_eq, h]
  simp only [zero_mul, mul_zero, one_mul, zero_add, add_zero, narainMeanCentralUnit_zero]
  rw [← filledNumeratorMean_first_jet_eq_divided Y,
    ← filledNumeratorMean_first_jet_eq_divided Z,
    filledNumeratorMean_deriv_zero, filledNumeratorMean_deriv_zero]
  ring

#print axioms narainMellinMean_central_germ
#print axioms narainMellinMean_deriv_zero
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
