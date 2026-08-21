import GaloisForLFunctions.RHTower.XiWardCubicBichamberHolomorphicCodiagonal
import GaloisForLFunctions.RHTower.HedenmalmOrientationDivisorTransgression

/-!
# Positive-shift arithmetic realization of the reflection--Loewner covariance

The reflection--Loewner kernel becomes a literal positive-real-shift quotient of the completed
pole--Gamma--von-Mangoldt current on a source pair chosen wholly inside the two absolute-Euler
chambers.  No Xi zero, divisor support, or critical-line projector enters the definition.

The complex-shift extension also has a canonical punctured diagonal value: whenever the completed
arithmetic current has derivative `d`, its shift covariance tends to `d`.  This identifies the
finite-part diagonal before any divisor expansion.  It supplies source provenance for the
submicroscopic covariance, but does not assert the still-open height-local `4 / 25` trace bound.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Positive-real-shift source quotient of the completed arithmetic current. -/
def xiWardCubicPositiveRealShiftArithmeticCovariance
    (z : ℂ) (eps : ℝ) : ℂ :=
  (xiWardCubicCompletedArithmeticCurrent (z + (eps : ℂ)) -
    xiWardCubicCompletedArithmeticCurrent z) / (eps : ℂ)

/-- Complex punctured extension used for the diagonal finite part. -/
def xiWardCubicShiftArithmeticCovariance
    (z eps : ℂ) : ℂ :=
  eps⁻¹ * (xiWardCubicCompletedArithmeticCurrent (z + eps) -
    xiWardCubicCompletedArithmeticCurrent z)

/-- On opposite absolute-Euler chambers the reflection--Loewner kernel is exactly the positive
real shift covariance of the pole--Gamma--von-Mangoldt source current. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_positiveRealShiftArithmeticCovariance
    {z : ℂ} {eps : ℝ} (hz : 1 < z.re) (heps : 0 < eps) :
    xiWardCubicReflectionLoewnerKernel
        (1 - z) (star (z + (eps : ℂ))) =
      xiWardCubicPositiveRealShiftArithmeticCovariance z eps := by
  have hs : (1 - z).re < 0 := by simp; linarith
  have ht : 1 < (star (z + (eps : ℂ))).re := by
    simp
    linarith
  rw [xiWardCubicReflectionLoewnerKernel_eq_bichamberArithmetic hs ht]
  simp [xiWardCubicPositiveRealShiftArithmeticCovariance,
    RCLike.star_def]

/-- Exact source split: rational poles and Gamma occupy the first quotient; the sign-oriented
von Mangoldt increment occupies the second. -/
theorem xiWardCubicShiftArithmeticCovariance_eq_poleGamma_add_vonMangoldt
    (z eps : ℂ) :
    xiWardCubicShiftArithmeticCovariance z eps =
      (((z + eps)⁻¹ - z⁻¹) +
          ((z + eps - 1)⁻¹ - (z - 1)⁻¹) +
          (logDeriv Gammaℝ (z + eps) - logDeriv Gammaℝ z)) / eps +
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z -
          LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (z + eps)) / eps := by
  rw [xiWardCubicShiftArithmeticCovariance]
  unfold xiWardCubicCompletedArithmeticCurrent
  ring

/-- Diagonal finite part of the source quotient is the derivative of the completed arithmetic
current. -/
theorem tendsto_xiWardCubicShiftArithmeticCovariance
    {z d : ℂ}
    (hderiv : HasDerivAt xiWardCubicCompletedArithmeticCurrent d z) :
    Tendsto (xiWardCubicShiftArithmeticCovariance z) (𝓝[≠] 0) (𝓝 d) := by
  change Tendsto (fun eps : ℂ => eps⁻¹ *
    (xiWardCubicCompletedArithmeticCurrent (z + eps) -
      xiWardCubicCompletedArithmeticCurrent z)) (𝓝[≠] 0) (𝓝 d)
  simpa only [smul_eq_mul] using hderiv.tendsto_slope_zero

/-! ## Source-first continuation to translated divisor multiplicity -/

/-- Meromorphic continuation of the source covariance after translating its right endpoint to
`z`.  The definition is made only after the source quotient above has been formed. -/
def xiWardCubicPositiveShiftDivisorTransgression
    (z : ℂ) (eps : ℝ) : ℂ :=
  -((eps : ℂ)⁻¹) * xiFluxShiftDifference eps z

/-- On the absolute-Euler chamber, the continued transgression is exactly the original
pole--Gamma--von-Mangoldt positive-shift covariance. -/
theorem xiWardCubicPositiveShiftDivisorTransgression_eq_arithmeticCovariance
    {z : ℂ} {eps : ℝ} (hz : 1 < (z - (eps : ℂ)).re) (heps : 0 < eps) :
    xiWardCubicPositiveShiftDivisorTransgression z eps =
      xiWardCubicPositiveRealShiftArithmeticCovariance
        (z - (eps : ℂ)) eps := by
  have hz' : 1 < z.re := by
    have hre : z.re = (z - (eps : ℂ)).re + eps := by simp
    rw [hre]
    linarith
  have hzeq : z - (eps : ℂ) + (eps : ℂ) = z := by ring
  calc
    xiWardCubicPositiveShiftDivisorTransgression z eps =
        (logDeriv xi z - logDeriv xi (z - (eps : ℂ))) / (eps : ℂ) := by
      rw [xiWardCubicPositiveShiftDivisorTransgression,
        xiFluxShiftDifference, seamFluxCochain, seamFluxCochain]
      ring
    _ = xiWardCubicPositiveRealShiftArithmeticCovariance
          (z - (eps : ℂ)) eps := by
      rw [logDeriv_xi_eq_arithmetic hz', logDeriv_xi_eq_arithmetic hz]
      unfold xiWardCubicPositiveRealShiftArithmeticCovariance
      rw [hzeq]

/-- Removable local germ of the continued positive-shift transgression. -/
def xiWardCubicPositiveShiftDivisorTransgressionGerm
    (eps : ℝ) (rho x : ℂ) : ℂ :=
  -((eps : ℂ)⁻¹) * xiFluxShiftDifferenceFullResidueGerm eps rho x

theorem analyticAt_xiWardCubicPositiveShiftDivisorTransgressionGerm
    (eps : ℝ) (rho : ℂ) :
    AnalyticAt ℂ
      (xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho) 0 :=
  analyticAt_const.mul
    (analyticAt_xiFluxShiftDifferenceFullResidueGerm eps rho)

/-- Exact normalized discrete derivative of Xi multiplicity exposed only after continuation. -/
theorem xiWardCubicPositiveShiftDivisorTransgressionGerm_zero
    {eps : ℝ} (heps : eps ≠ 0) (rho : ℂ) :
    xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0 =
      ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) -
        (((analyticOrderAt xi (rho - (eps : ℂ))).toNat : ℕ) : ℂ)) /
          (eps : ℂ) := by
  rw [xiWardCubicPositiveShiftDivisorTransgressionGerm,
    xiFluxShiftDifferenceFullResidueGerm_zero]
  have hepsC : (eps : ℂ) ≠ 0 := ofReal_ne_zero.mpr heps
  field_simp [hepsC]
  ring

/-- Off the germ center, the local coordinate times the continued source covariance is recovered
exactly. -/
theorem xiWardCubicPositiveShiftDivisorTransgressionGerm_eventuallyEq
    (eps : ℝ) (rho : ℂ) :
    xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho =ᶠ[𝓝[≠] 0]
      fun x : ℂ => x *
        xiWardCubicPositiveShiftDivisorTransgression (rho + x) eps := by
  filter_upwards
    [xiFluxShiftDifferenceFullResidueGerm_eventuallyEq eps rho] with x hx
  rw [xiWardCubicPositiveShiftDivisorTransgressionGerm,
    xiWardCubicPositiveShiftDivisorTransgression, hx]
  ring

/-- At a left translation boundary the shifted predecessor is regular, so the post-scalarization
charge is exactly the diagonal multiplicity divided by the positive displacement. -/
theorem xiWardCubicPositiveShiftDivisorTransgressionGerm_zero_of_leftBoundary
    {eps : ℝ} (heps : 0 < eps) {rho : ℂ}
    (hrho : rho ∈ xiLeftShiftBoundary eps) :
    xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0 =
      (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) / (eps : ℂ) := by
  rw [xiWardCubicPositiveShiftDivisorTransgressionGerm_zero heps.ne']
  have hshiftOrder : analyticOrderAt xi (rho - (eps : ℂ)) = 0 :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hrho.2
  rw [hshiftOrder]
  norm_num

/-- Every multiplicity copy on a positive left translation boundary contributes strictly
positive real transgression charge. -/
theorem xiWardCubicPositiveShiftDivisorTransgressionGerm_zero_re_pos_of_leftBoundary
    {eps : ℝ} (heps : 0 < eps) {rho : ℂ}
    (hrho : rho ∈ xiLeftShiftBoundary eps) :
    0 < (xiWardCubicPositiveShiftDivisorTransgressionGerm eps rho 0).re := by
  rw [xiWardCubicPositiveShiftDivisorTransgressionGerm_zero_of_leftBoundary heps hrho]
  have hm : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hrho.1)
  have hmR : 0 < (((analyticOrderAt xi rho).toNat : ℕ) : ℝ) := by
    exact_mod_cast hm
  simpa using div_pos hmR heps

end


end RHTower
