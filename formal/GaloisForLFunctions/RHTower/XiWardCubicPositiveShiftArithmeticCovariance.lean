import GaloisForLFunctions.RHTower.XiWardCubicBichamberHolomorphicCodiagonal

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

end


end RHTower
