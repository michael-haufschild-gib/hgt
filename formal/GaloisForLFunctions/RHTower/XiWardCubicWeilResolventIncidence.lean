import GaloisForLFunctions.RHTower.XiWardCubicBichamberHolomorphicCodiagonal
import GaloisForLFunctions.RHTower.XiWeilResolventSource

/-!
# Cubic Ward reflection-Loewner / Weil-resolvent incidence (W-H192)

The W-H190 reflection-Loewner kernel is not merely analogous to the existing arithmetic Weil
polarization.  After the centered affine coordinate `z = -I * (s - 1/2)`, they are exactly equal.
Consequently the W-H191 holomorphic bichamber current has an unconditional, multiplicity-exact
divisor `tsum` whose coefficients are the source-realized Cauchy polarization and whose common
weight lands the cubic Hellinger codiagonal.

This identifies a literal coefficient-faithful pre-divisor incidence already present in the
Guinand--Weil source corpus.  No positivity or RH is used.  What remains is quantitative: prove a
two-chamber contour/trace shorting of this exact current by the P-G175 primitive source budget.
-/

open Complex

namespace RHTower

noncomputable section

/-- Centered affine coordinate carrying `s` to the XiC spectral plane. -/
def xiWardCubicCenteredCoordinate (s : ℂ) : ℂ := -I * (s - 1 / 2)

/-- The centered coordinate inverts the defining affine change of `XiC`. -/
theorem half_add_xiWardCubicCenteredCoordinate_mul_I (s : ℂ) :
    1 / 2 + xiWardCubicCenteredCoordinate s * I = s := by
  rw [xiWardCubicCenteredCoordinate]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- FE reflection becomes centered complex conjugation. -/
theorem xiWardCubicCenteredCoordinate_star (t : ℂ) :
    (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t) =
      xiWardCubicCenteredCoordinate (1 - star t) := by
  rw [xiWardCubicCenteredCoordinate, xiWardCubicCenteredCoordinate]
  change (starRingEnd ℂ) (-I * (t - 1 / 2)) = _
  simp
  rw [map_ofNat (starRingEnd ℂ) 2]
  ring

/-- Conjugated centered coordinate maps back to the FE-reflected Xi argument. -/
theorem half_add_star_xiWardCubicCenteredCoordinate_mul_I (t : ℂ) :
    1 / 2 + (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t) * I =
      1 - star t := by
  rw [xiWardCubicCenteredCoordinate_star,
    half_add_xiWardCubicCenteredCoordinate_mul_I]

/-- The centered Cauchy denominator is `-I` times the reflection-Loewner denominator. -/
theorem xiWardCubicCenteredCoordinate_sub_star (s t : ℂ) :
    xiWardCubicCenteredCoordinate s -
        (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t) =
      -I * (s + star t - 1) := by
  rw [xiWardCubicCenteredCoordinate]
  change _ - (starRingEnd ℂ) (-I * (t - 1 / 2)) = _
  simp
  rw [map_ofNat (starRingEnd ℂ) 2]
  ring

/-- Exact incidence: reflection-Loewner equals the arithmetic Weil polarization of two Cauchy
tests.  The premises only say the chosen evaluation points are regular and separated. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_xiWeilPolarization
    {s t : ℂ}
    (hs : XiC (xiWardCubicCenteredCoordinate s) ≠ 0)
    (ht : XiC ((starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) ≠ 0)
    (hsep : xiWardCubicCenteredCoordinate s ≠
      (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) :
    xiWardCubicReflectionLoewnerKernel s t =
      xiWeilPolarization
        (xiWeilCauchyTest (xiWardCubicCenteredCoordinate s))
        (xiWeilCauchyTest (xiWardCubicCenteredCoordinate t)) := by
  rw [xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference
    hs ht hsep]
  rw [← logDeriv_XiC_eq_relativeResolventTrace hs]
  rw [← logDeriv_XiC_eq_relativeResolventTrace ht]
  rw [logDeriv_XiC_eq_mul_I_logDeriv_xi,
    logDeriv_XiC_eq_mul_I_logDeriv_xi,
    half_add_xiWardCubicCenteredCoordinate_mul_I,
    half_add_star_xiWardCubicCenteredCoordinate_mul_I]
  rw [logDeriv_xi_reciprocity]
  rw [show logDeriv xi (star t) = star (logDeriv xi t) by
    exact logDeriv_xi_conj_global t]
  rw [xiWardCubicReflectionLoewnerKernel,
    xiWardCubicCenteredCoordinate_sub_star]
  field_simp [sub_ne_zero.mpr hsep]
  ring

/-- Multiplicity-exact divisor expansion of the reflection-Loewner kernel. -/
theorem xiWardCubicReflectionLoewnerKernel_eq_xiZeroCopy_tsum
    {s t : ℂ}
    (hs : XiC (xiWardCubicCenteredCoordinate s) ≠ 0)
    (ht : XiC ((starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) ≠ 0)
    (hsep : xiWardCubicCenteredCoordinate s ≠
      (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) :
    xiWardCubicReflectionLoewnerKernel s t =
      ∑' q : XiZeroCopy,
        xiWeilCauchyTest (xiWardCubicCenteredCoordinate s) (xiSpectralPoint q) *
          xiWeilCauchyTest
            ((starRingEnd ℂ) (xiWardCubicCenteredCoordinate t))
            (xiSpectralPoint q) := by
  rw [xiWardCubicReflectionLoewnerKernel_eq_xiWeilPolarization hs ht hsep,
    xiWeilPolarization]
  apply tsum_congr
  intro q
  rw [xiWeilSharp_cauchy]

/-- Complete holomorphic bichamber current as a coefficient-faithful divisor `tsum`. -/
theorem xiWardCubicBichamberHolomorphicallyWeightedCurrent_eq_xiZeroCopy_tsum
    {s t : ℂ}
    (hs : XiC (xiWardCubicCenteredCoordinate s) ≠ 0)
    (ht : XiC ((starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) ≠ 0)
    (hsep : xiWardCubicCenteredCoordinate s ≠
      (starRingEnd ℂ) (xiWardCubicCenteredCoordinate t)) (r : ℝ) :
    xiWardCubicBichamberHolomorphicallyWeightedCurrent s t r =
      ∑' q : XiZeroCopy,
        (xiWeilCauchyTest (xiWardCubicCenteredCoordinate s) (xiSpectralPoint q) *
          xiWeilCauchyTest
            ((starRingEnd ℂ) (xiWardCubicCenteredCoordinate t))
            (xiSpectralPoint q)) *
              xiWardCubicBichamberFeatureProduct s t r := by
  rw [xiWardCubicBichamberHolomorphicallyWeightedCurrent,
    xiWardCubicReflectionLoewnerKernel_eq_xiZeroCopy_tsum hs ht hsep,
    tsum_mul_right]

end
end RHTower
