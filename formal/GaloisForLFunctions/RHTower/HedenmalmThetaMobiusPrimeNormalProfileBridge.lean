import GaloisForLFunctions.RHTower.HedenmalmThetaContinuousPrincipalRenormalizationNoGo
import GaloisForLFunctions.RHTower.MobiusThetaInternalJetPrimeNormalComplexGraph

/-!
# Physical Möbius prime-normal profile bridge to Route P

The singular Möbius--theta prime-normal source graph already carries the unsquared reflected
orientation that survives every bounded-reader no-go.  This file identifies its local positive
energy exactly with the Route P Kakutani polarization.

For centered grade `a`, the raw source reflection profile is `p^a - p^-a`.  Its square, divided by
the forced positive gauge `p (1 + p^|a|)^(2 : ℕ)`, is precisely
`p^-1 (1 - p^-|a|)^(2 : ℕ)`.  Thus the unrenormalized Route P harmonic class is not an abstract product
measure artifact: it is the normalized square of a literal target-free singular source profile.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Reflection-odd modular profile of the actual Möbius prime-normal raw source at one Xi copy. -/
def thetaMobiusPrimeNormalReflectionProfile
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  ‖mobiusThetaPrimeRawAmplitude p 1 (1 - (q.1 : ℂ))‖ /
      ‖mobiusThetaPrimeRawAmplitude p 1 (q.1 : ℂ)‖ -
    ‖mobiusThetaPrimeRawAmplitude p 1 (q.1 : ℂ)‖ /
      ‖mobiusThetaPrimeRawAmplitude p 1 (1 - (q.1 : ℂ))‖

/-- The source profile is the unsquared prime modular displacement. -/
theorem thetaMobiusPrimeNormalReflectionProfile_eq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalReflectionProfile p q =
      (p : ℝ) ^ primeDepthBVWoldXiCenteredRate q.1 -
        (p : ℝ) ^ (-primeDepthBVWoldXiCenteredRate q.1) := by
  rw [thetaMobiusPrimeNormalReflectionProfile,
    mobiusThetaPrimeRawAmplitude_reflection_ratio p.2,
    mobiusThetaPrimeRawAmplitude_reverseReflection_ratio p.2]
  simp [primeDepthBVWoldXiCenteredRate]

/-- Positive source gauge converting the raw reflection profile square to Route P polarization. -/
def thetaMobiusPrimeNormalProfilePositiveGauge
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  1 / (p : ℝ) /
    (1 + (p : ℝ) ^ |primeDepthBVWoldXiCenteredRate q.1|) ^ 2

theorem thetaMobiusPrimeNormalProfilePositiveGauge_pos
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaMobiusPrimeNormalProfilePositiveGauge p q := by
  rw [thetaMobiusPrimeNormalProfilePositiveGauge]
  exact div_pos (one_div_pos.mpr (by exact_mod_cast p.2.pos))
    (sq_pos_of_pos (by positivity))

/-- **Exact physical-profile bridge.** Route P local polarization is the normalized square of the
literal singular Möbius prime-normal reflection profile. -/
theorem primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    primeValuationHellingerGap
        (-|primeDepthBVWoldXiCenteredRate q.1|) p =
      thetaMobiusPrimeNormalProfilePositiveGauge p q *
        thetaMobiusPrimeNormalReflectionProfile p q ^ 2 := by
  let a : ℝ := primeDepthBVWoldXiCenteredRate q.1
  let d : ℝ := |a|
  let P : ℝ := p
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast p.2.pos
  have hprofileSq :
      thetaMobiusPrimeNormalReflectionProfile p q ^ 2 =
        (P ^ d - P ^ (-d)) ^ 2 := by
    rw [thetaMobiusPrimeNormalReflectionProfile_eq]
    change (P ^ a - P ^ (-a)) ^ 2 = (P ^ d - P ^ (-d)) ^ 2
    by_cases ha : 0 ≤ a
    · rw [show d = a by simp [d, abs_of_nonneg ha]]
    · have ha' : a ≤ 0 := le_of_not_ge ha
      rw [show d = -a by simp [d, abs_of_nonpos ha']]
      simp only [neg_neg]
      ring
  rw [primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq,
    thetaKakutaniFluxPolarization_eq_primeHarmonic_mul_sq,
    thetaMobiusPrimeNormalProfilePositiveGauge, hprofileSq]
  change 1 / P * (1 - P ^ (-d)) ^ 2 =
    (1 / P / (1 + P ^ d) ^ 2) * (P ^ d - P ^ (-d)) ^ 2
  rw [Real.rpow_neg hP.le]
  have hPd : 0 < P ^ d := Real.rpow_pos_of_pos hP _
  field_simp [hP.ne', hPd.ne']
  ring

/-- Physical Möbius profile vanishing is exactly same-fibre theta-current neutrality. -/
theorem thetaMobiusPrimeNormalReflectionProfile_eq_zero_iff_boundaryFlux_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaMobiusPrimeNormalReflectionProfile p q = 0 ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  have hgauge := thetaMobiusPrimeNormalProfilePositiveGauge_pos p q
  have htheta := thetaKakutaniFluxPositiveUnit_pos p q
  constructor
  · intro hprofile
    have hgap : primeValuationHellingerGap
        (-|primeDepthBVWoldXiCenteredRate q.1|) p = 0 := by
      rw [primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq,
        hprofile]
      norm_num
    rw [primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq] at hgap
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hgap).resolve_left htheta.ne')
  · intro hflux
    have hgap : thetaMobiusPrimeNormalProfilePositiveGauge p q *
        thetaMobiusPrimeNormalReflectionProfile p q ^ 2 = 0 := by
      rw [← primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq,
        primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq,
        hflux]
      norm_num
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hgap).resolve_left hgauge.ne')

/-- All-prime square admission of the physical singular source profile is exactly individual
Route P node positivity. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_mobiusPrimeNormalProfileEnergy
    (q : XiZeroCopy) :
    (∃ x : ℝ, 0 < x ∧ thetaXiReciprocalEigenvalue q ^ 2 = (x : ℂ)) ↔
      Summable (fun p : Nat.Primes =>
        thetaMobiusPrimeNormalProfilePositiveGauge p q *
          thetaMobiusPrimeNormalReflectionProfile p q ^ 2) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_kakutaniFluxPolarization]
  rw [show (fun p : Nat.Primes =>
      thetaMobiusPrimeNormalProfilePositiveGauge p q *
        thetaMobiusPrimeNormalReflectionProfile p q ^ 2) =
      fun p : Nat.Primes => thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 by
    funext p
    rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq,
      primeValuationHellingerGap_eq_mobiusPrimeNormalProfile_sq]]

end

end RHTower.HedenmalmThetaSource
