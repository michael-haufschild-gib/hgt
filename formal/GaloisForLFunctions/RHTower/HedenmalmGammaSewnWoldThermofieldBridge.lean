import GaloisForLFunctions.RHTower.HedenmalmGammaSewnKakutaniPolarizationBridge
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture

/-!
# Wold thermofield realization of the Route N critical doublet

The Gamma-sewn Route N marked-channel amplitudes are exactly the square roots of the existing
critical and radially twisted prime-valuation masses.  Their product is exactly the corresponding
cross mass.  Thus the full normalized Wold thermofield Hellinger factor is not merely another
detector with the same zero set: its local complement is the Route N critical amplitude gap,
divided by the square of the Wold resolvent denominator.

Combining this identity with the preceding Krein polarization gives a direct formula for the
complete local thermofield sector defect in terms of the signed Route N wall.  No product measure,
Xi zero, or RH hypothesis is inserted into the comparison.
-/

namespace RHTower

noncomputable section

/-- The Route N universal channel mass is the critical prime-valuation mass. -/
theorem routeNGammaSewnUniversalCriticalChannelMass_eq_primeRadialCriticalMass
    (p : Nat.Primes) :
    routeNGammaSewnUniversalCriticalChannelMass p =
      primeRadialCriticalMass p := by
  rw [routeNGammaSewnUniversalCriticalChannelMass,
    primeRadialCriticalMass, Real.rpow_neg_one]

/-- The Route N twisted channel mass is the existing radial mass at centered drift `-|t|`. -/
theorem routeNGammaSewnTwistedCriticalChannelMass_eq_primeRadialTwistedMass
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelMass t p =
      primeRadialTwistedMass (-|t|) p := by
  rw [routeNGammaSewnTwistedCriticalChannelMass, primeRadialTwistedMass]
  congr 1
  ring

/-- Product of the two Route N channel amplitudes is the Wold thermofield cross mass. -/
theorem routeNGammaSewnCriticalChannelAmplitude_mul_eq_primeRadialCrossMass
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnUniversalCriticalChannelAmplitude p *
        routeNGammaSewnTwistedCriticalChannelAmplitude t p =
      primeRadialCrossMass (-|t|) p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnUniversalCriticalChannelAmplitude,
    routeNGammaSewnTwistedCriticalChannelAmplitude,
    primeRadialCrossMass, ← Real.rpow_add hp0]
  congr 1
  ring

/-- Algebraic polarization law behind normalized geometric-law Hellinger affinity. -/
theorem one_sub_squaredHellingerAffinity_sq_eq_amplitudeGap
    {x y : ℝ} (hxy : 1 - x * y ≠ 0) :
    1 - squaredHellingerAffinity (x ^ 2) (y ^ 2) (x * y) =
      (x - y) ^ 2 / (1 - x * y) ^ 2 := by
  rw [squaredHellingerAffinity]
  field_simp [hxy]
  ring

/-- **Route N/Wold thermofield identity.**  Complement of the complete normalized local
thermofield overlap is exactly the Route N critical amplitude gap divided by the Wold resolvent
denominator. -/
theorem one_sub_primeValuationSquaredHellingerFactor_neg_abs_eq_routeNAmplitudeGap
    (t : ℝ) (p : Nat.Primes) :
    1 - primeValuationSquaredHellingerFactor (-|t|) p =
      primeValuationHellingerGap (-|t|) p /
        (1 - primeRadialCrossMass (-|t|) p) ^ 2 := by
  have hcrossLt : primeRadialCrossMass (-|t|) p < 1 :=
    primeRadialCrossMass_lt_one (by linarith [abs_nonneg t]) p
  have hden : 1 - primeRadialCrossMass (-|t|) p ≠ 0 :=
    ne_of_gt (sub_pos.mpr hcrossLt)
  have hdenAmplitude :
      1 - routeNGammaSewnUniversalCriticalChannelAmplitude p *
          routeNGammaSewnTwistedCriticalChannelAmplitude t p ≠ 0 := by
    rw [routeNGammaSewnCriticalChannelAmplitude_mul_eq_primeRadialCrossMass]
    exact hden
  rw [primeValuationSquaredHellingerFactor,
    ← routeNGammaSewnUniversalCriticalChannelMass_eq_primeRadialCriticalMass,
    ← routeNGammaSewnTwistedCriticalChannelMass_eq_primeRadialTwistedMass,
    ← routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
    ← routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
    ← routeNGammaSewnCriticalChannelAmplitude_mul_eq_primeRadialCrossMass,
    primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap]
  exact one_sub_squaredHellingerAffinity_sq_eq_amplitudeGap hdenAmplitude

/-- Full normalized thermofield sector defect as an exact nonlinear polarization of the signed
Route N Krein wall. -/
theorem one_sub_primeValuationSquaredHellingerFactor_neg_abs_eq_routeNKreinPolarization
    (t : ℝ) (p : Nat.Primes) :
    1 - primeValuationSquaredHellingerFactor (-|t|) p =
      ((p : ℝ) * routeNGammaSewnCriticalHorizonKreinCharge t p ^ 2 /
          (1 + (p : ℝ) ^ (-|t|)) ^ 2) /
        (1 - primeRadialCrossMass (-|t|) p) ^ 2 := by
  rw [one_sub_primeValuationSquaredHellingerFactor_neg_abs_eq_routeNAmplitudeGap,
    primeValuationHellingerGap_neg_abs_eq_routeNKreinPolarization]

/-- Route N amplitude gap is bounded above by the full normalized thermofield defect. -/
theorem primeValuationHellingerGap_neg_abs_le_thermofieldDefect
    (t : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap (-|t|) p ≤
      1 - primeValuationSquaredHellingerFactor (-|t|) p := by
  have hcross0 : 0 ≤ primeRadialCrossMass (-|t|) p :=
    Real.rpow_nonneg (by exact_mod_cast p.2.pos.le) _
  have hcrossHalf : primeRadialCrossMass (-|t|) p ≤ 1 / 2 :=
    primeRadialCrossMass_le_half_of_nonpos (neg_nonpos.mpr (abs_nonneg t)) p
  have hdenBase : 0 < 1 - primeRadialCrossMass (-|t|) p := by
    linarith
  have hdenPos : 0 < (1 - primeRadialCrossMass (-|t|) p) ^ 2 := by
    positivity
  have hdenLe : (1 - primeRadialCrossMass (-|t|) p) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (primeRadialCrossMass (-|t|) p)]
  have hgap0 : 0 ≤ primeValuationHellingerGap (-|t|) p := by
    rw [primeValuationHellingerGap]
    positivity
  rw [one_sub_primeValuationSquaredHellingerFactor_neg_abs_eq_routeNAmplitudeGap]
  apply (le_div_iff₀ hdenPos).2
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hdenLe hgap0

/-- Summability of the complete local Wold thermofield defect occurs exactly at neutral Route N
grade.  This is the full normalized sector statement, not only its unnormalized numerator. -/
theorem summable_routeNWoldThermofieldDefect_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      1 - primeValuationSquaredHellingerFactor (-|t|) p) ↔
      t = 0 := by
  constructor
  · intro hdefect
    have hgap : Summable (primeValuationHellingerGap (-|t|)) :=
      Summable.of_nonneg_of_le
        (fun p => by rw [primeValuationHellingerGap]; positivity)
        (primeValuationHellingerGap_neg_abs_le_thermofieldDefect t)
        hdefect
    have hcenter := (summable_primeValuationHellingerGap_iff (-|t|)).mp hgap
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    simpa only [abs_zero, neg_zero, primeValuationSquaredHellingerFactor_zero,
      sub_self] using (summable_zero : Summable (fun _p : Nat.Primes => (0 : ℝ)))

end

end RHTower
