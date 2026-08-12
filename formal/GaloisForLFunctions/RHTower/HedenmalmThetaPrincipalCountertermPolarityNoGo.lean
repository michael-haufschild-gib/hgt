import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniPermutationSectorNoGo
import GaloisForLFunctions.RHTower.XiUnitDoubleEulerPhysicalTraceClassUniversalityLaw

/-!
# Principal-counterterm polarity no-go for Route P

The corpus contains a genuine source-side cancellation of the prime-harmonic principal mass: the
unit-double Euler response has normalized coefficient `-1/p + 2/p²`.  Joining this counterterm to
the Route P Hellinger defect does make every nonneutral fibre summable.  But it makes the neutral
fibre nonsummable.  The result is the exact logical complement of the required Route P sector.

This polarity reversal is stable under every trace-class correction.  Thus cancellation of the
universal harmonic symbol by a fixed signed diagonal counterterm is not enough: the source must
force the coefficient of that symbol to vanish specifically on the neutral fibre, before the
positive sector norm is formed.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Hellinger polarization after subtraction of its universal prime-harmonic principal mass. -/
def thetaPrimePrincipalRelativeGap (t : ℝ) (p : Nat.Primes) : ℝ :=
  primeValuationHellingerGap (-|t|) p -
    routeNGammaSewnUniversalCriticalChannelMass p

/-- Exact trace-class tail after the universal harmonic symbol is subtracted off center. -/
theorem thetaPrimePrincipalRelativeGap_eq (t : ℝ) (p : Nat.Primes) :
    thetaPrimePrincipalRelativeGap t p =
      -2 * (p : ℝ) ^ (-(1 + |t|)) +
        (p : ℝ) ^ (-(1 + 2 * |t|)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hcross :
      routeNGammaSewnUniversalCriticalChannelAmplitude p *
          routeNGammaSewnTwistedCriticalChannelAmplitude t p =
        (p : ℝ) ^ (-(1 + |t|)) := by
    rw [routeNGammaSewnUniversalCriticalChannelAmplitude,
      routeNGammaSewnTwistedCriticalChannelAmplitude,
      ← Real.rpow_add hp0]
    congr 1
    ring
  rw [thetaPrimePrincipalRelativeGap,
    primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap,
    ← routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
    show
      (routeNGammaSewnUniversalCriticalChannelAmplitude p -
          routeNGammaSewnTwistedCriticalChannelAmplitude t p) ^ 2 -
          routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 =
        -2 * (routeNGammaSewnUniversalCriticalChannelAmplitude p *
          routeNGammaSewnTwistedCriticalChannelAmplitude t p) +
          routeNGammaSewnTwistedCriticalChannelAmplitude t p ^ 2 by ring,
    hcross, routeNGammaSewnTwistedCriticalChannelAmplitude_sq,
    routeNGammaSewnTwistedCriticalChannelMass]
  ring

/-- After principal subtraction, the Route P gap is summable exactly away from neutral grade. -/
theorem summable_thetaPrimePrincipalRelativeGap_iff (t : ℝ) :
    Summable (thetaPrimePrincipalRelativeGap t) ↔ t ≠ 0 := by
  constructor
  · intro hsum ht
    subst t
    apply not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq
    have hneg := hsum.mul_left (-1)
    exact hneg.congr fun p => by
      rw [thetaPrimePrincipalRelativeGap_eq,
        routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
        routeNGammaSewnUniversalCriticalChannelMass]
      simp
      ring
  · intro ht
    have htpos : 0 < |t| := abs_pos.mpr ht
    have hfirst : Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-(1 + |t|))) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    have hsecond : Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-(1 + 2 * |t|))) :=
      Nat.Primes.summable_rpow.mpr (by linarith)
    exact ((hfirst.mul_left (-2)).add hsecond).congr fun p => by
      rw [thetaPrimePrincipalRelativeGap_eq]

/-- Adding any trace-class remainder cannot repair the polarity reversal. -/
theorem summable_thetaPrimePrincipalRelativeGap_add_iff_of_summable
    (t : ℝ) (r : Nat.Primes → ℝ) (hr : Summable r) :
    Summable (fun p => thetaPrimePrincipalRelativeGap t p + r p) ↔ t ≠ 0 := by
  rw [← summable_thetaPrimePrincipalRelativeGap_iff t]
  constructor
  · intro hsum
    exact (hsum.sub hr).congr fun p => by ring
  · intro hsum
    exact hsum.add hr

/-- The actual unit-double Euler response divided by its nonzero prime log. -/
def thetaUnitDoubleEulerNormalizedCounterterm (p : Nat.Primes) : ℝ :=
  xiUnitDoubleEulerResponseSpectralCoefficient p / Real.log (p : ℝ)

/-- Exact normalized source counterterm: negative universal mass plus a trace-class remainder. -/
theorem thetaUnitDoubleEulerNormalizedCounterterm_eq (p : Nat.Primes) :
    thetaUnitDoubleEulerNormalizedCounterterm p =
      -(p : ℝ) ^ (-1 : ℝ) + 2 / (p : ℝ) ^ 2 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [thetaUnitDoubleEulerNormalizedCounterterm,
    xiUnitDoubleEulerResponseSpectralCoefficient,
    ArithmeticFunction.vonMangoldt_apply_prime p.2]
  rw [mul_div_cancel_left₀ _ hlog, Real.rpow_neg_one]
  field_simp [hp0]
  ring

/-- The inverse-square remainder in the normalized unit-double response is summable. -/
theorem summable_thetaUnitDoubleEulerNormalizedRemainder :
    Summable (fun p : Nat.Primes => 2 / (p : ℝ) ^ 2) := by
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  exact (hpow.mul_left 2).congr fun p => by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hp0.le, Real.rpow_natCast]
    ring

/-- **Actual source-counterterm polarity reversal.** The normalized unit-double Euler response
makes the Route P prime gap summable exactly off neutral grade. -/
theorem summable_thetaGap_add_unitDoubleEulerCounterterm_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      primeValuationHellingerGap (-|t|) p +
        thetaUnitDoubleEulerNormalizedCounterterm p) ↔ t ≠ 0 := by
  rw [show (fun p : Nat.Primes =>
      primeValuationHellingerGap (-|t|) p +
        thetaUnitDoubleEulerNormalizedCounterterm p) =
      fun p : Nat.Primes => thetaPrimePrincipalRelativeGap t p +
        2 / (p : ℝ) ^ 2 by
    funext p
    rw [thetaPrimePrincipalRelativeGap,
      thetaUnitDoubleEulerNormalizedCounterterm_eq,
      routeNGammaSewnUniversalCriticalChannelMass]
    ring]
  exact summable_thetaPrimePrincipalRelativeGap_add_iff_of_summable
    t _ summable_thetaUnitDoubleEulerNormalizedRemainder

/-- On an oriented Xi copy, the actual source counterterm selects nonzero theta flux rather than
neutrality. -/
theorem summable_thetaGap_add_unitDoubleEulerCounterterm_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      primeValuationHellingerGap
          (-|primeDepthBVWoldXiCenteredRate q.1|) p +
        thetaUnitDoubleEulerNormalizedCounterterm p) ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  rw [summable_thetaGap_add_unitDoubleEulerCounterterm_iff]
  rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  apply not_congr
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left
      (neg_ne_zero.mpr
        (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne')

/-- **Route P polarity no-go.** Individual squared-node positivity is equivalent to failure, not
success, of summability after the fixed unit-double Euler principal cancellation. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_not_summable_unitDoubleCorrectedGap
    (q : XiZeroCopy) :
    (∃ r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      ¬ Summable (fun p : Nat.Primes =>
        primeValuationHellingerGap
            (-|primeDepthBVWoldXiCenteredRate q.1|) p +
          thetaUnitDoubleEulerNormalizedCounterterm p) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    summable_thetaGap_add_unitDoubleEulerCounterterm_iff_boundaryFlux_ne_zero]
  simp

end

end RHTower.HedenmalmThetaSource
