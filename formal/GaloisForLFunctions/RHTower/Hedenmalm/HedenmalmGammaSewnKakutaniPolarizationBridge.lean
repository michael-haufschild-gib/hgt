import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnTransverseModularCocycle
import GaloisForLFunctions.RHTower.PrimeValuationKakutaniRadialPurity

/-!
# Kakutani polarization of the Route N critical doublet

At the sharp damping horizon, the two unordered marked channel masses are

`p^-1` and `p^(-1-2|t|)`.

Their ratio is exactly the transverse modular cocycle recovered in the preceding module.  Their
square-root distance is exactly the source-derived prime-valuation Hellinger gap at radial twist
`-|t|`.  Consequently the positive Kakutani sector detector is the canonical nonlinear
polarization of the signed Route N Krein wall:

`H_t(p) = p Q_t(p)^(2 : ℕ) / (1 + p^(-|t|))^(2 : ℕ)`.

This identifies the apparently external product-measure sector with the literal two-channel
Gamma-sewn Route N source.  It also explains the singular factor `p`: it is division by the
universal critical channel mass `p^-1`, not an arbitrary diagonal renormalization.
-/

namespace RHTower

noncomputable section

/-- Universal, untwisted channel mass at the Route N critical horizon. -/
def routeNGammaSewnUniversalCriticalChannelMass (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-1 : ℝ)

/-- Radially twisted channel mass at the Route N critical horizon. -/
def routeNGammaSewnTwistedCriticalChannelMass
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-1 - 2 * |t|)

/-- The full positive critical-horizon energy is the sum of the universal and twisted channel
masses. -/
theorem routeNGammaSewnCriticalHorizonEnergy_eq_channelMasses
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnCriticalHorizonEnergy t p =
      routeNGammaSewnUniversalCriticalChannelMass p +
        routeNGammaSewnTwistedCriticalChannelMass t p := by
  rw [routeNGammaSewnCriticalHorizonEnergy_eq,
    routeNGammaSewnUniversalCriticalChannelMass,
    routeNGammaSewnTwistedCriticalChannelMass,
    Real.rpow_neg_one]

/-- The twisted-to-universal channel ratio is exactly the transverse modular cocycle. -/
theorem routeNGammaSewnTwistedCriticalChannelMass_eq_universal_mul_modularCocycle
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelMass t p =
      routeNGammaSewnUniversalCriticalChannelMass p *
        routeNGammaSewnTransverseModularCocycle t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnTwistedCriticalChannelMass,
    routeNGammaSewnUniversalCriticalChannelMass,
    routeNGammaSewnTransverseModularCocycle,
    routeNGammaSewnTransverseModularClockCocycle,
    ← Real.rpow_add hp0]
  congr 1
  ring

/-- Exact Radon--Nikodym ratio of the two positive marked channel masses. -/
theorem routeNGammaSewnTwisted_div_universal_eq_modularCocycle
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelMass t p /
        routeNGammaSewnUniversalCriticalChannelMass p =
      routeNGammaSewnTransverseModularCocycle t p := by
  rw [routeNGammaSewnTwistedCriticalChannelMass_eq_universal_mul_modularCocycle]
  have hmass : routeNGammaSewnUniversalCriticalChannelMass p ≠ 0 := by
    rw [routeNGammaSewnUniversalCriticalChannelMass]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
  exact mul_div_cancel_left₀ _ hmass

/-- Universal square-root channel amplitude. -/
def routeNGammaSewnUniversalCriticalChannelAmplitude
    (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-(1 / 2 : ℝ))

/-- Twisted square-root channel amplitude. -/
def routeNGammaSewnTwistedCriticalChannelAmplitude
    (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-(1 / 2 : ℝ) - |t|)

theorem routeNGammaSewnUniversalCriticalChannelAmplitude_sq
    (p : Nat.Primes) :
    routeNGammaSewnUniversalCriticalChannelAmplitude p ^ 2 =
      routeNGammaSewnUniversalCriticalChannelMass p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnUniversalCriticalChannelAmplitude,
    routeNGammaSewnUniversalCriticalChannelMass, pow_two,
    ← Real.rpow_add hp0]
  congr 1
  ring

theorem routeNGammaSewnTwistedCriticalChannelAmplitude_sq
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelAmplitude t p ^ 2 =
      routeNGammaSewnTwistedCriticalChannelMass t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnTwistedCriticalChannelAmplitude,
    routeNGammaSewnTwistedCriticalChannelMass, pow_two,
    ← Real.rpow_add hp0]
  congr 1
  ring

/-- The twisted amplitude is the universal amplitude multiplied by the square root of the
transverse modular cocycle. -/
theorem routeNGammaSewnTwistedCriticalChannelAmplitude_eq_universal_mul_sqrtCocycle
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnTwistedCriticalChannelAmplitude t p =
      routeNGammaSewnUniversalCriticalChannelAmplitude p *
        (p : ℝ) ^ (-|t|) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  rw [routeNGammaSewnTwistedCriticalChannelAmplitude,
    routeNGammaSewnUniversalCriticalChannelAmplitude,
    ← Real.rpow_add hp0]
  congr 1

/-- The existing prime-valuation Hellinger gap is literally the squared distance between the two
Route N critical marked-channel amplitudes. -/
theorem primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap
    (t : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap (-|t|) p =
      (routeNGammaSewnUniversalCriticalChannelAmplitude p -
        routeNGammaSewnTwistedCriticalChannelAmplitude t p) ^ 2 := by
  rw [primeValuationHellingerGap,
    routeNGammaSewnUniversalCriticalChannelAmplitude,
    routeNGammaSewnTwistedCriticalChannelAmplitude]
  congr 2
  ring

/-- **Kakutani/Krein polarization identity.**  Positive Hellinger defect is the canonical square
of the signed Route N Krein wall after division by the universal channel mass. -/
theorem primeValuationHellingerGap_neg_abs_eq_routeNKreinPolarization
    (t : ℝ) (p : Nat.Primes) :
    primeValuationHellingerGap (-|t|) p =
      (p : ℝ) * routeNGammaSewnCriticalHorizonKreinCharge t p ^ 2 /
        (1 + (p : ℝ) ^ (-|t|)) ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  let a : ℝ := (p : ℝ) ^ (-|t|)
  let u : ℝ := routeNGammaSewnUniversalCriticalChannelAmplitude p
  let q : ℝ := routeNGammaSewnCriticalHorizonKreinCharge t p
  have ha : 0 < a := Real.rpow_pos_of_pos hp0 _
  have hden : 1 + a ≠ 0 := by positivity
  have huSq : u ^ 2 = routeNGammaSewnUniversalCriticalChannelMass p := by
    exact routeNGammaSewnUniversalCriticalChannelAmplitude_sq p
  have hxuSq : (p : ℝ) * u ^ 2 = 1 := by
    rw [huSq, routeNGammaSewnUniversalCriticalChannelMass, Real.rpow_neg_one]
    exact mul_inv_cancel₀ hp0.ne'
  have htwisted :
      routeNGammaSewnTwistedCriticalChannelAmplitude t p = u * a := by
    exact routeNGammaSewnTwistedCriticalChannelAmplitude_eq_universal_mul_sqrtCocycle t p
  by_cases ht : t = 0
  · subst t
    norm_num [a, q, routeNGammaSewnCriticalHorizonKreinCharge_eq,
      primeValuationHellingerGap]
  · have hcocycleSq : routeNGammaSewnTransverseModularCocycle t p = a ^ 2 := by
      rw [routeNGammaSewnTransverseModularCocycle,
        routeNGammaSewnTransverseModularClockCocycle, pow_two,
        ← Real.rpow_add hp0]
      congr 1
      ring
    have hmodular := one_add_sign_mul_prime_mul_routeNKrein_eq_modularCocycle t p
    rw [hcocycleSq] at hmodular
    change 1 + Real.sign t * (p : ℝ) * q = a ^ 2 at hmodular
    have hqSq : (p : ℝ) ^ 2 * q ^ 2 = (1 - a ^ 2) ^ 2 := by
      rcases Real.sign_apply_eq_of_ne_zero t ht with hsign | hsign
      · rw [hsign] at hmodular
        nlinarith
      · rw [hsign] at hmodular
        nlinarith
    rw [primeValuationHellingerGap_neg_abs_eq_routeNCriticalAmplitudeGap,
      htwisted]
    change (u - u * a) ^ 2 = (p : ℝ) * q ^ 2 / (1 + a) ^ 2
    apply (eq_div_iff (pow_ne_zero 2 hden)).2
    calc
      (u - u * a) ^ 2 * (1 + a) ^ 2 =
          u ^ 2 * (1 - a ^ 2) ^ 2 := by ring
      _ = u ^ 2 * ((p : ℝ) ^ 2 * q ^ 2) := by rw [hqSq]
      _ = ((p : ℝ) * u ^ 2) * ((p : ℝ) * q ^ 2) := by ring
      _ = (p : ℝ) * q ^ 2 := by rw [hxuSq, one_mul]

/-- The product-measure normal sector and the Route N fixed-trace neutral sector are the same
source locus, now by an exact local polarization rather than by comparison of zero sets. -/
theorem summable_routeNKreinPolarization_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      (p : ℝ) * routeNGammaSewnCriticalHorizonKreinCharge t p ^ 2 /
        (1 + (p : ℝ) ^ (-|t|)) ^ 2) ↔
      t = 0 := by
  rw [show (fun p : Nat.Primes =>
      (p : ℝ) * routeNGammaSewnCriticalHorizonKreinCharge t p ^ 2 /
        (1 + (p : ℝ) ^ (-|t|)) ^ 2) =
      primeValuationHellingerGap (-|t|) by
    funext p
    exact (primeValuationHellingerGap_neg_abs_eq_routeNKreinPolarization t p).symm,
    summable_primeValuationHellingerGap_iff]
  constructor
  · intro h
    have habs : |t| = 0 := by linarith
    exact abs_eq_zero.mp habs
  · rintro rfl
    norm_num

end

end RHTower
