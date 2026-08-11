import GaloisForLFunctions.RHTower.HedenmalmThetaRouteRPositiveUnitCurrentBridge
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnKakutaniPolarizationBridge

/-!
# Theta Green current as a Kakutani polarization

The signed Route P theta boundary flux and the positive Route N Kakutani defect are two
polarizations of one centered Xi grade.  The bridge must remain valid at neutral grade, so the
ratio of the Route N Krein charge by the grade is completed by its removable value
`2 log(p) / p`.

Prime by prime, the Hellinger defect is then a strictly positive unit times the square of the
actual theta Green flux.  Functional-equation reflection can cancel the signed flux, but cannot
cancel this polarization.  Its all-prime summability is exactly positivity of the corresponding
Route P reciprocal-square node.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Positive removable completion of minus the Route N Krein current divided by centered grade. -/
def thetaRouteNKreinSlope (t : ℝ) (p : Nat.Primes) : ℝ :=
  if t = 0 then
    2 * Real.log (p : ℝ) / (p : ℝ)
  else
    -routeNGammaSewnCriticalHorizonKreinCharge t p / t

/-- The signed Route N current is centered grade times its completed positive slope. -/
theorem routeNGammaSewnCriticalHorizonKreinCharge_eq_neg_grade_mul_slope
    (t : ℝ) (p : Nat.Primes) :
    routeNGammaSewnCriticalHorizonKreinCharge t p =
      -t * thetaRouteNKreinSlope t p := by
  rw [thetaRouteNKreinSlope]
  by_cases ht : t = 0
  · subst t
    simp [routeNGammaSewnCriticalHorizonKreinCharge_eq]
  · rw [if_neg ht]
    field_simp [ht]

/-- The completed Krein slope is strictly positive at every grade, including the neutral fibre. -/
theorem thetaRouteNKreinSlope_pos (t : ℝ) (p : Nat.Primes) :
    0 < thetaRouteNKreinSlope t p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  rw [thetaRouteNKreinSlope]
  by_cases ht : t = 0
  · subst t
    rw [if_pos rfl]
    exact div_pos (mul_pos (by norm_num) (Real.log_pos hp1)) hp0
  · rw [if_neg ht]
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hpow : (p : ℝ) ^ t < (p : ℝ) ^ (-t) :=
        Real.strictMono_rpow_of_base_gt_one hp1 (by linarith)
      have hqpos : 0 < routeNGammaSewnCriticalHorizonKreinCharge t p := by
        rw [routeNGammaSewnCriticalHorizonKreinCharge_eq]
        exact div_pos
          (mul_pos (Real.rpow_pos_of_pos hp0 _) (sub_pos.mpr hpow)) hp0
      exact div_pos_of_neg_of_neg (neg_neg_of_pos hqpos) htneg
    · have hpow : (p : ℝ) ^ (-t) < (p : ℝ) ^ t :=
        Real.strictMono_rpow_of_base_gt_one hp1 (by linarith)
      have hqneg : routeNGammaSewnCriticalHorizonKreinCharge t p < 0 := by
        rw [routeNGammaSewnCriticalHorizonKreinCharge_eq]
        exact div_neg_of_neg_of_pos
          (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hp0 _) (sub_neg.mpr hpow)) hp0
      exact div_pos (neg_pos.mpr hqneg) htpos

/-- Theta Green flux is centered Xi grade times one fixed negative orientation and positive
theta mass-energy scale. -/
theorem thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate
    (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q =
      -(thetaSource.mass * thetaXiRootEnergy q) *
        primeDepthBVWoldXiCenteredRate q.1 := by
  rw [thetaXiRankTwoBoundaryFlux_eq,
    primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
  ring

/-- Functional-equation reflection reverses the centered Xi grade. -/
theorem primeDepthBVWoldXiCenteredRate_copyReflect (q : XiZeroCopy) :
    primeDepthBVWoldXiCenteredRate (xiZeroCopyReflectEquiv q).1 =
      -primeDepthBVWoldXiCenteredRate q.1 := by
  rw [primeDepthBVWoldXiCenteredRate, primeDepthBVWoldXiCenteredRate]
  change 2 * (1 - (q.1 : ℂ)).re - 1 = -(2 * (q.1 : ℂ).re - 1)
  simp
  ring

/-- Explicit positive calibration from squared theta Green flux to local Kakutani defect. -/
def thetaKakutaniFluxPositiveUnit
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  let a := primeDepthBVWoldXiCenteredRate q.1
  (p : ℝ) * thetaRouteNKreinSlope a p ^ 2 /
    ((1 + (p : ℝ) ^ (-|a|)) ^ 2 *
      (thetaSource.mass * thetaXiRootEnergy q) ^ 2)

theorem thetaKakutaniFluxPositiveUnit_pos
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaKakutaniFluxPositiveUnit p q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hclock : 0 < (p : ℝ) ^
      (-|primeDepthBVWoldXiCenteredRate q.1|) :=
    Real.rpow_pos_of_pos hp0 _
  have hslope := thetaRouteNKreinSlope_pos
    (primeDepthBVWoldXiCenteredRate q.1) p
  have hmassEnergy : 0 < thetaSource.mass * thetaXiRootEnergy q :=
    mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)
  rw [thetaKakutaniFluxPositiveUnit]
  exact div_pos
    (mul_pos hp0 (sq_pos_of_pos hslope))
    (mul_pos (sq_pos_of_pos (by linarith)) (sq_pos_of_pos hmassEnergy))

/-- **Exact P/N positive-unit merger.**  Local Hellinger defect is the canonical positive
polarization of the oriented theta Green current.  No division by horizontal grade occurs. -/
theorem primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    primeValuationHellingerGap
        (-|primeDepthBVWoldXiCenteredRate q.1|) p =
      thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 := by
  rw [primeValuationHellingerGap_neg_abs_eq_routeNKreinPolarization,
    routeNGammaSewnCriticalHorizonKreinCharge_eq_neg_grade_mul_slope,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate,
    thetaKakutaniFluxPositiveUnit]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hden : 1 + (p : ℝ) ^
      (-|primeDepthBVWoldXiCenteredRate q.1|) ≠ 0 := by positivity
  have hmassEnergy : thetaSource.mass * thetaXiRootEnergy q ≠ 0 :=
    (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  field_simp [hden, hmassEnergy, thetaSource.mass_ne_zero,
    (thetaXiRootEnergy_pos q).ne']

/-- Reflection adds, rather than cancels, after canonical positive polarization: the pair carries
twice the same local Hellinger defect. -/
theorem thetaKakutaniFluxPolarization_add_reflect_eq_two_gap
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
        thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
          thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2 =
      2 * primeValuationHellingerGap
        (-|primeDepthBVWoldXiCenteredRate q.1|) p := by
  rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq p q,
    ← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq p
      (xiZeroCopyReflectEquiv q),
    primeDepthBVWoldXiCenteredRate_copyReflect, abs_neg]
  ring

/-- The local polarization is nonnegative and is strictly positive exactly off the neutral
theta boundary locus. -/
theorem thetaKakutaniFluxPolarization_pos_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro h hzero
    rw [hzero, zero_pow (by norm_num), mul_zero] at h
    exact (lt_irrefl 0) h
  · intro h
    exact mul_pos (thetaKakutaniFluxPositiveUnit_pos p q)
      (sq_pos_of_ne_zero h)

/-- The reflection-pair polarization is strictly positive exactly when the original signed
current is nonzero; the anti-current cancellation has disappeared. -/
theorem thetaKakutaniFluxPolarization_add_reflect_pos_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
        thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
          thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2 ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  constructor
  · intro h hzero
    have hreflect :
        thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) = 0 := by
      rw [thetaXiRankTwoBoundaryFlux_reflect, hzero, neg_zero]
    rw [hzero, hreflect] at h
    norm_num at h
  · intro h
    have hfirst :
        0 < thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 :=
      (thetaKakutaniFluxPolarization_pos_iff p q).2 h
    have hsecond :
        0 ≤ thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
          thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2 :=
      mul_nonneg (thetaKakutaniFluxPositiveUnit_pos p _).le (sq_nonneg _)
    linarith

/-- All-prime summability of the positive theta-flux polarization is exactly boundary-current
neutrality.  This is the precise source-domain condition still needed by Route P. -/
theorem summable_thetaKakutaniFluxPolarization_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [show (fun p : Nat.Primes =>
      thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) =
        primeValuationHellingerGap
          (-|primeDepthBVWoldXiCenteredRate q.1|) by
    funext p
    exact (primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq p q).symm,
    summable_primeValuationHellingerGap_iff]
  constructor
  · intro h
    have habs : |primeDepthBVWoldXiCenteredRate q.1| = 0 := by linarith
    have ha : primeDepthBVWoldXiCenteredRate q.1 = 0 := abs_eq_zero.mp habs
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, ha, mul_zero]
  · intro hflux
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate] at hflux
    have hmassEnergy :
        -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
      neg_ne_zero.mpr
        (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
    have ha : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hflux).resolve_left hmassEnergy
    simp [ha]

/-- Route P node positivity is equivalent to all-prime admission of its canonical positive
theta-current polarization. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_summable_kakutaniFluxPolarization
    (q : XiZeroCopy) :
    (exists r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      Summable (fun p : Nat.Primes =>
        thetaKakutaniFluxPositiveUnit p q *
          thetaXiRankTwoBoundaryFlux q ^ 2) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    summable_thetaKakutaniFluxPolarization_iff_boundaryFlux_zero]

end

end RHTower.HedenmalmThetaSource
