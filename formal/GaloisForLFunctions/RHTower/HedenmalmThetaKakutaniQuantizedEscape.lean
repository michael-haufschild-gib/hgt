import GaloisForLFunctions.RHTower.HedenmalmThetaPrimeSeamPolarizationBridge
import GaloisForLFunctions.RHTower.XiPrimeSeamPairAsymptotics

/-!
# Quantized harmonic escape of theta Kakutani polarization

The normalized FE--Schwarz seam energy has a sharper off-center law than harmonic coercivity.
For every nonneutral theta divisor copy, its finite-prime polarization energy divided by
reciprocal-prime mass tends to exactly one.  Functional-equation reflection doubles this limit.

The horizontal grade affects only an absolutely summable deficit.  Thus every oriented
off-center copy carries one universal harmonic escape unit, independent of its distance from the
critical line.  This is a source-facing quantized obstruction, not a source upper bound.
-/

open scoped BigOperators
open Filter

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Absolutely summable correction between one prime-harmonic atom and the normalized theta
polarization at a nonneutral grade. -/
def thetaKakutaniHarmonicDeficit (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  let d := |primeDepthBVWoldXiCenteredRate q.1|
  2 * (p : ℝ) ^ (-(1 + d)) - (p : ℝ) ^ (-(1 + 2 * d))

/-- Exact local normal form: theta polarization is the prime-harmonic atom times a squared radial
defect. -/
theorem thetaKakutaniFluxPolarization_eq_primeHarmonic_mul_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 =
      (1 / (p : ℝ)) *
        (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 := by
  rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq]
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hsplit :
      (p : ℝ) ^ (-(1 / 2 - -d)) =
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-d) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hhalfSq :
      ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (p : ℝ) := by
    rw [pow_two, ← Real.rpow_add hp0]
    rw [show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = (-1 : ℝ) by ring,
      Real.rpow_neg_one, one_div]
  rw [primeValuationHellingerGap]
  change ((p : ℝ) ^ (-(1 / 2 : ℝ)) -
      (p : ℝ) ^ (-(1 / 2 - -d))) ^ 2 = _
  rw [hsplit]
  calc
    ((p : ℝ) ^ (-(1 / 2 : ℝ)) -
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-d)) ^ 2 =
        ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
          (1 - (p : ℝ) ^ (-d)) ^ 2 := by ring
    _ = _ := by rw [hhalfSq]

/-- The normalized polarization plus its explicit radial deficit is exactly one reciprocal-prime
mass atom. -/
theorem thetaKakutaniFluxPolarization_add_deficit_eq_primeHarmonic
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
        thetaKakutaniHarmonicDeficit p q = 1 / (p : ℝ) := by
  rw [thetaKakutaniFluxPolarization_eq_primeHarmonic_mul_sq]
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hone : 1 / (p : ℝ) = (p : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  have hpd :
      (p : ℝ) ^ (-1 : ℝ) * (p : ℝ) ^ (-d) =
        (p : ℝ) ^ (-(1 + d)) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hp2d :
      (p : ℝ) ^ (-1 : ℝ) * ((p : ℝ) ^ (-d)) ^ 2 =
        (p : ℝ) ^ (-(1 + 2 * d)) := by
    rw [pow_two, ← Real.rpow_add hp0, ← Real.rpow_add hp0]
    congr 1
    ring
  rw [thetaKakutaniHarmonicDeficit]
  change 1 / (p : ℝ) * (1 - (p : ℝ) ^ (-d)) ^ 2 +
      (2 * (p : ℝ) ^ (-(1 + d)) -
        (p : ℝ) ^ (-(1 + 2 * d))) = 1 / (p : ℝ)
  rw [hone, ← hpd, ← hp2d]
  ring

/-- Away from the neutral theta fibre, the entire grade-dependent correction to harmonic mass is
absolutely summable over primes. -/
theorem summable_thetaKakutaniHarmonicDeficit_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Summable (fun p : Nat.Primes => thetaKakutaniHarmonicDeficit p q) := by
  have ha : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
    intro ha
    apply hflux
    rw [thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate, ha, mul_zero]
  have hd : 0 < |primeDepthBVWoldXiCenteredRate q.1| := abs_pos.mpr ha
  have hfirst : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-(1 + |primeDepthBVWoldXiCenteredRate q.1|))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hsecond : Summable (fun p : Nat.Primes =>
      (p : ℝ) ^ (-(1 + 2 * |primeDepthBVWoldXiCenteredRate q.1|))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  exact ((hfirst.mul_left 2).sub hsecond).congr (fun p => by
    simp only [thetaKakutaniHarmonicDeficit])

/-- Renormalized theta polarization has a finite prime sum: subtracting one reciprocal-prime atom
per prime leaves precisely the negative summable deficit. -/
theorem hasSum_thetaKakutaniFluxPolarization_sub_primeHarmonic
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    HasSum (fun p : Nat.Primes =>
      thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 -
        1 / (p : ℝ))
      (-∑' p : Nat.Primes, thetaKakutaniHarmonicDeficit p q) := by
  apply (summable_thetaKakutaniHarmonicDeficit_of_boundaryFlux_ne_zero q hflux).hasSum.neg.congr_fun
  intro p
  have h := thetaKakutaniFluxPolarization_add_deficit_eq_primeHarmonic p q
  linarith

/-- **Universal one-copy escape law.** Every nonneutral oriented theta copy consumes asymptotically
one full unit of reciprocal-prime mass, regardless of horizontal displacement. -/
theorem tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_of_boundaryFlux_ne_zero
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
            primeReciprocalMass s)
      atTop (nhds 1) := by
  have hdiff : Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) -
            primeReciprocalMass s)
      atTop
      (nhds (-∑' p : Nat.Primes, thetaKakutaniHarmonicDeficit p q)) := by
    have h := hasSum_thetaKakutaniFluxPolarization_sub_primeHarmonic q hflux
    change Tendsto
      (fun s : Finset Nat.Primes =>
        ∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 -
            1 / (p : ℝ)))
      atTop
      (nhds (-∑' p : Nat.Primes, thetaKakutaniHarmonicDeficit p q)) at h
    simpa only [primeReciprocalMass, Finset.sum_sub_distrib] using h
  have hzero : Tendsto
      (fun s : Finset Nat.Primes =>
        ((∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) -
            primeReciprocalMass s) / primeReciprocalMass s)
      atTop (nhds 0) :=
    hdiff.div_atTop tendsto_primeReciprocalMass_atTop
  have hone := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  have hmasspos : ∀ᶠ s : Finset Nat.Primes in atTop, 0 < primeReciprocalMass s :=
    tendsto_primeReciprocalMass_atTop.eventually (eventually_gt_atTop 0)
  have heq :
      (fun s : Finset Nat.Primes =>
        1 +
          ((∑ p ∈ s,
            thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) -
              primeReciprocalMass s) / primeReciprocalMass s) =ᶠ[atTop]
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
            primeReciprocalMass s) := by
    filter_upwards [hmasspos] with s hs
    field_simp [hs.ne']
    simp only [mul_comm]
    ring
  simpa only [add_zero] using hone.congr' heq

/-- Quantized harmonic escape index: zero on a neutral copy and one on every nonneutral oriented
copy. -/
def thetaKakutaniHarmonicEscapeIndex (q : XiZeroCopy) : ℝ :=
  if thetaXiRankTwoBoundaryFlux q = 0 then 0 else 1

/-- The cofinal normalized energy always converges and its limit is the quantized escape index. -/
theorem tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass
    (q : XiZeroCopy) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
            primeReciprocalMass s)
      atTop (nhds (thetaKakutaniHarmonicEscapeIndex q)) := by
  by_cases hflux : thetaXiRankTwoBoundaryFlux q = 0
  · simp [thetaKakutaniHarmonicEscapeIndex, hflux]
  · simpa [thetaKakutaniHarmonicEscapeIndex, hflux] using
      tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_of_boundaryFlux_ne_zero
        q hflux

/-- Vanishing harmonic escape is exactly same-fibre theta-current neutrality. -/
theorem tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_zero_iff
    (q : XiZeroCopy) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
            primeReciprocalMass s)
      atTop (nhds 0) ↔ thetaXiRankTwoBoundaryFlux q = 0 := by
  constructor
  · intro hzero
    by_contra hflux
    have hone :=
      tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_of_boundaryFlux_ne_zero
        q hflux
    have : (1 : ℝ) = 0 := tendsto_nhds_unique hone hzero
    norm_num at this
  · intro hflux
    simp [hflux]

/-- Route P node positivity is exactly zero quantized harmonic escape. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_harmonicEscape_zero
    (q : XiZeroCopy) :
    (exists r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      Tendsto
        (fun s : Finset Nat.Primes =>
          (∑ p ∈ s,
            thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
              primeReciprocalMass s)
        atTop (nhds 0) := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero,
    tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_zero_iff]

/-- A nonneutral reflected pair has escape index two: reflection cancels signed current but adds
two full harmonic units. -/
theorem tendsto_reflectionPairKakutaniFluxPolarization_div_primeReciprocalMass
    (q : XiZeroCopy) (hflux : thetaXiRankTwoBoundaryFlux q ≠ 0) :
    Tendsto
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
            thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2)) /
            primeReciprocalMass s)
      atTop (nhds 2) := by
  have htwo :=
    (tendsto_thetaKakutaniFluxPolarization_div_primeReciprocalMass_of_boundaryFlux_ne_zero
      q hflux).const_mul 2
  have heq :
      (fun s : Finset Nat.Primes =>
        2 * ((∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) /
            primeReciprocalMass s)) =
      (fun s : Finset Nat.Primes =>
        (∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
            thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2)) /
            primeReciprocalMass s) := by
    funext s
    have hsum :
        (∑ p ∈ s,
          (thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
            thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
              thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2)) =
          2 * (∑ p ∈ s,
            thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) := by
      calc
        _ = ∑ p ∈ s,
            2 * (thetaKakutaniFluxPositiveUnit p q *
              thetaXiRankTwoBoundaryFlux q ^ 2) := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [thetaKakutaniFluxPolarization_add_reflect_eq_two_gap,
                primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq]
        _ = _ := by rw [Finset.mul_sum]
    rw [hsum]
    ring
  simpa only [mul_one] using
    htwo.congr' (Filter.Eventually.of_forall fun s => congrFun heq s)

end

end RHTower.HedenmalmThetaSource
