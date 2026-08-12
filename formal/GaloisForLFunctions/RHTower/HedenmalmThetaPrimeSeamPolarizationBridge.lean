import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniHarmonicCoercivity

/-!
# Canonical prime seam / theta polarization bridge

The literal FE--Schwarz seam charge already carries the positive Route P current.  For horizontal
centered grade `a = 2 Re(rho) - 1`, its squared norm is the local Hellinger/theta polarization
multiplied by the forced positive source scale `(log p)^2 p^|a|`.

This is a coefficient-faithful source-to-theta transport, not a zero-set comparison.  It leaves
one precise producer estimate: uniformly bound the normalized finite-prime seam energy on actual
theta divisor modes.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Prime-clock reflected energy is the local Hellinger defect times the exact absolute-grade
source gauge. -/
theorem primeClockReflectionEnergy_eq_absCenteredGauge_mul_hellingerGap
    (sigma : ℝ) (p : Nat.Primes) :
    primeClockReflectionEnergy sigma p =
      (p : ℝ) ^ |2 * sigma - 1| *
        primeValuationHellingerGap (-|2 * sigma - 1|) p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  by_cases hsigma : sigma ≤ 1 / 2
  · have habs : |2 * sigma - 1| = 1 - 2 * sigma := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs, primeClockReflectionEnergy, primeValuationHellingerGap]
    have hsquare :
        (p : ℝ) ^ (1 - 2 * sigma) =
          ((p : ℝ) ^ ((1 - 2 * sigma) / 2)) ^ 2 := by
      rw [pow_two, ← Real.rpow_add hp0]
      congr 1
      ring
    have hleft :
        (p : ℝ) ^ ((1 - 2 * sigma) / 2) *
            (p : ℝ) ^ (-(1 / 2 : ℝ)) =
          (p : ℝ) ^ (-sigma) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hright :
        (p : ℝ) ^ ((1 - 2 * sigma) / 2) *
            (p : ℝ) ^ (-(1 / 2 - -(1 - 2 * sigma))) =
          (p : ℝ) ^ (-(1 - sigma)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    rw [hsquare, ← mul_pow, mul_sub, hleft, hright]
  · have hsigma' : 1 / 2 < sigma := lt_of_not_ge hsigma
    have habs : |2 * sigma - 1| = 2 * sigma - 1 := by
      rw [abs_of_pos (by linarith)]
    rw [habs, primeClockReflectionEnergy, primeValuationHellingerGap]
    have hsquare :
        (p : ℝ) ^ (2 * sigma - 1) =
          ((p : ℝ) ^ ((2 * sigma - 1) / 2)) ^ 2 := by
      rw [pow_two, ← Real.rpow_add hp0]
      congr 1
      ring
    have hleft :
        (p : ℝ) ^ ((2 * sigma - 1) / 2) *
            (p : ℝ) ^ (-(1 / 2 : ℝ)) =
          (p : ℝ) ^ (-(1 - sigma)) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hright :
        (p : ℝ) ^ ((2 * sigma - 1) / 2) *
            (p : ℝ) ^ (-(1 / 2 - -(2 * sigma - 1))) =
          (p : ℝ) ^ (-sigma) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    rw [hsquare, ← mul_pow, mul_sub, hleft, hright]
    ring

/-- Forced strictly positive calibration from local theta polarization to the literal canonical
FE--Schwarz prime seam norm. -/
def thetaPrimeSeamPolarizationPositiveUnit
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  (Real.log (p : ℝ)) ^ 2 *
    (p : ℝ) ^ |primeDepthBVWoldXiCenteredRate q.1|

theorem thetaPrimeSeamPolarizationPositiveUnit_pos
    (p : Nat.Primes) (q : XiZeroCopy) :
    0 < thetaPrimeSeamPolarizationPositiveUnit p q := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  rw [thetaPrimeSeamPolarizationPositiveUnit]
  exact mul_pos (sq_pos_of_pos (Real.log_pos hp1)) (Real.rpow_pos_of_pos hp0 _)

/-- **Exact source/P merger.**  Squared norm of the literal FE--Schwarz seam is a strictly
positive source unit times the canonical theta Green-current polarization. -/
theorem norm_sq_orbitwisePrimeSeamCharge_eq_positiveUnit_mul_thetaPolarization
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 =
      thetaPrimeSeamPolarizationPositiveUnit p q *
        (thetaKakutaniFluxPositiveUnit p q *
          thetaXiRankTwoBoundaryFlux q ^ 2) := by
  rw [norm_sq_orbitwiseNatPrimeSeamCharge_eq_log_sq_mul_primeClockReflectionEnergy,
    primeClockReflectionEnergy_eq_absCenteredGauge_mul_hellingerGap]
  change (Real.log (p : ℝ)) ^ 2 *
      ((p : ℝ) ^ |primeDepthBVWoldXiCenteredRate q.1| *
        primeValuationHellingerGap
          (-|primeDepthBVWoldXiCenteredRate q.1|) p) = _
  rw [
    primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq,
    thetaPrimeSeamPolarizationPositiveUnit]
  ring

/-- The normalized literal seam energy is exactly the theta polarization, without division by a
horizontal grade. -/
theorem norm_sq_orbitwisePrimeSeamCharge_div_sourceUnit_eq_thetaPolarization
    (p : Nat.Primes) (q : XiZeroCopy) :
    ‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 /
        thetaPrimeSeamPolarizationPositiveUnit p q =
      thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 := by
  rw [norm_sq_orbitwisePrimeSeamCharge_eq_positiveUnit_mul_thetaPolarization]
  field_simp [(thetaPrimeSeamPolarizationPositiveUnit_pos p q).ne']

/-- At one prime, vanishing of the literal source seam is exactly positivity of the corresponding
individual Route P squared node. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_primeSeamCharge_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    (exists r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ) = 0 := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero]
  constructor
  · intro hflux
    have hnorm :=
      norm_sq_orbitwisePrimeSeamCharge_eq_positiveUnit_mul_thetaPolarization p q
    rw [hflux, zero_pow (by norm_num), mul_zero, mul_zero] at hnorm
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  · intro hseam
    have hnorm :=
      norm_sq_orbitwisePrimeSeamCharge_eq_positiveUnit_mul_thetaPolarization p q
    rw [hseam, norm_zero, zero_pow (by norm_num)] at hnorm
    have hproduct :
        thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 = 0 :=
      (mul_eq_zero.mp hnorm.symm).resolve_left
        (thetaPrimeSeamPolarizationPositiveUnit_pos p q).ne'
    have hsq : thetaXiRankTwoBoundaryFlux q ^ 2 = 0 :=
      (mul_eq_zero.mp hproduct).resolve_left
        (thetaKakutaniFluxPositiveUnit_pos p q).ne'
    exact sq_eq_zero_iff.mp hsq

/-- Uniform boundedness of normalized finite-prime seam energy is exactly positivity of one Route
P node.  This is the coefficient-faithful finite-stage source contract. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_normalizedPrimeSeamEnergy
    (q : XiZeroCopy) :
    (exists r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      exists C : ℝ, ∀ s : Finset Nat.Primes,
        ∑ p ∈ s,
          ‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 /
            thetaPrimeSeamPolarizationPositiveUnit p q ≤ C := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_finset_polarization_bound]
  apply exists_congr
  intro C
  apply forall_congr'
  intro s
  have hsum :
      (∑ p ∈ s,
          ‖orbitwiseNatPrimeSeamCharge (p : ℕ) (q.1 : ℂ)‖ ^ 2 /
            thetaPrimeSeamPolarizationPositiveUnit p q) =
        ∑ p ∈ s,
          thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 := by
    apply Finset.sum_congr rfl
    intro p _
    exact norm_sq_orbitwisePrimeSeamCharge_div_sourceUnit_eq_thetaPolarization p q
  rw [hsum]

end

end RHTower.HedenmalmThetaSource
