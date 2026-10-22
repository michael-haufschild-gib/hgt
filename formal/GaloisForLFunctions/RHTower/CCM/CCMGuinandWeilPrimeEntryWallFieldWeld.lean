import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilPrimeEntryThirdJetConnection
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalWallFieldSquareRootWeld

/-!
# CCM prime-entry third jet / Suzuki wall-field weld

The first CCM source channel visible after centering is the cubic prime-entry jet.  Suzuki's
critical entry-wall construction carries an apparently different object: one complex wall field
whose square is the far delayed-hinge numerator.  This file proves that these are the same source
after one forced local renormalization.

For the prime power `k = p^(e+1)`, let `a_k = log(k)/2` be its entry-wall aperture, `W_k(t)` its
Suzuki wall field, and `q_k` the CCM cubic Loewner scale.  Then

`q_k exp(i t log k) = (4 / a_k^(3 : ℕ)) W_k(t)^(2 : ℕ)`.

At zero height this says `q_k = 4 |W_k(0)|^(2 : ℕ) / a_k^(3 : ℕ)`.  Consequently the whole CCM cubic matrix,
and its centered quadratic form, are exactly normalized Suzuki wall-field energy.  This is a
phase-complete source identification, not a comparison of asymptotic orders.

No RH premise, estimate, numerical computation, positivity assumption, or added axiom is used.
-/

open scoped BigOperators

namespace RHTower

open Matrix

noncomputable section

/-! ## Atomic arithmetic weld -/

/-- The critical Mellin mass of a prime power is the square of Suzuki's bare entry-wall
amplitude. -/
theorem criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude
    (p : Nat.Primes) (e : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) =
      suzukiCriticalEntryWallBareAmplitude p e ^ 2 := by
  rw [sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  unfold criticalMellinAtomWeight
  have hn : 0 < (xiGammaEulerValuationNat (p, e) : ℝ) := by
    exact_mod_cast (pow_pos p.property.pos (e + 1))
  have hexp : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  rw [hexp, Real.rpow_neg hn.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

/-- In logarithmic coordinates, the CCM cubic scale is the squared wall amplitude divided by the
third power of the full prime-power delay. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallAmplitude_sq_div_log_cube
    (p : Nat.Primes) (e : ℕ) :
    ccmGuinandWeilPrimeEntryThirdJetScale
        (xiGammaEulerValuationNat (p, e)) =
      32 * suzukiCriticalEntryWallBareAmplitude p e ^ 2 /
        Real.log (xiGammaEulerValuationNat (p, e) : ℝ) ^ 3 := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale,
    criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude]

/-- **Cubic aperture calibration.**  Since the entry wall is at half the logarithmic delay, the
coefficient `32 / log(k)^(3 : ℕ)` becomes exactly `4 / a_k^(3 : ℕ)`. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_four_wallAmplitude_sq_div_aperture_cube
    (p : Nat.Primes) (e : ℕ) :
    ccmGuinandWeilPrimeEntryThirdJetScale
        (xiGammaEulerValuationNat (p, e)) =
      4 * suzukiCriticalEntryWallBareAmplitude p e ^ 2 /
        suzukiPrimePowerEntryWallAperture p e ^ 3 := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallAmplitude_sq_div_log_cube,
    ← two_mul_suzukiPrimePowerEntryWallAperture]
  ring

/-! ## Wall-field energy form -/

/-- At spectral height zero, the Suzuki wall field is exactly its real bare amplitude. -/
theorem suzukiCriticalWallField_zero_eq_bareAmplitude
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField 0 p e =
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ) := by
  rw [suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  simp [suzukiOscillatoryKernel]

/-- Zero-height wall-field energy is the square of the bare amplitude. -/
theorem normSq_suzukiCriticalWallField_zero
    (p : Nat.Primes) (e : ℕ) :
    Complex.normSq (suzukiCriticalWallField 0 p e) =
      suzukiCriticalEntryWallBareAmplitude p e ^ 2 := by
  rw [suzukiCriticalWallField_zero_eq_bareAmplitude]
  simp [Complex.normSq]
  ring

/-- The CCM cubic rate is normalized zero-height Suzuki wall-field energy. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallField_energy_div_aperture_cube
    (p : Nat.Primes) (e : ℕ) :
    ccmGuinandWeilPrimeEntryThirdJetScale
        (xiGammaEulerValuationNat (p, e)) =
      4 * Complex.normSq (suzukiCriticalWallField 0 p e) /
        suzukiPrimePowerEntryWallAperture p e ^ 3 := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_four_wallAmplitude_sq_div_aperture_cube,
    normSq_suzukiCriticalWallField_zero]

/-- Every canonical prime-power index is strictly above one. -/
theorem one_lt_xiGammaEulerValuationNat (p : Nat.Primes) (e : ℕ) :
    1 < xiGammaEulerValuationNat (p, e) := by
  simp only [xiGammaEulerValuationNat]
  exact one_lt_pow₀ p.property.one_lt (by omega)

/-- Every canonical prime-power index is a genuine prime power. -/
theorem isPrimePow_xiGammaEulerValuationNat (p : Nat.Primes) (e : ℕ) :
    IsPrimePow (xiGammaEulerValuationNat (p, e)) := by
  refine ⟨p, e + 1, ?_, by omega, rfl⟩
  exact p.property.prime

/-- Normalized zero-height wall-field energy is strictly positive at every prime-power wall. -/
theorem ccmSuzukiPrimeEntryWallFieldEnergyRate_pos (p : Nat.Primes) (e : ℕ) :
    0 < 4 * Complex.normSq (suzukiCriticalWallField 0 p e) /
      suzukiPrimePowerEntryWallAperture p e ^ 3 := by
  rw [←
    ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallField_energy_div_aperture_cube]
  exact ccmGuinandWeilPrimeEntryThirdJetScale_pos
    (isPrimePow_xiGammaEulerValuationNat p e)

/-! ## Phase-complete square-root weld -/

/-- The CCM cubic source with its full-delay phase is the Suzuki wall-field square with forced
logarithmic cubic normalization. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_mul_fullPhase_eq_wallField_sq_div_log_cube
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    (ccmGuinandWeilPrimeEntryThirdJetScale
          (xiGammaEulerValuationNat (p, e)) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) =
      (32 / Real.log (xiGammaEulerValuationNat (p, e) : ℝ) ^ 3 : ℝ) *
        suzukiCriticalWallField t p e ^ 2 := by
  have hweight :
      criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) =
        ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) := by
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
      sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  rw [ccmGuinandWeilPrimeEntryThirdJetScale,
    sq_suzukiCriticalWallField_eq_farHingeNumerator, hweight]
  push_cast
  ring

/-- **Phase-complete CCM/Suzuki weld.**  The first centered CCM source is precisely the symmetric
square of the Suzuki wall field, divided by the cube of its entry-wall aperture. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_mul_fullPhase_eq_four_wallField_sq_div_aperture_cube
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    (ccmGuinandWeilPrimeEntryThirdJetScale
          (xiGammaEulerValuationNat (p, e)) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) =
      (4 / suzukiPrimePowerEntryWallAperture p e ^ 3 : ℝ) *
        suzukiCriticalWallField t p e ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale_mul_fullPhase_eq_wallField_sq_div_log_cube,
    ← two_mul_suzukiPrimePowerEntryWallAperture]
  push_cast
  ring

/-! ## Matrix and centered-sector consequences -/

/-- The whole prime-entry cubic Loewner matrix is universal shape scaled by normalized Suzuki
wall-field energy. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_primePower_eq_wallFieldEnergy_smul
    (p : Nat.Primes) (e N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet3
        (xiGammaEulerValuationNat (p, e)) N =
      (4 * Complex.normSq (suzukiCriticalWallField 0 p e) /
          suzukiPrimePowerEntryWallAperture p e ^ 3) •
        ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_scale_smul
      (one_lt_xiGammaEulerValuationNat p e),
    ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallField_energy_div_aperture_cube]

/-- On the zero-sum sector, the prime-entry cubic form is the first clock-moment square weighted
by normalized Suzuki wall-field energy. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_primePower_quadratic_eq_wallFieldEnergy
    (p : Nat.Primes) (e N : ℕ)
    (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v
        (ccmGuinandWeilPrimeEntryCenteredMatrixJet3
          (xiGammaEulerValuationNat (p, e)) N *ᵥ v) =
      8 * Real.pi ^ 2 * Complex.normSq (suzukiCriticalWallField 0 p e) /
          suzukiPrimePowerEntryWallAperture p e ^ 3 *
        (∑ i, ccmPublishedCenteredClock N i * v i) ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_quadratic_of_sum_eq_zero
      (one_lt_xiGammaEulerValuationNat p e) N v hv,
    ccmGuinandWeilPrimeEntryThirdJetScale_primePower_eq_wallField_energy_div_aperture_cube]
  ring

end

end RHTower
