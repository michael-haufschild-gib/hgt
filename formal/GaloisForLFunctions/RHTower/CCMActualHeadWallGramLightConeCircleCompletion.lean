import GaloisForLFunctions.RHTower.CCMActualHeadWallGramSignedProducer
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedWallLightThirdJetTransmutation

/-!
# Circle completion of the actual CCM wall Gram by Suzuki light orientation

The actual-head prime channel records the reflected wall chord, hence only the cosine coordinate
of each prime-power phase. The literal Suzuki light imbalance supplies the missing sine coordinate.
Together they reconstruct the full anti-diagonal wall Gram and obey an exact circle law.
-/

open Complex
open scoped ComplexConjugate

noncomputable section
namespace RHTower

/-- Canonical complex completion of actual chord energy by literal wall-light orientation. -/
def ccmActualHeadWallLightCompletedPhase
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  let n := xiGammaEulerValuationNat (p, e)
  ((criticalMellinAtomWeight n -
      normSq (ccmActualHeadMellinWallChord xi n) / 2 : ℝ) : ℂ) +
    I * (ccmActualHeadMatchedWallLightImbalance p e xi : ℂ)

/-- The chord-complement coordinate is exactly the real anti-diagonal wall Gram. -/
theorem criticalWeight_sub_half_chord_eq_wallGram_re
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    criticalMellinAtomWeight n -
        normSq (ccmActualHeadMellinWallChord xi n) / 2 =
      (suzukiCriticalWallFieldGramKernel
        (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e).re := by
  let n := xiGammaEulerValuationNat (p, e)
  have hweight :
      criticalMellinAtomWeight n =
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
      sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  have hchord :=
    normSq_suzukiCriticalWallField_reflectedChord_eq_diagonal_sub_re_antidiagonal
      xi p e
  rw [← ccmActualHeadMellinWallChord_primePower_eq_suzukiCriticalWallField_sub]
    at hchord
  change normSq (ccmActualHeadMellinWallChord xi n) = _ at hchord
  rw [← hweight] at hchord
  dsimp only
  linarith

/-- Literal light imbalance is exactly the imaginary anti-diagonal wall Gram. -/
theorem ccmActualHeadMatchedWallLightImbalance_eq_wallGram_im
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadMatchedWallLightImbalance p e xi =
      (suzukiCriticalWallFieldGramKernel
        (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e).im := by
  have hlight :=
    normSq_suzukiCriticalWallPositiveLightAmplitude_sub_negative
      (2 * Real.pi * xi) p e
  change ccmActualHeadMatchedWallLightImbalance p e xi = _
  rw [ccmActualHeadMatchedWallLightImbalance]
  rw [hlight]
  congr 1
  rw [suzukiCriticalWallFieldGramKernel, suzukiCriticalWallField_neg_eq_star,
    star_star, ← pow_two]

/-- Complex completion theorem: actual chord data plus light orientation is the full source phase. -/
theorem ccmActualHeadWallLightCompletedPhase_eq_wallGram
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    ccmActualHeadWallLightCompletedPhase xi p e =
      suzukiCriticalWallFieldGramKernel
        (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e := by
  apply Complex.ext
  · simp only [ccmActualHeadWallLightCompletedPhase, add_re, ofReal_re,
      mul_re, I_re, ofReal_im, I_im, zero_mul, mul_zero, sub_zero, add_zero]
    exact criticalWeight_sub_half_chord_eq_wallGram_re xi p e
  · simp only [ccmActualHeadWallLightCompletedPhase, add_im, ofReal_im,
      mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]
    exact ccmActualHeadMatchedWallLightImbalance_eq_wallGram_im xi p e

/-- Exact circle law: chord coordinate and oriented light coordinate retain full critical mass. -/
theorem ccmActualHeadWallChord_lightImbalance_circle
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    (criticalMellinAtomWeight n -
        normSq (ccmActualHeadMellinWallChord xi n) / 2) ^ (2 : ℕ) +
      ccmActualHeadMatchedWallLightImbalance p e xi ^ (2 : ℕ) =
        criticalMellinAtomWeight n ^ (2 : ℕ) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hweight :
      criticalMellinAtomWeight n =
        ArithmeticFunction.vonMangoldt n / Real.sqrt (n : ℝ) := by
    dsimp only [n]
    rw [criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
      sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  have hre := criticalWeight_sub_half_chord_eq_wallGram_re xi p e
  have him := ccmActualHeadMatchedWallLightImbalance_eq_wallGram_im xi p e
  have hpolar := suzukiCriticalWallFieldGramKernel_antidiagonal_re_im
    (2 * Real.pi * xi) p e
  dsimp only at hre ⊢
  rw [hre, him, hpolar.1, hpolar.2, ← hweight]
  have htrig := Real.sin_sq_add_cos_sq
    ((2 * Real.pi * xi) * Real.log (n : ℝ))
  nlinarith

/-- The actual chord determines the magnitude, but not the sign, of the light orientation. -/
theorem ccmActualHeadWallLightImbalance_sq_eq_chord_mul_complement
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    ccmActualHeadMatchedWallLightImbalance p e xi ^ (2 : ℕ) =
      normSq (ccmActualHeadMellinWallChord xi n) *
        (criticalMellinAtomWeight n -
          normSq (ccmActualHeadMellinWallChord xi n) / 4) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hcircle := ccmActualHeadWallChord_lightImbalance_circle xi p e
  dsimp only at hcircle ⊢
  nlinarith

/-- Negative-light energy is one orientation sheet over the scalar chord coordinate. -/
theorem centered_negativeLight_sq_eq_chord_mul_complement
    (xi : ℝ) (p : Nat.Primes) (e : ℕ) :
    let n := xiGammaEulerValuationNat (p, e)
    (2 * normSq
        (suzukiCriticalWallNegativeLightAmplitude (2 * Real.pi * xi) p e) -
      criticalMellinAtomWeight n) ^ (2 : ℕ) =
      normSq (ccmActualHeadMellinWallChord xi n) *
        (criticalMellinAtomWeight n -
          normSq (ccmActualHeadMellinWallChord xi n) / 4) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hnegative :=
    normSq_suzukiCriticalWallNegativeLightAmplitude_eq_centerReserve_sub_imbalance
      p e xi
  have hmagnitude :=
    ccmActualHeadWallLightImbalance_sq_eq_chord_mul_complement xi p e
  dsimp only at hnegative hmagnitude ⊢
  rw [hnegative, ← hmagnitude]
  ring

end RHTower
