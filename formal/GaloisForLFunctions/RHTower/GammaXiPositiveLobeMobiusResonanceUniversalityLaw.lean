import GaloisForLFunctions.RHTower.GammaXiResponseGapOneCutSpectrum
import GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockGammaBand

/-!
# Gamma--Xi positive-lobe visibility of the Möbius resonance band

The Gamma--Xi response gap is positive exactly below its unique nonzero spectral cut.  The critical
Möbius prime block has an exponential lower bound throughout its positive-width moving Gamma band.
Once that band lies below the cut, multiplying by the signed response gap preserves a strictly
positive explicit lower bound at every frequency in the band.
-/

open Real Set

noncomputable section

namespace RHTower

/-- **Positive-lobe Möbius resonance law.**  Whenever the upper endpoint of the critical moving
band lies below the unique Gamma--Xi spectral cut, its signed response-gap energy is strictly
positive throughout the band and retains the full exponential prime-block lower bound. -/
theorem gammaXiPositiveLobe_mobiusCriticalPrimeBlock_weightedLower
    {y t : ℝ} (hy : 27 ≤ y)
    (hcut : 4 * Real.pi / (3 * Real.log y) < gammaXiResponseSpectralCutoff)
    (htLower : Real.pi / Real.log y ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log y)) :
    0 < gammaXiResponseGapSpectralDensity t *
        (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ∧
      gammaXiResponseGapSpectralDensity t *
          (1 + 1 / Real.sqrt y) ^ (mobiusCriticalPrimeWindow y).card ≤
        gammaXiResponseGapSpectralDensity t *
          ‖mobiusCriticalPrimeBlock y t‖ ^ 2 := by
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have ht : 0 < t :=
    (div_pos Real.pi_pos hlogy).trans_le htLower
  have hgap : 0 < gammaXiResponseGapSpectralDensity t :=
    (gammaXiResponseGapSpectralDensity_pos_iff t).2 ⟨by simpa [abs_of_pos ht], by
      rw [abs_of_pos ht]
      exact htUpper.trans_lt hcut⟩
  have hblock :=
    mobiusCriticalPrimeBlock_norm_sq_lower_on_gammaBand hy htLower htUpper
  constructor
  · exact mul_pos hgap (by positivity)
  · exact mul_le_mul_of_nonneg_left hblock hgap.le

end RHTower
