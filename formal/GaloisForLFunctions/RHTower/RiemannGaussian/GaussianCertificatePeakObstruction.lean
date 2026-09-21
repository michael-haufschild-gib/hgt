import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianDigammaGauss

/-!
# Phase-flip cost of a finite Gaussian positivity certificate

The center-minimum condition in a `GaussianArithmeticWidthCertificate` has a
quantitative consequence which does not assume RH.  The retained model loses
the elementary Gaussian peak at a phase flip.  On every compact interval on
which the certificate claims that the center is a minimum, that loss must be
paid by the digamma gain and the *finite* retained prime block.

At the natural phase flip `π / ε`, the required payment is explicit:
`4 exp (ε / 4) + 4 exp (ε / 4 - π² / ε)`.  Thus a cofinal certificate
construction cannot hide the elementary peak in a tail estimate; it must give
a quantitative lower bound for one of the two displayed payment channels, or
put that phase flip under its separate large-center proof.
-/

open Filter Set

namespace RiemannGaussian

noncomputable section

/-- Exact increment of a retained arithmetic Gaussian model: the elementary
peak loss is paid only by the digamma gain and the retained prime oscillation. -/
theorem gaussianArithmeticRetainedFormula_sub_zero_eq_neg_primeEnergyMainTerm_add_digammaGain_add_partialOscillation
    (ε t : ℝ) (cutoff : ℕ) :
    gaussianArithmeticRetainedFormula ε cutoff t -
        gaussianArithmeticRetainedFormula ε cutoff 0 =
      -gaussianPrimeEnergyMainTerm ε t +
        gaussianDigammaGain ε t +
          gaussianPrimePartialOscillationEnergy ε t (Finset.range cutoff) := by
  unfold gaussianArithmeticRetainedFormula gaussianArchimedeanContribution
    gaussianPrimePartialContribution gaussianPrimePartialSum
    gaussianPrimeEnergyMainTerm gaussianElementaryBoundaryTerm
    gaussianDigammaGain gaussianPrimePartialOscillationEnergy
    gaussianPrimeOscillationSummand
  rw [Finset.sum_sub_distrib]
  ring

/-- A certificate whose retained model has its minimum at the center must pay
all elementary Gaussian peak loss by the digamma gain and its finite prime block. -/
theorem GaussianArithmeticWidthCertificate.primeEnergyMainTerm_le_digammaGain_add_partialOscillation
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    {t : ℝ} (ht : 0 ≤ t) (htRadius : t ≤ certificate.compactRadius) :
    gaussianPrimeEnergyMainTerm ε t ≤
      gaussianDigammaGain ε t +
        gaussianPrimePartialOscillationEnergy ε t
          (Finset.range certificate.cutoff) := by
  have hmono := certificate.compact_retained_ge_zero t ht htRadius
  have hnonneg : 0 ≤
      gaussianArithmeticRetainedFormula ε certificate.cutoff t -
        gaussianArithmeticRetainedFormula ε certificate.cutoff 0 :=
    sub_nonneg.mpr hmono
  rw [gaussianArithmeticRetainedFormula_sub_zero_eq_neg_primeEnergyMainTerm_add_digammaGain_add_partialOscillation] at hnonneg
  linarith

/-- The elementary peak loss at the natural phase-flip center `π / ε`. -/
theorem gaussianPrimeEnergyMainTerm_pi_div
    {ε : ℝ} (hε : 0 < ε) :
    gaussianPrimeEnergyMainTerm ε (Real.pi / ε) =
      4 * Real.exp (ε / 4) +
        4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) := by
  rw [gaussianPrimeEnergyMainTerm_eq]
  have hεne : ε ≠ 0 := hε.ne'
  have hphase : ε * (Real.pi / ε) = Real.pi := by
    field_simp [hεne]
  have hsq : ε * (Real.pi / ε) ^ 2 = Real.pi ^ 2 / ε := by
    field_simp [hεne]
  rw [hphase, hsq, Real.cos_pi]
  ring

/-- At the phase flip, every compact center-minimum certificate must supply an
explicit exponentially scaled peak payment from the digamma and retained-prime
channels. -/
theorem GaussianArithmeticWidthCertificate.phaseFlipPeak_le_digammaGain_add_partialOscillation
    {ε : ℝ} (certificate : GaussianArithmeticWidthCertificate ε)
    (hphaseRadius : Real.pi / ε ≤ certificate.compactRadius) :
    4 * Real.exp (ε / 4) +
        4 * Real.exp (ε / 4 - Real.pi ^ 2 / ε) ≤
      gaussianDigammaGain ε (Real.pi / ε) +
        gaussianPrimePartialOscillationEnergy ε (Real.pi / ε)
          (Finset.range certificate.cutoff) := by
  rw [← gaussianPrimeEnergyMainTerm_pi_div certificate.width_pos]
  apply certificate.primeEnergyMainTerm_le_digammaGain_add_partialOscillation
  · exact div_nonneg Real.pi_pos.le certificate.width_pos.le
  · exact hphaseRadius

end

end RiemannGaussian
