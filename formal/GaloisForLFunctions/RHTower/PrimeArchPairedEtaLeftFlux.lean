import GaloisForLFunctions.RHTower.PrimeArchD2QObliqueFlux
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaEnergy

/-!
# Literal paired-eta source for the left-strip Route-Q flux

The paired-eta factorization is valid on the entire positive half-plane, but the existing
logarithmic-derivative bridge was stated only to the right of the critical line.  Route Q probes
the opposite half-strip.  Here the same arithmetic series is joined to its actual completed
prime--Gamma flux there, and the two-component oblique sign is cleared of its eta denominator.

No sign estimate is asserted: the signed eta numerator must still cancel the elementary
factor and archimedean correction at moving height.
-/

open Complex Filter Topology
open scoped Topology
open GaloisForLFunctions RiemannGaussian

namespace RHTower

noncomputable section

/-- The eta logarithmic derivative splits into the elementary factor and zeta throughout the
positive strip, not only on its right half. -/
theorem logDeriv_pairedEtaCore_eq_factor_add_zeta_of_re_pos_lt_one
    {s : ℂ} (hpos : 0 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv pairedEtaCore s =
      pairedEtaFactorLogDerivative s + logDeriv riemannZeta s := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hupper
  have hfactor : pairedEtaFactor s ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hupper
  have hevent : pairedEtaCore =ᶠ[𝓝 s]
      fun w : ℂ => pairedEtaFactor w * riemannZeta w := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos,
      isOpen_compl_singleton.mem_nhds
        (show s ∈ ({1}ᶜ : Set ℂ) by simpa)] with w hwre hwone
    simpa [pairedEtaFactor] using
      pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
        hwre (by simpa using hwone)
  rw [(GaloisForLFunctions.HTGeometry.logDeriv_congr_nhds hevent).eq_of_nhds]
  rw [logDeriv_mul s hfactor hzeta
    (hasDerivAt_pairedEtaFactor s).differentiableAt
    (differentiableAt_riemannZeta hsone)]
  rw [logDeriv_pairedEtaFactor]

/-- The genuine completed prime--Gamma flux is the negative paired-eta logarithmic quotient
plus the elementary-factor correction and the entire archimedean correction. -/
theorem completedPrimeGammaFlux_eq_pairedEta_of_re_pos_lt_one
    {s : ℂ} (hpos : 0 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    completedPrimeGammaFlux s =
      -(pairedEtaArithmeticDerivativeValue s / pairedEtaCore s) +
        pairedEtaFactorLogDerivative s - logDeriv archFactor s := by
  have h := logDeriv_pairedEtaCore_eq_factor_add_zeta_of_re_pos_lt_one
    hpos hupper hzeta
  rw [logDeriv_pairedEtaCore_eq_tsum hpos] at h
  change pairedEtaArithmeticDerivativeValue s / pairedEtaCore s =
      pairedEtaFactorLogDerivative s + logDeriv riemannZeta s at h
  unfold completedPrimeGammaFlux infinitePrimeFlux
  rw [h]
  ring

/-- The eta denominator is strictly positive on the actual pole-free left-strip source. -/
theorem pairedEtaCoreNormSq_pos_of_re_pos_lt_one_of_zeta_ne_zero
    {s : ℂ} (hpos : 0 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    0 < pairedEtaCoreNormSq s := by
  unfold pairedEtaCoreNormSq
  apply Complex.normSq_pos.mpr
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hpos (by
    intro h
    subst s
    norm_num at hupper)]
  exact mul_ne_zero (pairedEtaFactor_ne_zero_of_re_lt_one hupper) hzeta

/-- Denominator-cleared, two-component Route-Q source law in the literal paired-eta variables.
The numerator remains signed; this is the exact cancellation target, not a positivity claim. -/
theorem completedPrimeGammaFlux_oblique_pairedEta_numerator
    {s : ℂ} (hpos : 0 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) (t u : ℝ) :
    pairedEtaCoreNormSq s *
        (t * (completedPrimeGammaFlux s).re +
          u * (completedPrimeGammaFlux s).im) =
      -(t * pairedEtaLogDerivativeRealNumerator s +
          u * pairedEtaLogDerivativeImaginaryNumerator s) +
        pairedEtaCoreNormSq s *
          (t * (pairedEtaFactorLogDerivative s - logDeriv archFactor s).re +
            u * (pairedEtaFactorLogDerivative s - logDeriv archFactor s).im) := by
  rw [completedPrimeGammaFlux_eq_pairedEta_of_re_pos_lt_one hpos hupper hzeta]
  have hE := (pairedEtaCoreNormSq_pos_of_re_pos_lt_one_of_zeta_ne_zero
    hpos hupper hzeta).ne'
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.neg_re, Complex.neg_im]
  rw [pairedEtaArithmeticQuotient_re, pairedEtaArithmeticQuotient_im]
  field_simp [hE]
  ring

/-- Since the literal eta denominator is positive off the zeta divisor, the oblique sign is
equivalent to one explicit signed arithmetic-versus-completion inequality. -/
theorem completedPrimeGammaFlux_oblique_nonneg_iff_pairedEta_numerator
    {s : ℂ} (hpos : 0 < s.re) (hupper : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) (t u : ℝ) :
    0 ≤ t * (completedPrimeGammaFlux s).re +
          u * (completedPrimeGammaFlux s).im ↔
      0 ≤ -(t * pairedEtaLogDerivativeRealNumerator s +
          u * pairedEtaLogDerivativeImaginaryNumerator s) +
        pairedEtaCoreNormSq s *
          (t * (pairedEtaFactorLogDerivative s - logDeriv archFactor s).re +
            u * (pairedEtaFactorLogDerivative s - logDeriv archFactor s).im) := by
  rw [← completedPrimeGammaFlux_oblique_pairedEta_numerator
    hpos hupper hzeta t u]
  exact (mul_nonneg_iff_of_pos_left
    (pairedEtaCoreNormSq_pos_of_re_pos_lt_one_of_zeta_ne_zero
      hpos hupper hzeta)).symm

/-- The actual Route-Q sector condition, on its pole-free positive-frequency quadrant, is
exactly the signed paired-eta bilinear inequality.  This theorem does not supply that sign. -/
theorem continuedPrimeArchReciprocalSquare_sector_iff_pairedEta_numerator
    {z : ℂ} (hzre : 0 < z.re) (hzim : 0 < z.im)
    (hzimhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 ≤ z.re * (continuedPrimeArchReciprocalSquareTrace z).im ↔
      0 ≤ -(z.re * pairedEtaLogDerivativeRealNumerator (1 / 2 + z * I) +
          z.im * pairedEtaLogDerivativeImaginaryNumerator (1 / 2 + z * I)) +
        pairedEtaCoreNormSq (1 / 2 + z * I) *
          (z.re * (pairedEtaFactorLogDerivative (1 / 2 + z * I) -
              logDeriv archFactor (1 / 2 + z * I)).re +
            z.im * (pairedEtaFactorLogDerivative (1 / 2 + z * I) -
              logDeriv archFactor (1 / 2 + z * I)).im) := by
  have hsre : (1 / 2 + z * I).re = 1 / 2 - z.im := by
    simp [Complex.mul_re]
    ring
  have hspos : 0 < (1 / 2 + z * I).re := by rw [hsre]; linarith
  have hsupper : (1 / 2 + z * I).re < 1 := by rw [hsre]; linarith
  rw [d2q_sector_nonneg_iff_oblique_completedFlux hzre]
  exact completedPrimeGammaFlux_oblique_nonneg_iff_pairedEta_numerator
    hspos hsupper hzeta z.re z.im

end
end RHTower
