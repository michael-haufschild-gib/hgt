import GaloisForLFunctions.RHTower.InverseTiltedPrimeGammaCentralSource
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaEnergy

/-!
# Paired eta reconstructs the completed central source

The convergent paired eta series and its convergent derivative series determine the zeta
logarithmic derivative throughout the strip `0 < Re(s) < 1` wherever paired eta is nonzero.
Adding the elementary rational and Gamma connections gives exactly the inverse-tilted
prime--Gamma trace at `s = 1/2 + iz`.
-/

open Complex Filter Function Set Topology
open GaloisForLFunctions

namespace RiemannGaussian

noncomputable section

/-- Nonvanishing of paired eta implies nonvanishing of zeta in the full positive strip. -/
theorem riemannZeta_ne_zero_of_pairedEtaCore_ne_zero
    {s : ℂ} (hlower : 0 < s.re) (hupper : s.re < 1)
    (heta : pairedEtaCore s ≠ 0) : riemannZeta s ≠ 0 := by
  have hsone : s ≠ 1 := by
    intro h
    subst s
    norm_num at hupper
  intro hzero
  apply heta
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hlower hsone,
    hzero, mul_zero]

/-- The eta logarithmic derivative splits into its elementary factor and zeta parts on the
full strip `0 < Re(s) < 1`, away from the zeta divisor. -/
theorem logDeriv_pairedEtaCore_eq_factor_add_riemannZeta_of_re_pos_of_re_lt_one
    {s : ℂ} (hlower : 0 < s.re) (hupper : s.re < 1)
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
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlower,
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

/-- The zeta logarithmic derivative is the quotient of the two convergent paired eta source
series, minus the elementary-factor connection.  Eta nonvanishing supplies zeta nonvanishing. -/
theorem logDeriv_riemannZeta_eq_pairedEtaArithmetic_of_re_pos_of_re_lt_one
    {s : ℂ} (hlower : 0 < s.re) (hupper : s.re < 1)
    (heta : pairedEtaCore s ≠ 0) :
    logDeriv riemannZeta s =
      pairedEtaArithmeticDerivativeValue s / pairedEtaCore s -
        pairedEtaFactorLogDerivative s := by
  have hzeta := riemannZeta_ne_zero_of_pairedEtaCore_ne_zero hlower hupper heta
  have h := logDeriv_pairedEtaCore_eq_factor_add_riemannZeta_of_re_pos_of_re_lt_one
    hlower hupper hzeta
  rw [logDeriv_pairedEtaCore_eq_tsum hlower] at h
  dsimp only [pairedEtaArithmeticDerivativeValue]
  linear_combination -h

end

end RiemannGaussian

namespace RHTower

noncomputable section

/-- The completed central source formed directly from the convergent paired eta quotient and
the explicit elementary, rational and Gamma connections. -/
def liEvenCrossActualClockPairedEtaSourceTrace (z : ℂ) : ℂ :=
  let s : ℂ := 1 / 2 + z * I
  I *
    (RiemannGaussian.pairedEtaArithmeticDerivativeValue s /
        RiemannGaussian.pairedEtaCore s -
      RiemannGaussian.pairedEtaFactorLogDerivative s +
      1 / s + 1 / (s - 1) + gammaRealLogConnection s)

/-- The literal paired eta source reconstructs the inverse-tilted prime--Gamma trace wherever
the central coordinate lies in the full positive strip and paired eta is nonzero. -/
theorem liEvenCrossActualClockPairedEtaSourceTrace_eq_inverseTiltedPrimeGammaSourceTrace
    {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1)
    (heta : RiemannGaussian.pairedEtaCore (1 / 2 + z * I) ≠ 0) :
    liEvenCrossActualClockPairedEtaSourceTrace z =
      inverseTiltedPrimeGammaSourceTrace z := by
  have hzeta := RiemannGaussian.riemannZeta_ne_zero_of_pairedEtaCore_ne_zero
    hlower hupper heta
  have hsone : 1 / 2 + z * I ≠ 1 := by
    intro h
    rw [h] at hupper
    norm_num at hupper
  have hszero : 1 / 2 + z * I ≠ 0 := by
    intro h
    rw [h] at hlower
    norm_num at hlower
  have hu : xiCriticalMellinCoordinate z = (1 / 2 + z * I) - 1 := by
    rw [xiCriticalMellinCoordinate]
    ring
  rw [inverseTiltedPrimeGammaSourceTrace_eq_continuedPrimeArchSourceRelativeTrace
      hlower hsone hzeta,
    continuedPrimeArchSourceRelativeTrace_eq_continuedMellinGamma hlower hszero hsone]
  rw [liEvenCrossActualClockPairedEtaSourceTrace, continuedMellinGammaSourceTrace,
    continuedCriticalMellinDefect, hu, sub_add_cancel,
    RiemannGaussian.logDeriv_riemannZeta_eq_pairedEtaArithmetic_of_re_pos_of_re_lt_one
      hlower hupper heta]
  ring

end

end RHTower
