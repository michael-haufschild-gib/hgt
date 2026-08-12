import GaloisForLFunctions.RHTower.CCMFirstClockLandauCompleteness
import GaloisForLFunctions.RHTower.SuzukiExplicitScrewZeroSeries
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Suzuki's one-sided Fourier transform

This module proves Theorem 1.1(i) of Suzuki, *Aspects of the screw function corresponding to the
Riemann zeta-function* (arXiv:2206.03682), for the paper's displayed prime--Lerch function.

The proof transports the complete multiplicity-exact Xi screw Laplace law through the exact
identity `suzukiPsi = xiScrewDivisor`.  The substitution `s = -i z`, the centered Xi coordinate,
and the functional equation of `xi` give Suzuki's sign and argument exactly.  No RH hypothesis is
used.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **Suzuki 2022, Theorem 1.1(i).**  One-sided Fourier transform of the literal displayed
function `Psi`, on the sharp source half-plane `Im z > 1/2`. -/
theorem integral_suzukiPsi_mul_cexp_eq_logDeriv_xi
    {z : ℂ} (hz : 1 / 2 < z.im) :
    (∫ t : ℝ in Ioi 0,
      (suzukiPsi t : ℂ) * Complex.exp (I * z * (t : ℂ))) =
        -(1 : ℂ) / z ^ 2 * logDeriv xi (1 / 2 - I * z) := by
  let s : ℂ := -I * z
  have hs : 1 / 2 < s.re := by
    dsimp only [s]
    simpa [Complex.mul_re] using hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hreflect :
      logDeriv xi (1 / 2 + z * I) =
        -logDeriv xi (1 / 2 - I * z) := by
    have h := logDeriv_xi_reciprocity (1 / 2 - I * z)
    have harg : 1 - (1 / 2 - I * z) = 1 / 2 + z * I := by ring
    rw [harg] at h
    exact h
  calc
    (∫ t : ℝ in Ioi 0,
      (suzukiPsi t : ℂ) * Complex.exp (I * z * (t : ℂ))) =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-s * (t : ℂ)) * xiScrewDivisor t := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            rw [ofReal_suzukiPsi_eq_xiScrewDivisor ht.le]
            have hexp : I * z * (t : ℂ) = -s * (t : ℂ) := by
              dsimp only [s]
              ring
            rw [hexp, mul_comm]
    _ = I / s ^ 2 * logDeriv XiC (I * s) :=
      integral_exp_mul_xiScrewDivisor_eq_logDeriv_XiC hs
    _ = -(1 : ℂ) / z ^ 2 * logDeriv xi (1 / 2 - I * z) := by
      rw [show I * s = z by dsimp only [s]; simp [← mul_assoc],
        logDeriv_XiC_eq_mul_I_logDeriv_xi, hreflect]
      dsimp only [s]
      field_simp

end

end RHTower
