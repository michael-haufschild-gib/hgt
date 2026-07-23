import GaloisForLFunctions.RHTower.PolarPrimeChannelContinuation
import GaloisForLFunctions.RHTower.XiAperturePoissonEulerLogDerivCompletion

/-!
# Polar-prime aperture--Poisson conservation universality law

Two independently developed source mechanisms encode the same prime logarithmic derivative.  The
critical Mellin-defect channel contains `ζ'/ζ(a)` together with two polar coordinates, whereas the
clocked valuation-fused aperture current is `-a ζ'/ζ(a)`.  At matching apertures their arithmetic
parts cancel exactly, leaving a universal rational boundary current.  After archimedean completion,
the residual identity compares the critical Mellin channel directly with the Xi logarithmic flux.
-/

namespace RHTower

noncomputable section

/-- **Polar-prime/aperture--Poisson conservation law.**  Multiplying the critical Mellin channel
by its aperture and adding the fully valuation-fused prime current cancels every prime term. -/
theorem criticalMellinDefect_add_clockedPrimeCurrent_eq_rationalBoundary
    {a : ℝ} (ha : 1 < a) :
    (a : ℂ) * criticalMellinDefectChannelComplex ((a - 1 : ℝ) : ℂ) +
        (∑' p : Nat.Primes, xiAperturePoissonClockedPrimeCurrent a p) =
      (a : ℂ) / (a - 1 : ℝ) + 1 := by
  rw [criticalMellinDefectChannelComplex,
    tsum_xiAperturePoissonClockedPrimeCurrent_eq_neg_zeta_deriv_div ha,
    vonMangoldtPrimeChannelComplex]
  have ha0 : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ha))
  have ha1 : ((a : ℂ) - 1) ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_gt ha))
  push_cast
  have harg : (a : ℂ) - 1 + 1 = (a : ℂ) := by ring
  rw [harg]
  field_simp [ha0, ha1]
  ring

/-- Archimedean completion changes the rational conservation remainder by exactly the fixed
archimedean logarithmic current. -/
theorem criticalMellinDefect_add_completedApertureCurrent_eq_archBoundary
    {a : ℝ} (ha : 1 < a) :
    (a : ℂ) * criticalMellinDefectChannelComplex ((a - 1 : ℝ) : ℂ) +
        xiAperturePoissonCompletedCurrent a =
      (a : ℂ) / (a - 1 : ℝ) + 1 -
        (a : ℂ) * logDeriv archFactor (a : ℂ) := by
  rw [xiAperturePoissonCompletedCurrent, ← add_sub_assoc,
    criticalMellinDefect_add_clockedPrimeCurrent_eq_rationalBoundary ha]

/-- **Completed Xi residual law.**  The difference between the shifted critical Mellin channel
and the Xi logarithmic derivative is prime-blind: only two rational boundary poles and the fixed
archimedean logarithmic derivative remain. -/
theorem criticalMellinDefect_sub_xiLogDeriv_eq_primeBlindArchBoundary
    {a : ℝ} (ha : 1 < a) :
    criticalMellinDefectChannelComplex ((a - 1 : ℝ) : ℂ) -
        logDeriv xi (a : ℂ) =
      1 / ((a - 1 : ℝ) : ℂ) + 1 / (a : ℂ) -
        logDeriv archFactor (a : ℂ) := by
  have h := criticalMellinDefect_add_completedApertureCurrent_eq_archBoundary ha
  rw [xiAperturePoissonCompletedCurrent_eq_neg_xi_logDeriv ha] at h
  have ha0 : (a : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans zero_lt_one ha))
  apply mul_left_cancel₀ ha0
  calc
    (a : ℂ) * (criticalMellinDefectChannelComplex ((a - 1 : ℝ) : ℂ) -
        logDeriv xi (a : ℂ)) =
      (a : ℂ) * criticalMellinDefectChannelComplex ((a - 1 : ℝ) : ℂ) +
        -(a : ℂ) * logDeriv xi (a : ℂ) := by ring
    _ = (a : ℂ) / (a - 1 : ℝ) + 1 -
        (a : ℂ) * logDeriv archFactor (a : ℂ) := h
    _ = (a : ℂ) * (1 / ((a - 1 : ℝ) : ℂ) + 1 / (a : ℂ) -
        logDeriv archFactor (a : ℂ)) := by field_simp

end

end RHTower
