import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMEThirdOrderSourceCohomology

/-!
# HB BM third-order cokernel necessity

The exact Einstein `++-` charge split separates the source into the AIME mass-memory channel,
a charge-orthogonal stationary cascade, a second-harmonic cascade, and the direct third variation.
HC11 proves that BM incidence on a critical Xi fibre forces the aggregate of the last three
channels to have resonant projection equal to the negative nonzero AIME numerator.

Consequently, for nonzero absorbed seed, at least one of those three non-AIME channels represents
a nonzero class modulo the range of the linearized Einstein--Teukolsky operator.  If all three were
gauge-exact, the left resonant state would annihilate the forced counterterm, contradicting its
exact nonzero value.

This upgrades the surviving HB burden from an unspecified nonzero remainder to a source-faithful
cohomological trichotomy.  Literal dynamics must produce a nonexact charge-orthogonal stationary,
second-harmonic, or direct-third-variation channel.

`[NEW] [SOURCE COHOMOLOGY] [EXACT TRICHOTOMY] [HB BURDEN REDUCTION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- On a critical Xi fibre, unit BM incidence fixes the aggregate non-AIME third-order
projection exactly: it is the negative AIME numerator. -/
theorem d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    ell (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) =
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  exact
    (d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_forcedCounterterm_of_criticalLine
      n amplitude
      (fun _ => ell
        (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
          d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
      q hline).mp hmatch

/-- For nonzero absorbed seed, the exact aggregate non-AIME projection forced by critical-line BM
incidence is nonzero. -/
theorem d4EinsteinThirdOrder_nonAIMEProjection_ne_zero_of_unitBMTarget_of_criticalLine
    (ell : V →ₗ[ℂ] ℂ)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    ell (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus) ≠ 0 := by
  rw [d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
    ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch]
  exact neg_ne_zero.mpr
    ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr hamplitude)

/-- Exact BM incidence at a critical Xi fibre forces a nontrivial cokernel class in at least one
non-AIME third-order Einstein channel. -/
theorem d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_forces_nonexact_channel
    (L : V →ₗ[ℂ] V) (ell : V →ₗ[ℂ] ℂ)
    (hleft : ∀ v, ell (L v) = 0)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] V)
    (C : V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V)
    (P : V →ₗ[ℂ] V) (hPlus hMinus hPlusPlus hPlusMinus : V)
    (n : ℕ) {amplitude : ℂ} (hamplitude : amplitude ≠ 0) (q : XiZeroCopy)
    (hline : (q.1 : ℂ).re = 1 / 2)
    (hAIME : ell (B hPlus (P hPlusMinus)) =
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q))
    (hmatch :
      d4FullCrossBranchProjectedResidue amplitude
          (fun _ => ell
            (B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
              d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus))
          (xiSpectralPoint q) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n 1 q) :
    (¬ ∃ gauge, B hPlus (hPlusMinus - P hPlusMinus) = L gauge) ∨
      (¬ ∃ gauge, B hMinus hPlusPlus = L gauge) ∨
      (¬ ∃ gauge,
        d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus = L gauge) := by
  let remainder : V :=
    B hPlus (hPlusMinus - P hPlusMinus) + B hMinus hPlusPlus +
      d4EinsteinDirectThirdVariationPlusPlusMinus C hPlus hMinus
  have hremainder : ell remainder =
      -d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
    exact d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine
      ell B C P hPlus hMinus hPlusPlus hPlusMinus n amplitude q hline hmatch
  have hAIMENe : ell (B hPlus (P hPlusMinus)) ≠ 0 := by
    rw [hAIME]
    exact (d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr
      hamplitude
  apply d4EinsteinThirdOrderPlusPlusMinusCancellation_forces_nonexact_channel
    L ell hleft B C P hPlus hMinus hPlusPlus hPlusMinus hAIMENe
  rw [d4EinsteinThirdOrderPlusPlusMinusSource_chargeSplit]
  rw [map_add, hAIME]
  change d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
      ell remainder = 0
  rw [hremainder]
  ring

end

end RHTower
