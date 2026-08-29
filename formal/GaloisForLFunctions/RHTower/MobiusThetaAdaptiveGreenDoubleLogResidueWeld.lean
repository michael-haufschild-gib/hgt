import GaloisForLFunctions.RHTower.MobiusThetaAdaptivePrimeNormalGreenResolvedLineComparison
import GaloisForLFunctions.RHTower.HedenmalmThetaMobiusPrimeNormalHalfDensityDoubleLogBoundaryResidue
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceEntropyBoundaryWeld

/-!
# Möbius--theta adaptive Green / double-log residue weld

The adaptive prime-normal resolved Green comparison and the physical Möbius prime half-density
were previously two independent RH receivers.  This module identifies their local zero and
nonzero strata exactly.  At every retained prime and Xi copy, the actual resolved Green
codiagonal vanishes precisely when physical half-density energy has zero double-logarithmic
residue; it is nonzero precisely when that residue is one.

Consequently fixed-prime global codiagonal annihilation is the same proposition as universal
zero residue and hence RH.  The remaining producer is source-side: derive codiagonal annihilation
from the arithmetic source differential.  No comparison between that codiagonal and the
prime-natural residue remains.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource
open DeningerMeyerGaussianGreen

private theorem thetaBoundaryFlux_eq_zero_iff_re_eq_half (q : XiZeroCopy) :
    thetaXiRankTwoBoundaryFlux q = 0 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [thetaXiRankTwoBoundaryFlux_eq_zero_iff_spectralIm_eq_zero,
    ← primeDepthBVWoldXiCenteredRate_eq_zero_iff,
    primeDepthBVWoldXiCenteredRate_eq_neg_two_spectralIm]
  constructor <;> intro h
  · rw [h]
    ring
  · linarith

/-- Local zero weld: resolved Green codiagonal vanishing is exactly zero physical double-log
residue. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_doubleLogResidue_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 ↔
      Tendsto (fun N : ℕ =>
        thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
          Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
  rw [adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff,
    tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_boundaryFlux_zero,
    thetaBoundaryFlux_eq_zero_iff_re_eq_half]

/-- Local nonzero weld: resolved Green codiagonal survival is exactly unit physical double-log
residue. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_ne_zero_iff_doubleLogResidue_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) ≠ 0 ↔
      Tendsto (fun N : ℕ =>
        thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
          Real.log (Real.log (N : ℝ))) atTop (𝓝 1) := by
  rw [tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_one_iff_boundaryFlux_ne_zero]
  exact not_congr
    ((adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff p q).trans
      (thetaBoundaryFlux_eq_zero_iff_re_eq_half q).symm)

/-- Fixed-prime global codiagonal annihilation is exactly universal zero double-log residue. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_all_doubleLogResidue_zero
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0) ↔
      ∀ q : XiZeroCopy,
        Tendsto (fun N : ℕ =>
          thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
            Real.log (Real.log (N : ℝ))) atTop (𝓝 0) := by
  exact forall_congr'
    (adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_doubleLogResidue_zero p)

/-- Fixed-prime annihilation of the actual adaptive Green codiagonal is exactly RH, now through
the physical double-log residue rather than a parallel critical-line receiver. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0) ↔
      RiemannHypothesis := by
  rw [adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_all_doubleLogResidue_zero,
    all_tendsto_thetaMobiusPrimeNormalHalfDensityEnergyPrefix_div_logLog_zero_iff_riemannHypothesis]

end

end RHTower
