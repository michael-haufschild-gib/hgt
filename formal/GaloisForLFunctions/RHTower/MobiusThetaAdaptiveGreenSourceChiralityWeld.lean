import GaloisForLFunctions.RHTower.MobiusThetaAdaptiveGreenDoubleLogResidueWeld
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherChiralitySelection

/-!
# Adaptive Green source-chirality weld

The adaptive prime-normal Green codiagonal, physical double-log residue, and the two
source-horizontal selection quantities are one obstruction, rather than four parallel RH
receivers.  At each prime and multiplicity-resolved Xi copy, codiagonal annihilation is
equivalent to zero double-log residue, zero directed adaptive KL chirality, and equality of
the frozen Hodge and adaptive Jeffreys source works.

This identifies the exact source-side task for HDL: derive either source equality before
divisor specialization.  No annihilation law is postulated here.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmThetaSource
open DeningerMeyerGaussianGreen

/-- The resolved adaptive Green codiagonal vanishes exactly when the literal directed
source-horizontal KL chirality vanishes. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_sourceHorizontalKL_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 ↔
      sourceHorizontalPrimeAdaptiveKLChirality p
        (primeDepthBVWoldXiCenteredRate q.1) = 0 := by
  exact
    (adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff p q).trans
      (sourceHorizontalXiAdaptiveKLChirality_eq_zero_iff q p).symm

/-- The same codiagonal vanishing is exactly equality of the two coefficient-faithful
source-horizontal work readings. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_sourceHorizontalWork_eq
    (p : Nat.Primes) (q : XiZeroCopy) :
    resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0 ↔
      sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiAdaptiveJeffreysWork q p := by
  exact
    (adaptivePrimeNormalActualGreenResolvedLineComparison_codiagonal_eq_zero_iff p q).trans
      (sourceHorizontalXiFrozenHodgeWork_eq_adaptiveJeffreysWork_iff q p).symm

/-- Zero prime-natural double-log residue is exactly zero directed adaptive source chirality. -/
theorem thetaMobiusPrimeNormalDoubleLogResidue_zero_iff_sourceHorizontalKL_zero
    (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto (fun N : ℕ =>
      thetaMobiusPrimeNormalHalfDensityEnergyPrefix q N /
        Real.log (Real.log (N : ℝ))) atTop (𝓝 0) ↔
      sourceHorizontalPrimeAdaptiveKLChirality p
        (primeDepthBVWoldXiCenteredRate q.1) = 0 := by
  exact
    (adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_doubleLogResidue_zero p q).symm.trans
      (adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_sourceHorizontalKL_zero p q)

/-- At one retained prime, codiagonal annihilation on the full multiplicity-exact Xi divisor
is equivalent to the source-horizontal KL annihilation law. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_sourceHorizontalKL_all_zero
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0) ↔
      ∀ q : XiZeroCopy,
        sourceHorizontalPrimeAdaptiveKLChirality p
          (primeDepthBVWoldXiCenteredRate q.1) = 0 := by
  exact forall_congr'
    (adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_sourceHorizontalKL_zero p)

/-- At one retained prime, codiagonal annihilation is equivalently equality of the frozen and
adaptive source work on every Xi copy. -/
theorem adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_sourceHorizontalWork_all_eq
    (p : Nat.Primes) :
    (∀ q : XiZeroCopy,
      resolvedDefectCodiagonal (R := ℂ)
        (adaptivePrimeNormalActualGreenResolvedLineComparison p q) = 0) ↔
      ∀ q : XiZeroCopy,
        sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiAdaptiveJeffreysWork q p := by
  exact forall_congr'
    (adaptivePrimeNormalActualGreenCodiagonal_eq_zero_iff_sourceHorizontalWork_eq p)

/-- The all-copy frozen/adaptive source-work equality is an exact source formulation of RH. -/
theorem riemannHypothesis_iff_sourceHorizontalWork_all_eq (p : Nat.Primes) :
    RiemannHypothesis ↔
      ∀ q : XiZeroCopy,
        sourceHorizontalXiFrozenHodgeWork q p = sourceHorizontalXiAdaptiveJeffreysWork q p := by
  exact
    (adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_riemannHypothesis p).symm.trans
      (adaptivePrimeNormalActualGreenCodiagonal_all_zero_iff_sourceHorizontalWork_all_eq p)

end

end RHTower
