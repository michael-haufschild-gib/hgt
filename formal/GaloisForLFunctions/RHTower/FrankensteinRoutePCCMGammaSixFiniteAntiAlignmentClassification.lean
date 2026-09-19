import GaloisForLFunctions.RHTower.FrankensteinRoutePCCMGammaSixMeyerTateSourceBridge

/-!
# Exact classification of finite P/CCM anti-alignment

The literal Meyer--Tate finite P/CCM source cell and the Xi-selected Green
cell align coefficient-faithfully in their common two-sheet carrier.  Hence
asking for their anti-alignment at a fixed finite cell is not an independent
source law: it is equivalent to the critical-line condition for that Xi copy.

This identifies the precise residual producer obligation.  It must be a
cofinal, history-sensitive relation, rather than a finite-cell cancellation
inside the already aligned carrier.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- On every literal finite P/CCM source cell, the proposed anti-alignment
is exactly the critical-line condition of the selected Xi copy. -/
theorem frankensteinPCCMMeyerTateXiGreenFiniteAntiAlignment_iff_criticalLine
    (pe : Nat.Primes × ℕ) (q : XiZeroCopy) (n : ℕ) :
    DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
        frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
          (frankensteinRoutePMeyerTateFiniteSourceCell pe n) +
      (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
        deningerGammaSixCofinalGraphPhysicalTransport
          (2 * (q.1 : ℂ).re - 1)
          (deningerGammaSixCofinalMeyerTateCompletedDifferential
            (deningerGammaSixCofinalXiGreenDegreeOneChain pe.1 q n)) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · exact frankensteinPCCMMeyerTateXiGreenAntiAlignment_forces_criticalLine pe q n
  · intro hline
    have hleft :
        DeningerMeyerGaussianGreen.reflectedGaussianHorizonGreenProvenance q •
            frankensteinTwoSheetPhysicalTransport (2 * (q.1 : ℂ).re - 1)
              (frankensteinRoutePMeyerTateFiniteSourceCell pe n) = 0 :=
      (frankensteinPCCMMeyerTateXiGreenPhysicalAlignment_left_eq_zero_iff pe q n).mpr hline
    have halign := frankensteinPCCMMeyerTateXiGreenPhysicalAlignment pe q n
    rw [hleft] at halign
    rw [hleft]
    simpa only [zero_add] using halign.symm

end

end RHTower
