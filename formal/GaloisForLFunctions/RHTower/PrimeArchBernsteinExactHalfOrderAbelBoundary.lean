import GaloisForLFunctions.RHTower.XiBernsteinPurityHalfOrderAbelBoundary
import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSusceptibility
import GaloisForLFunctions.HTGeometry.PositiveSquareRootBoundaryBlowup

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Under failure of RH, the source-attained maximal packet controls both the exact Abel radius
and the positive half-order boundary there. -/
theorem exists_exactRadius_positiveHalfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta L : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      L = ∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant u ∧
      0 < L ∧ 0 < Real.sqrt Real.pi * L ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ 2) ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) *
          primeArchEndpointBernsteinAbelSusceptibility t)
        (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2)))
        (nhds (Real.sqrt Real.pi * L)) ∧
      Tendsto primeArchEndpointBernsteinAbelSusceptibility
        (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2))) atTop := by
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hboundaryPos, hboundary⟩ :=
    exists_positive_halfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh hRH
  obtain ⟨B', hthreshold, hcritical⟩ :=
    exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh hRH
  obtain ⟨qD, hqD⟩ := hDne
  have hB_le : B ≤ B' := by
    calc
      B = xiEndpointBernsteinAtomAmplitudeBase qD := (hD qD hqD).symm
      _ ≤ B' := hthreshold.2.2.2.1 qD
  obtain ⟨q', hq'⟩ := hthreshold.2.2.1
  have hB'_le : B' ≤ B := by
    calc
      B' = xiEndpointBernsteinAtomAmplitudeBase q' := hq'.symm
      _ ≤ B := by
        by_cases hqmem : q' ∈ D
        · exact (hD q' hqmem).le
        · exact (hDsub q' hqmem).trans hbeta.le
  have hBB' : B = B' := le_antisymm hB_le hB'_le
  have hcriticalB : PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ 2) := by
    rw [hBB']
    exact hcritical
  have hblowup :=
    GaloisForLFunctions.HTGeometry.tendsto_atTop_of_positive_sqrt_scaled_boundary
      (lt_trans zero_lt_one hB) hboundaryPos hboundary
  exact ⟨D, B, beta, L, hB, hbeta1, hbeta, ⟨qD, hqD⟩, hD, hDsub,
    hL, hLpos, hboundaryPos, hcriticalB, hboundary, hblowup⟩

end

end RHTower

