import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport
import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentFiniteBoundaryReadout

/-!
# SP-E boundary charge through the relative carrier

The literal SP-E completed quantile Riesz transport and the completed unit-Riesz relative carrier
are two source presentations of one scalar charge.  The former retains the finite labelled
prime--polar cells; the latter reconstructs the same charge from decaying shift codiagonals.

This file records their exact meeting point.  It does not assume, prove, or disguise a uniform
bound for the charge.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The normalized literal SP-E transport is exactly the boundary value reconstructed by the
decaying completed unit-Riesz shift codiagonal.  Thus any uniform SP-E estimate must control this
specific infinite signed accumulation; no finite endpoint or discarded tail can replace it. -/
theorem tendsto_unitRieszCoherentCompletedShiftCodiagonal_eq_speQuantileRieszTransport
    {M : ℕ} (hM : 2 ≤ M) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun m : ℕ =>
        ∑ j ∈ Finset.range m,
          GaloisForLFunctions.RHTower.unitRieszCoherentCompletedShiftCodiagonal M h
            (j * h))
      atTop
      (𝓝 (speCompletedQuantileRieszTransport M / (2 * (M : ℝ)))) := by
  have hcarrier :=
    GaloisForLFunctions.RHTower.tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal_zero
      hM hh
  have hMR : (M : ℝ) ≠ 0 := by positivity
  have hlimit :
      criticalMellinChebyshevResolventSource (Real.log M) / 2 =
        speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) := by
    rw [← speCompletedQuantileRieszTransport_div_eq_resolvent_source hM]
    field_simp [hMR]
  rw [← hlimit]
  exact hcarrier

/-- The normalized labelled SP-E transport has a uniformly conditioned finite readout through
three literal completed-codiagonal samples at shifts `0`, `log M`, and `2 log M`.  This removes
the infinite-tail bookkeeping, but leaves the required uniform control of those source samples as
the live arithmetic problem. -/
theorem abs_speQuantileRieszTransport_half_le_threeCodiagonalSamples
    {M : ℕ} (hM : 2 ≤ M) :
    let L := Real.log M
    |speCompletedQuantileRieszTransport M / (2 * (M : ℝ))| ≤
      |GaloisForLFunctions.RHTower.unitRieszCoherentCompletedShiftCodiagonal M L 0| +
        48 * |GaloisForLFunctions.RHTower.unitRieszCoherentCompletedShiftCodiagonal M L L| +
        16 * |GaloisForLFunctions.RHTower.unitRieszCoherentCompletedShiftCodiagonal M L (2 * L)| := by
  dsimp only
  have hMR : (M : ℝ) ≠ 0 := by positivity
  have hnormalize :
      speCompletedQuantileRieszTransport M / (2 * (M : ℝ)) =
        (speCompletedQuantileRieszTransport M / (M : ℝ)) / 2 := by
    field_simp [hMR]
  rw [hnormalize, speCompletedQuantileRieszTransport_div_eq_resolvent_source hM]
  exact GaloisForLFunctions.RHTower.abs_criticalMellinChebyshevResolventSource_half_le_threeCodiagonalSamples hM

end

end RHTower
