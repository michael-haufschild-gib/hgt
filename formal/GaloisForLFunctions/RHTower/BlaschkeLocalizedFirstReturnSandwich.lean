import GaloisForLFunctions.RHTower.BlaschkeLocalizedEarlyReturnClock
import GaloisForLFunctions.RHTower.BlaschkeLocalizedReturnDefectLimit

/-!
# Almost-sure actual first-return sandwich for the infinite Blaschke packet

The probabilistic early-hit obstruction and deterministic square-root
shifted constructive return are combined at the same target accuracy.
Thus almost every countable Haar phase packet has an actual finite first
return trapped between explicit lower and upper spectral-depth clocks.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace RHTower

/--
Exact two-sided actual-first-return clock at logarithmic target scales.
The lower deadline is a fixed fractional subentropy clock. The upper
deadline pays exact depth entropy at only a square-root shifted water level
plus its explicit linear active-coordinate cost.
-/
theorem ae_eventually_blaschkeFirstCoherenceTime_spectralDepthSandwich
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {K : ℝ}
    (hKtail : blaschkeSpectralOffset a ≤ K)
    (hKzero : blaschkeSpectralSlope a ≤ K)
    (hKnonneg : 0 ≤ K)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ℕ =>
          (volume : Measure UnitAddCircle)),
      ∀ᶠ k in atTop,
        (blaschkeHaarSubentropyDeadline a K delta k :
            WithTop ℕ) <
          countableTorusWeightedFirstCoherenceTime
            (blaschkeLocalizedWeight a) x
            (Real.exp (-blaschkeShiftedScale K k)) ∧
        ∃ T : ℕ,
          countableTorusWeightedFirstCoherenceTime
              (blaschkeLocalizedWeight a) x
              (Real.exp (-blaschkeShiftedScale K k)) ≤ T ∧
          Real.log (T : ℝ) ≤
            blaschkeDepthWaterEntropy a
                (blaschkeSqrtShiftedScale K k) +
              (blaschkeActiveTailRadius a
                  (blaschkeSqrtShiftedScale K k) + 1 : ℕ) *
                Real.log projectivePhaseResolutionConstant := by
  have hlower :=
    ae_eventually_blaschkeHaarSubentropyDeadline_lt_firstCoherenceTime
      a ha0 ha1 hKtail hKzero hKnonneg hdelta
  have hupper :=
    eventually_exists_blaschkeFirstCoherenceTimeDeadline_sqrtShift
      a ha0 ha1 hKtail hKzero hKnonneg
  filter_upwards [hlower] with x hx
  filter_upwards [hx, hupper] with k hk hT
  obtain ⟨T, hTx, hlog⟩ := hT
  exact ⟨hk, T, hTx x, hlog⟩

end RHTower
