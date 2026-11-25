import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CandidateFace

/-! # One spectator-phase test at a fixed offset from a late antipode -/

open Set Filter MeasureTheory Topology Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
open PrescribedTimes.PhaseLaws
noncomputable section

/-- The relative phases of all spectator levels q turns after the nth
antipode. Time is measured in periods of the chosen gap. -/
def spectators (k : ℕ) (i j : Level k) (n : ℕ) (q : ℝ) (x : Coupling k) :=
  finiteClockPhasePoint (gapFrequency k i j x) (2*π*((n:ℝ)+(1/2+q)))

/-- Any upper bound strictly above the short-arc Haar mass eventually
bounds this one observation. The offset can be any prescribed real. -/
theorem late_spread_bound (k : ℕ) (i j : Level k) (hij : i≠j) (q : ℝ)
    (r : Icc (0:ℝ) (1/2)) {b : ℝ≥0∞}
    (hb : (Fintype.card (Outside i j):ℝ≥0∞)*ENNReal.ofReal (r:ℝ)^(Fintype.card (Outside i j)-1)<b) :
    ∀ᶠ n : ℕ in atTop, (centredProductGaussian (Fin (Fintype.card (ChainLabel (k+3)))) 1)
      {x | spectators k i j n q x∈enclosingUnitArc r}<b := by
  let μ : ProbabilityMeasure (Coupling k) := ⟨centredProductGaussian _ 1,inferInstance⟩
  let S := enclosingUnitArc (ι:=Outside i j) (r:ℝ)
  let T (n : ℕ) := 2*π*((n:ℝ)+(1/2+q))
  have h : Tendsto (fun n => gapSnapshot k i j μ (T n)) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
    simpa only [sub_neg_eq_add,T] using gaussian_high_winding_snapshot k i j hij (-(1/2+q))
  have hc : IsClosed S := isClosed_enclosingUnitArc _
  have hp := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hc
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,show volume S=_ from volume_enclosingUnitArc r] at hp
  filter_upwards [eventually_lt_of_limsup_lt (hp.trans_lt hb)] with n hn
  change (gapSnapshot k i j μ (T n) : Measure _) S<b at hn
  rwa [gapSnapshot,frequencySnapshot,ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (measurable_gap_point k i j (T n)) hc.measurableSet] at hn

#print axioms late_spread_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons
