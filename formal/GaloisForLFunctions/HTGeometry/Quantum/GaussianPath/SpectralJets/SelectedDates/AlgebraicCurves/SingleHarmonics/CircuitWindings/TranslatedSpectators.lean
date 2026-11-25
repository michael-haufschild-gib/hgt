import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.PhaseLaws.RandomTranslations
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.SpectatorLaw

/-! # Spectator phases measured against a circuit depending on the disorder -/

open Set Filter MeasureTheory Real Topology
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
open PrescribedTimes.PhaseLaws AntipodalHorizons
noncomputable section

/-- Draw-dependent offsets are allowed on every spectator line. At one
late winding their translated phases still have the joint Haar law. -/
theorem translated_spectators_haar (k : ℕ) (i j : Level k) (hij : i≠j)
    (μ : ProbabilityMeasure (Coupling k)) (hμ : (μ:Measure (Coupling k))≪volume)
    (u : Coupling k→UnitAddTorus (Outside i j)) (hu : Measurable u) (q : ℝ) :
    Tendsto (fun n : ℕ => translatedSnapshot μ (gapFrequency k i j) (gapFrequency_measurable ..)
      u hu (2*π*((n:ℝ)+(1/2+q)))) atTop (𝓝 (finiteTorusHaarProbabilityMeasure _)) := by
  have h := translatedSnapshot_haar μ (gapFrequency k i j) (gapFrequency_measurable ..) u hu (by
    intro m hm
    apply gap_projection_ac k i j hij _ hμ (fun l => (m l:ℝ))
    intro hz
    apply hm
    funext l
    have hl : (m l:ℝ)=0 := congrFun hz l
    change m l=0
    exact_mod_cast hl)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)+(1/2+q)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (a-(1/2+q))] with n hn
    linarith only [hn]
  exact (h.mono_left atTop_le_cocompact).comp (ht.const_mul_atTop two_pi_pos)

/-- A short arc for the translated phases costs the same limiting Haar
probability, even after conditioning the coupling law on a fixed event. -/
theorem translated_spread_bound (k : ℕ) (i j : Level k) (hij : i≠j)
    (μ : ProbabilityMeasure (Coupling k)) (hμ : (μ:Measure (Coupling k))≪volume)
    (u : Coupling k→UnitAddTorus (Outside i j)) (hu : Measurable u) (q : ℝ)
    (r : Icc (0:ℝ) (1/2)) {b : ℝ≥0∞}
    (hb : (Fintype.card (Outside i j):ℝ≥0∞)*ENNReal.ofReal (r:ℝ)^(Fintype.card (Outside i j)-1)<b) :
    ∀ᶠ n : ℕ in atTop, (μ:Measure (Coupling k))
      {x | u x+spectators k i j n q x∈enclosingUnitArc r}<b := by
  let S := enclosingUnitArc (ι:=Outside i j) (r:ℝ)
  have hc : IsClosed S := isClosed_enclosingUnitArc _
  have h := translated_spectators_haar k i j hij μ hμ u hu q
  have hp := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hc
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume,show volume S=_ from volume_enclosingUnitArc r] at hp
  filter_upwards [eventually_lt_of_limsup_lt (hp.trans_lt hb)] with n hn
  let t := 2*π*((n:ℝ)+(1/2+q))
  change (translatedSnapshot μ (gapFrequency k i j) _ u hu t : Measure _) S<b at hn
  have hm := hu.add (measurable_gap_point k i j t)
  rwa [translatedSnapshot,ProbabilityMeasure.toMeasure_map,Measure.map_apply hm hc.measurableSet] at hn

#print axioms translated_spread_bound
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.CircuitWindings
