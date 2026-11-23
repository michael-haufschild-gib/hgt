import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Intervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Uniform forecast exclusion for the first wait after the near-Hilbert crossing -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
open IncrementClocks ShortWindows
noncomputable section

/-- On the original infinite draw the half-budget first wait eventually
exceeds the simulation travel width. Smaller budgets wait at least as long. -/
theorem typical_first_wait_lower :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      crossingWidth (k+3) < crossingWait (k+1) P (P/2) (prefixPoint k ω) := by
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  let B (k : ℕ) := crossingWidth (k+3)
  obtain ⟨_,hh⟩ := gaussian_path_first_crossing_near_dimension_wait
  filter_upwards [hh] with ω hw
  filter_upwards [hw] with k hk
  let u := pathPauliDisorderShell ω (k+1)
  let x := prefixPoint k ω
  let H : selfAdjoint (Register (k+3)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  have hgen : numberedGenerator (k+1) x=H.val := numberedGenerator_shell u
  have hd (j) (t) : pathGateDistance (k+1) j x t=orbitCircuitDistance H j t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [hgen]
  obtain ⟨σ,hσ,_,hc,hp,hwin,_⟩ := hk
  have hB : 0 < B k := by dsimp only [B,crossingWidth]; positivity
  have hor := crossingOrigin_eq_of_first (hB.trans hσ).le ((hd _ σ).trans hc)
    (fun t ht => (hd _ t).trans_lt (hp t ht))
  by_contra! hx
  obtain ⟨v,hv,he⟩ := (crossingWait_le_iff (k+1) (P k) (P k/2) x (B k)).mp hx
  rw [hor] at hv
  have hsep := hwin v ⟨(sub_le_self σ hB.le).trans hv.1,hv.2⟩
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val v) (P k/2) (1/10:ℝ)).mpr
    ((hd _ v).symm.trans_le he)
  obtain ⟨z,hz,C,hC,herr⟩ := hfit
  exact herr.not_lt (hsep z hz C hC)

private theorem early_probability :
    let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
    let μ (k : ℕ) := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    Tendsto (fun k : ℕ => (μ k).real
      {x | crossingWait (k+1) (P k) (P k/2) x ≤ crossingWidth (k+3)}) atTop (𝓝 0) := by
  intro P μ
  let B (k : ℕ) := crossingWidth (k+3)
  let E (k : ℕ) := {x | crossingWait (k+1) (P k) (P k/2) x ≤ B k}
  have hm (k) : MeasurableSet (E k) := measurableSet_le (measurable_crossingWait ..) measurable_const
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hmiss : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω∉prefixPoint k ⁻¹' E k := by
    filter_upwards [typical_first_wait_lower] with ω hw
    exact hw.mono fun _ hk => hk.not_ge
  have hlim := probability_vanishes pathPauliDisorderLaw (fun k => prefixPoint k ⁻¹' E k)
    (fun k => (hm k).preimage (gaussian_pauli_prefix_coordinates_law (k+1)).measurable) hmiss
  exact hlim.congr fun k => congrArg ENNReal.toReal
    ((gaussian_pauli_prefix_coordinates_law (k+1)).measure_preimage (hm k).nullMeasurableSet)

/-- For every error probability, all sufficiently long Gaussian prefixes
exclude any finite list of forecasts of sufficiently small total duration,
uniformly over their dates and over all return budgets up to half the
near-Hilbert threshold. The reference scale is the physical travel width
divided by the square root of the number of independent coefficients. -/
theorem gaussian_first_wait_excludes_forecasts {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
      let m := Fintype.card (ChainLabel N)
      ∀ (K : ℕ) (s : Fin K→ℕ) (t w : Fin K→ℝ), (∀ i, s i ≤ P/2) → (∀ i, 0 ≤ w i) →
        1024*sqrt m*(∑ i, w i) ≤ η*crossingWidth N/2 →
        μ.real {x | ∃ i, crossingWait (k+1) P (s i) x ∈ Ioc (t i) (t i+w i)} < η := by
  filter_upwards [early_probability.eventually_lt_const (half_pos hη)] with k hk
  intro N P μ m K s t w hs hw hwidth
  have hB : 0 < crossingWidth N := by unfold crossingWidth; positivity
  have hh := first_wait_forecast_union (k+1) P (P/2) s t w hs hw hB
  have hprice : 1024*sqrt m*(∑ i, w i)/crossingWidth N ≤ η/2 := (div_le_iff₀ hB).mpr (by linarith only [hwidth])
  exact hh.trans_lt (by linarith only [hk,hprice])

#print axioms gaussian_first_wait_excludes_forecasts
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
