import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ForecastWindows.Intervals
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.FrozenWidth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability

/-! # Uniform forecast exclusion for the first wait after the near-Hilbert crossing -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
open LocalPatches LocalPatches.PhysicalSpeed ShortWindows
noncomputable section

/-- A deterministic lower scale for simultaneous first waits on one frozen chain. -/
def forecastWidth (N : ℕ) : ℝ :=
  (N:ℝ)*localCrossingWidth N/(2*sqrt (log ((N:ℝ)+1)))

theorem forecastWidth_pos (k : ℕ) : 0 < forecastWidth (k+3) := by
  have hn : 0 < ((k+3:ℕ):ℝ) := by positivity
  have hl : 0 < log (((k+3:ℕ):ℝ)+1) := log_pos (by linarith only [hn])
  unfold forecastWidth localCrossingWidth
  positivity

/-- The random coefficient cap costs at most a square root of a logarithm
on every sufficiently long prefix of almost every infinite draw. -/
theorem typical_first_wait_lower :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      forecastWidth (k+3) < crossingWait (k+1) P (P/2) (prefixPoint k ω) := by
  obtain ⟨C,hC,h⟩ := gaussian_joint_frozen_travel_width
  obtain ⟨j,hj⟩ := exists_nat_gt (max C (1/C))
  filter_upwards [h] with ω hw
  filter_upwards [hw,eventually_ge_atTop j] with k hk hkj
  let N := k+3
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hjN : (j:ℝ) ≤ N := by exact_mod_cast (show j ≤ N by dsimp [N]; omega)
  have hCN : C ≤ (N:ℝ) := (le_max_left ..).trans (hj.le.trans hjN)
  have hone : 1 < C*(N:ℝ) := by
    rw [mul_comm]
    exact (div_lt_iff₀ hC).mp (((le_max_right ..).trans_lt hj).trans_le hjN)
  have hlog := log_pos hone
  have hNlog : 0 < log ((N:ℝ)+1) := log_pos (by linarith only [hN])
  have hcs : C*(N:ℝ) ≤ ((N:ℝ)+1)^2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hCN hN.le,hN.le]
  have hl := log_le_log (mul_pos hC hN) hcs
  rw [log_pow,Nat.cast_ofNat] at hl
  have hden : sqrt (log (C*(N:ℝ))) ≤ 2*sqrt (log ((N:ℝ)+1)) := by
    apply sqrt_le_iff.mpr ⟨by positivity,?_⟩
    nlinarith only [hl,hNlog.le,sq_sqrt hNlog.le]
  have hnum : 0 ≤ (N:ℝ)*localCrossingWidth N := by dsimp only [localCrossingWidth]; positivity
  exact (div_le_div_of_nonneg_left hnum (sqrt_pos.mpr hlog) hden).trans_lt (hk.2 _ le_rfl)

private theorem early_probability :
    let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
    let μ (k : ℕ) := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
    Tendsto (fun k : ℕ => (μ k).real
      {x | crossingWait (k+1) (P k) (P k/2) x ≤ forecastWidth (k+3)}) atTop (𝓝 0) := by
  intro P μ
  let B (k : ℕ) := forecastWidth (k+3)
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
        1024*sqrt m*(∑ i, w i) ≤ η*forecastWidth N/2 →
        μ.real {x | ∃ i, crossingWait (k+1) P (s i) x ∈ Ioc (t i) (t i+w i)} < η := by
  filter_upwards [early_probability.eventually_lt_const (half_pos hη)] with k hk
  intro N P μ m K s t w hs hw hwidth
  have hB : 0 < forecastWidth N := forecastWidth_pos k
  have hh := first_wait_forecast_union (k+1) P (P/2) s t w hs hw hB
  have hprice : 1024*sqrt m*(∑ i, w i)/forecastWidth N ≤ η/2 := (div_le_iff₀ hB).mpr (by linarith only [hwidth])
  exact hh.trans_lt (by linarith only [hk,hprice])

#print axioms gaussian_first_wait_excludes_forecasts
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ForecastWindows
