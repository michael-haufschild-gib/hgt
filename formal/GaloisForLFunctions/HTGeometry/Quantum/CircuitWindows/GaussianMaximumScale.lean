import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SynthesisBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.UniformGateCap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMeanReturns

/-! # Exponential scale of the actual fixed-error maximum and typical cost -/
open Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- At physical error 1/10 the actual maximum m has explicit exponential
upper and lower bounds. Outside a doubly exponentially small upper time
fraction, cost reaches m to the one-fifth power, and reaches its fourth
root divided by an explicit polynomial factor. -/
theorem gaussian_pauli_physical_maximum_and_power_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ m : ℕ, nearHilbertContinuousCircuitBudget N < m ∧ m ≤ 160*(2*N+1)*16^N ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
        ∃ S : ℝ, 0 ≤ S ∧ ∀ s : ℕ, (s^5 < m ∨ 160*(2*N+1)*(128*(N+1)*s)^4 < m) →
          ∀ a T : ℝ, 0 ≤ T →
          (2:ℝ)^(2^N/1024) * volume.real ({t | HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+S := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hwin⟩ := gaussian_pauli_chain_early_cost_excursions_and_returns
  filter_upwards [gaussian_pauli_prefix_maximum_and_occupation_quantiles,hwin] with ω hm hw
  filter_upwards [hm,hw,eventually_ge_atTop 256] with k hk hocc hlarge
  let N := k+3
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  obtain ⟨m,hlow,hmax,_⟩ := hk (1/10) (by constructor <;> norm_num)
  obtain ⟨_,w,_,hw,hh⟩ := hmax.2
  obtain ⟨u,_,hu⟩ := hh 0
  obtain ⟨z,hz,C,hC,he⟩ := evolution_uniform_projective_gate_cap (by dsimp [N]; omega : 2 ≤ N) H u
  have hupper := (hu u ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC
  have hex : PhysicalExcursionAndReturns H := hocc.2
  obtain ⟨⟨S,hS,hmeasure⟩,_⟩ := hex
  refine ⟨m,hlow,hupper,hmax,S,hS,?_⟩
  intro s hs a T hT
  have hr : s ≤ r := budget_le_excursion_of_below_maximum (by dsimp [N]; omega) hupper hs
  have hW : 0 ≤ W := by
    dsimp [W,translatedExcursionWidth]
    positivity
  have hsub : {t | HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t)} ⊆
      circuitWindowHits H.val r W := by
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,z,hz,C,hC.trans hr,he⟩
  have hf := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc a (a+T)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hpow : (2:ℝ)^(2^N/1024) ≤ ((r:ℝ)+1)^r := by
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  exact (mul_le_mul hpow hf ENNReal.toReal_nonneg (by positivity)).trans (hmeasure a T hT)

#print axioms gaussian_pauli_physical_maximum_and_power_occupation
end
end GaloisForLFunctions.HTGeometry
