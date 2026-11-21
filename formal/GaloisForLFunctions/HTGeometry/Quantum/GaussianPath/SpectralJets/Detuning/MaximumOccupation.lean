import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.WindowOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumScale
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SynthesisBudget

/-! # Finite-window occupation relative to the actual orbit maximum -/
open Matrix Set MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- From any origin, including zero, time below either power threshold of
the actual error-1/10 maximum is at most (T+2^(D^c))/2^⌊D/1024⌋. -/
theorem gaussian_path_finite_window_maximum_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Matrix (Fin N → Bool) (Fin N → Bool) ℂ) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∃ m : ℕ, nearHilbertContinuousCircuitBudget N < m ∧ m ≤ 160*(2*N+1)*16^N ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
        ∀ s : ℕ, (s^5 < m ∨ 160*(2*N+1)*(128*(N+1)*s)^4 < m) →
          ∀ a T : ℝ, 0 ≤ T →
          (2:ℝ)^(2^N/1024) * volume.real ({t | HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+(2:ℝ)^((2^N:ℕ)^c) := by
  obtain ⟨c,hocc⟩ := gaussian_path_finite_window_occupation
  refine ⟨c,?_⟩
  filter_upwards [hocc,gaussian_pauli_physical_maximum_and_power_occupation] with ω hω hmax
  filter_upwards [hω,hmax,eventually_ge_atTop 256] with k hw hm hk
  intro N u H
  obtain ⟨m,hmin,hcap,hm,_⟩ := hm
  refine ⟨m,hmin,hcap,hm,?_⟩
  intro s hs a T hT
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  have hr : s ≤ r := budget_le_excursion_of_below_maximum (by dsimp [N]; omega) hcap hs
  have hW : 0 ≤ W := by dsimp [W,translatedExcursionWidth]; positivity
  have hsub : {t | HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t)} ⊆
      circuitWindowHits H.val r W := by
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,z,hz,C,hC.trans hr,he⟩
  have hv := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc a (a+T)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hpow : (2:ℝ)^(2^N/1024) ≤ ((r:ℝ)+1)^r := by
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  exact (mul_le_mul hpow hv ENNReal.toReal_nonneg (by positivity)).trans (hw a T hT)

#print axioms gaussian_path_finite_window_maximum_occupation
end
end GaloisForLFunctions.HTGeometry.SpectralJets
