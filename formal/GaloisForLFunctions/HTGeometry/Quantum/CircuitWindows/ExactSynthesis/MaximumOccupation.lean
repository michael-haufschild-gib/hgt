import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactSynthesis.QuadraticBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.MaximumOccupation

/-! # Time occupation below the square root of the same-error maximum -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section

/-- Almost surely on all sufficiently long Gaussian prefixes, the actual
maximum at error 1/10 obeys a quadratic Hilbert-dimension cap. Every
observation interval has exponentially small-in-dimension occupation below
the cube root of that maximum, and below its square root divided by the
explicit polynomial square-root loss. -/
theorem gaussian_path_quadratic_maximum_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      ∃ m : ℕ, nearHilbertContinuousCircuitBudget N < m ∧ m ≤ (4*N+1)*(2*N+2)*(2^N)^2 ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
        ∀ s : ℕ, (s^3 < m ∨ (4*N+1)*(2*N+2)*(128*(N+1)*s)^2 < m) →
          ∀ a T : ℝ, 0 ≤ T →
          (2:ℝ)^(2^N/1024) * volume.real ({t | HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+(2:ℝ)^((2^N:ℕ)^c) := by
  obtain ⟨c,hocc⟩ := SpectralJets.gaussian_path_finite_window_occupation
  refine ⟨c,?_⟩
  filter_upwards [hocc,gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hω hmax
  filter_upwards [hω,hmax,eventually_ge_atTop 256] with k hw hh hk
  intro N u H
  obtain ⟨m,hmin,hm,_⟩ := hh (1/10) (by constructor <;> norm_num)
  obtain ⟨_,w,_,hw',hvisit⟩ := hm.2
  obtain ⟨v,_,hv⟩ := hvisit 0
  obtain ⟨z,hz,C,hC,he⟩ := (exact_evolution_gate_cap (by dsimp [N]; omega : 2 ≤ N) H v).approx
    (by norm_num : (0:ℝ) ≤ 1/10)
  have hm' := (hv v ⟨le_rfl,le_add_of_nonneg_right hw'.le⟩ z hz C he).trans hC
  refine ⟨m,hmin,hm',hm,?_⟩
  intro s hs a T hT
  let r := excursionGateBudget N
  let W := translatedExcursionWidth N ‖H.val‖
  have hr : s ≤ r := budget_of_quadratic_cap (by dsimp [N]; omega) hm' hs
  have hW : 0 ≤ W := by dsimp [W,translatedExcursionWidth]; positivity
  have hsub : {t | HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t)} ⊆
      circuitWindowHits H.val r W := by
    rintro t ⟨z,hz,C,hC,he⟩
    exact ⟨t,⟨le_rfl,le_add_of_nonneg_right hW⟩,z,hz,C,hC.trans hr,he⟩
  have hvol := measureReal_mono (μ := volume) (inter_subset_inter_left (Icc a (a+T)) hsub)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  have hpow : (2:ℝ)^(2^N/1024) ≤ ((r:ℝ)+1)^r := by
    exact_mod_cast (circuit_return_spacing_factor_bounds (by dsimp [N]; omega : 64 ≤ N)).1
  exact (mul_le_mul hpow hvol ENNReal.toReal_nonneg (by positivity)).trans (hw a T hT)

#print axioms gaussian_path_quadratic_maximum_occupation
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
