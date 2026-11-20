import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.RobustReflection
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.OrbitMaximumAtError
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw
import GaloisForLFunctions.HTGeometry.OnsetRecurrenceIndependence

/-! # Typical gate cost relative to the actual Gaussian orbit maximum -/
open Set MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- One time realizing the robust maximum m controls all the occupation
quantiles. Budgets s below m/(2q) occupy at most 1/(q+1) of long intervals
at errors at most η/(2q), uniformly in the interval origin. -/
theorem twoLocal_actual_maximum_and_occupation_quantiles {n : ℕ} (hn : 2 ≤ n)
    (H : selfAdjoint (Reg n)) (hloc : HasPauliWeightAtMost (Fin n) 2 H)
    (η : ℝ) (hη : 0 < η) :
    ∃ m : ℕ, IsRecurrentOrbitCircuitMaximumAt H η m ∧ ∃ u : ℝ, 0 ≤ u ∧
      ∀ q s : ℕ, 0 < q → 2*s*q < m → ∀ ε : ℝ, 0 ≤ ε → 2*(q:ℝ)*ε ≤ η → ∀ a T : ℝ, 0 ≤ T →
        ((q:ℝ)+1)*volume.real ({t | HasProjectiveCircuitApproximation n ε s
          (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+u := by
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at hn H hloc η hη
  obtain ⟨G,w,_,hw,hvisit⟩ := hm.2
  obtain ⟨u,hu,hfloor⟩ := hvisit 0
  refine ⟨m,hm,u,hu.1,?_⟩
  intro q s hq hs ε hε heps
  apply affordable_occupation_of_hard_lag H hq hε u hu.1
  intro z hz C hC
  by_contra! he
  have hc := hfloor u ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C (he.trans heps)
  omega

#print axioms twoLocal_actual_maximum_and_occupation_quantiles

/-- Along one Gaussian chain the actual maximum exceeds the exponential
budget simultaneously at all operator accuracies in (0,11/25].
The same draw satisfies the occupation bounds relative to each such maximum. -/
theorem gaussian_pauli_prefix_maximum_and_occupation_quantiles :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in Filter.atTop,
      let N := k+3
      let h := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian h,isSelfAdjoint_pathHamiltonian h⟩
      ∀ η ∈ Ioc (0:ℝ) (11/25), ∃ m > nearHilbertContinuousCircuitBudget N,
        IsRecurrentOrbitCircuitMaximumAt H η m ∧ ∃ u : ℝ, 0 ≤ u ∧
          ∀ q s : ℕ, 0 < q → 2*s*q < m → ∀ ε : ℝ, 0 ≤ ε → 2*(q:ℝ)*ε ≤ η → ∀ a T : ℝ, 0 ≤ T →
          ((q:ℝ)+1)*volume.real ({t | HasProjectiveCircuitApproximation N ε s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T)) ≤ T+u := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  have hN : Filter.Tendsto (fun k : ℕ => k+3) Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat 3
  filter_upwards [hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hent
  let N := k+3
  let d := 2^N-1
  let h := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian h,isSelfAdjoint_pathHamiltonian h⟩
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hp : 0 < (2:ℕ)^N := by positivity
                  dsimp [d]; omega))
  let P := nearHilbertContinuousCircuitBudget N
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  obtain ⟨x,hx⟩ := exists_coarsely_separated_spectral_reflection (s := P) e V hent
  intro _ _ _ η hη
  obtain ⟨m,hm,hocc⟩ := twoLocal_actual_maximum_and_occupation_quantiles (by dsimp [N]; omega : 2 ≤ N) H
    (hasPauliWeightAtMost_pathHamiltonian h (isSelfAdjoint_pathHamiltonian h)) η hη.1
  refine ⟨m,?_,hm,hocc⟩
  by_contra! hsmall
  have hall := (uniform_circuit_budget_iff_all_spectral_phases e H ((hω k).comp_equiv e.symm) m η).mp hm.1
  have hc := hall (anchoredBooleanProjectivePhase x)
  rw [projectiveSpectralMatrix_anchoredBooleanProjectivePhase] at hc
  obtain ⟨z,hz,C,hC,he⟩ := hc
  exact (not_lt_of_ge (he.trans hη.2)) (hx z hz C (hC.trans hsmall))

#print axioms gaussian_pauli_prefix_maximum_and_occupation_quantiles

/-- At physical error 1/10, at least half of long-window time costs half the
actual maximum at error 1/5, and at least two thirds costs a quarter of the
actual maximum at error 2/5. Both reference maxima exceed the exponential
budget, and the finite-window bounds hold at every origin. -/
theorem gaussian_pauli_physical_error_occupation_relative_to_actual_maxima :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in Filter.atTop,
      let N := k+3
      let h := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian h,isSelfAdjoint_pathHamiltonian h⟩
      ∃ m₁ m₂ : ℕ, nearHilbertContinuousCircuitBudget N < m₂ ∧ m₂ ≤ m₁ ∧
        IsRecurrentOrbitCircuitMaximumAt H (1/5) m₁ ∧ IsRecurrentOrbitCircuitMaximumAt H (2/5) m₂ ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ (s : ℕ) (a T : ℝ), 0 ≤ T →
          let L := volume.real ({t | HasProjectiveCircuitApproximation N (1/10:ℝ) s
            (unitaryEvolution H.val t)} ∩ Icc a (a+T))
          (2*s < m₁ → 2*L ≤ T+B) ∧ (4*s < m₂ → 3*L ≤ T+B) := by
  filter_upwards [gaussian_pauli_prefix_maximum_and_occupation_quantiles] with ω hω
  filter_upwards [hω] with k hk
  obtain ⟨m₁,_,hm₁,u,hu,h₁⟩ := hk (1/5) (by constructor <;> norm_num)
  obtain ⟨m₂,hm,hm₂,v,hv,h₂⟩ := hk (2/5) (by constructor <;> norm_num)
  obtain ⟨_,w,_,hw,hvisit⟩ := hm₂.2
  obtain ⟨t,_,ht⟩ := hvisit 0
  obtain ⟨z,hz,C,hC,he⟩ := hm₁.1 t
  have horder := (ht t ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C (he.trans (by norm_num))).trans hC
  refine ⟨m₁,m₂,hm,horder,hm₁,hm₂,max u v,hu.trans (le_max_left ..),?_⟩
  intro s a T hT
  constructor
  · intro hs
    have h := h₁ 1 s (by decide) (by simpa using hs) (1/10) (by norm_num) (by norm_num) a T hT
    norm_num at h
    exact h.trans (add_le_add_right (le_max_left ..) _)
  · intro hs
    have hb : 2*s*2 < m₂ := by omega
    have h := h₂ 2 s (by decide) hb (1/10) (by norm_num) (by norm_num) a T hT
    norm_num at h
    exact h.trans (add_le_add_right (le_max_right ..) _)

#print axioms gaussian_pauli_physical_error_occupation_relative_to_actual_maxima
end
end GaloisForLFunctions.HTGeometry
