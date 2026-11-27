import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.OccupationBounds
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.PhysicalCutoff

/-! # Sharp late return exponent after selection on the first-excursion history -/
open Filter Set MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
open SharpOccupation
noncomputable section

private theorem selected_interval (k P r j : ℕ) (ε l b : ℝ)
    (hbds₀ : ∀ᵐ ω ∂pathPauliDisorderLaw, l ≤ affordablePhaseMass k j ε ω ∧ affordablePhaseMass k j ε ω ≤ b) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
      ∃ p : ℝ, μ.real B*l ≤ p ∧ p ≤ μ.real B*b ∧
        Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+t)≤ε})) atTop (𝓝 p) ∧
        Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+crossingWait n P r x+t)≤ε})) atTop (𝓝 p) := by
  intro n μ σ B hB
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let A := X ⁻¹' B
  let W := affordablePhaseMass k j ε
  have hX := gaussian_pauli_prefix_coordinates_law n
  have hmass : pathPauliDisorderLaw.real A=μ.real B := hX.measureReal_preimage hB.nullMeasurableSet
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hw : Integrable W (pathPauliDisorderLaw.restrict A) := (integrable_affordablePhaseMass k j ε).integrableOn
  have hbds : ∀ᵐ ω ∂(pathPauliDisorderLaw.restrict A), l ≤ W ω ∧ W ω ≤ b :=
    ae_restrict_of_ae hbds₀
  have hlo := integral_mono_ae (integrable_const (l)) hw (hbds.mono fun _ h => h.1)
  have hhi := integral_mono_ae hw (integrable_const (b)) (hbds.mono fun _ h => h.2)
  change (∫ _ in A, l ∂pathPauliDisorderLaw) ≤ _ at hlo
  change _ ≤ (∫ _ in A, b ∂pathPauliDisorderLaw) at hhi
  rw [setIntegral_const,smul_eq_mul,hmass] at hlo hhi
  exact ⟨_,hlo,hhi,gaussian_selected_budget_distribution k P r j ε B hB⟩


/-- The same sharp exponential interval holds after any measurable
selection of the original prefix, with no lower bound on the selection
probability. Both clocks refer to this draw's actual first excursion. -/
theorem selected_late_budget_exponent (s : ℕ→ℕ) (hs : subcriticalBudget s)
    {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) (Real.sqrt 2)) {l b : ℝ}
    (hl : 0≤l) (hlx : l<physicalArc ε) (hxb : physicalArc ε<b) :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := k+3
      let P := nearHilbertContinuousCircuitBudget K
      let D := 2^K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ r j : ℕ, j ≤ s K → ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
        ∃ p : ℝ, μ.real B*l^D ≤ p ∧ p ≤ μ.real B*b^D ∧
          Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+t)≤ε})) atTop (𝓝 p) ∧
          Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+crossingWait n P r x+t)≤ε})) atTop (𝓝 p) := by
  filter_upwards [subcritical_phase_mass s hs hε hl hlx hxb] with k hk
  intro n K P D μ σ r j hj B hB
  exact selected_interval k P r j ε (l^D) (b^D) (hk.mono fun _ h => h j hj) B hB

/-- Even an arbitrarily rare selected history has exponentially small
conditional probability of a near-Hilbert-budget fit at sufficiently
late prescribed delays from either end of the original first wait. -/
theorem selected_hilbert_snapshot {ε : ℝ} (hε : ε ∈ Ioo (0:ℝ) (Real.sqrt 2)) :
    ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := k+3
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ r j : ℕ, j ≤ P → ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B →
        ∃ p : ℝ, p ≤ μ.real B*b^(2^K:ℕ) ∧
          Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+t)≤ε})) atTop (𝓝 p) ∧
          Tendsto (fun t => μ.real (B ∩ {x | pathGateDistance n j x (σ x+crossingWait n P r x+t)≤ε})) atTop (𝓝 p) := by
  obtain ⟨b,hb,hcut⟩ := WeakBonds.NearDiagonal.physical_record_cutoff ε hε.1 hε.2
  refine ⟨b,hb,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hcut] with k hk
  intro n K P μ σ r j hj B hB
  have hw : ∀ᵐ ω ∂pathPauliDisorderLaw, 0 ≤ affordablePhaseMass k j ε ω ∧
      affordablePhaseMass k j ε ω ≤ b^(2^K:ℕ) := by
    filter_upwards [gaussian_path_all_prefixes_maximally_projective,PhaseBoundary.gaussian_uniform_affordable_fraction]
      with ω hr hlim
    let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
    have hh := hlim k j ε (fun _ => 0)
    simp only [zero_add] at hh
    refine ⟨measureReal_nonneg,le_of_tendsto hh ?_⟩
    filter_upwards [hk H (hr k) 0,eventually_ge_atTop (0:ℝ)] with T ht hT
    exact (visitFraction_mono H hj ε 0 T hT).trans ht.le
  obtain ⟨p,_,hu,ht⟩ := selected_interval k P r j ε 0 _ hw B hB
  exact ⟨p,hu,ht⟩

#print axioms selected_late_budget_exponent
#print axioms selected_hilbert_snapshot
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
