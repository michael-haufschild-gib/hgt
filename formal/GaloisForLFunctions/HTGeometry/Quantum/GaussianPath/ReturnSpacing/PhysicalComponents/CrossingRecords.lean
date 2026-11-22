import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.EntryGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.RecordMean
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.ReturnSpacing

/-! # Exact mean spacing of unit-separated scalar records from the first physical crossing -/
open Filter MeasureTheory Real Set Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- At each small tolerance a visit excludes its unit translate, and every later fresh entry is farther than one unit away. -/
theorem eventual_unit_separation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ ε ∈ Ioc (0:ℝ) (1/10), let E := visitSet H 0 ε
      (∀ v ∈ E, v+1 ∉ E) ∧ (∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v) := by
  obtain ⟨A,c,_,hc,hfloor⟩ := gaussian_pauli_polynomial_interval_cost_floor
  have hN : Tendsto (fun n : ℕ => ((n+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hQ := (tendsto_rpow_atTop (show (0:ℝ)<(48:ℝ)⁻¹ by norm_num)).comp hN
  filter_upwards [hfloor,gaussian_physical_entry_gap] with ω hf hg
  filter_upwards [hf,hg,hN.eventually_ge_atTop A,hQ.eventually_ge_atTop 4] with n hf hg hs hq
  intro N H ε hε E
  have hp : 0<(N:ℝ) := by dsimp only [N]; positivity
  have h₁ : A/(N:ℝ) ≤ 1 := (div_le_iff₀ hp).mpr (by simpa only [one_mul] using hs)
  have h₂ : 1 ≤ (N:ℝ)^((48:ℝ)⁻¹)/4 := by
    change 4 ≤ (N:ℝ)^((48:ℝ)⁻¹) at hq
    linarith only [hq]
  have hw (u : ℝ) (hu : u ∈ E) : HasProjectiveCircuitApproximation N (1/10) 0 (unitaryEvolution H.val u) := by
    obtain ⟨z,hz,C,hC,he⟩ := hu
    exact ⟨z,hz,C,hC,he.trans hε.2⟩
  refine ⟨?_,fun v hv w he hlt => h₂.trans_lt (hg ε hε v hv w he.1 hlt he.2)⟩
  intro v hv hnext
  have h := (hf 1 h₁ h₂).2 v 0 0 (hw v hv) (hw _ hnext)
  have hp' : 0<c*sqrt (N:ℝ) := mul_pos hc (sqrt_pos.mpr hp)
  exact hp'.not_ge (by simpa only [Nat.cast_zero,add_zero] using h)

/-- The first robust crossing is an admissible observation origin. For
every tolerance through 1/10 the actual record spacing has a finite-prefix
limit, the reciprocal of the true continuous entry flux. -/
theorem gaussian_crossing_record_mean :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let energy := fun j => -H.2.isHermitian.eigenvalues j
      ∃ σ > 0, orbitCircuitDistance H P σ = 9/80 ∧
        (∀ v ∈ Ico 0 σ, orbitCircuitDistance H P v < 9/80) ∧
        ∀ ε ∈ Ioc (0:ℝ) (1/10), let rate := (physicalArc ε)^(2^N-2:ℕ)*pairTurnRate energy
          (∃ t, records H 0 ε σ t) ∧
          ∀ t, records H 0 ε σ t → Tendsto (fun j : ℕ => (t j-σ)/j) atTop (𝓝 (1/rate)) := by
  filter_upwards [eventual_unit_separation,gaussian_first_crossing_flux,gaussian_empty_visit_flux] with ω hs hcross hrate
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hs,hcross] with k hs hcross
  intro N H P energy
  obtain ⟨σ,hσ,hfirst,hbefore,hflux⟩ := hcross
  refine ⟨σ,hσ,hfirst,hbefore,?_⟩
  intro ε hε rate
  have hsmall : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg 2])
  obtain ⟨hx,htol⟩ := physicalArc_spec hε.1 hsmall
  obtain ⟨hg,he⟩ := hs ε hε
  obtain ⟨hF,hlim⟩ := hflux ε hε.1 hsmall
  refine ⟨?_,fun t ht => ?_⟩
  · simpa only [htol] using exists_records H 0 ⟨physicalArc ε,hx⟩ σ
  · exact record_mean _ σ _ t ht.1 ht.2 hg he hF ((hrate k ε hε.1 hsmall).2.1) hlim

#print axioms gaussian_crossing_record_mean
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
