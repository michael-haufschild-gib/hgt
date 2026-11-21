import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows

/-! # Exact rate of physical transitions from one gate to zero -/
open MeasureTheory Set Filter Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstGate
noncomputable section
open SharpOccupation EmptyVisitFlux

/-- From the actual first robust crossing, the empty-entry flux counts
precisely the arrivals with minimum gate count one on a whole interval
immediately preceding the arrival. -/
theorem gaussian_one_to_zero_rate (ε : ℝ) (hε : 0 < ε) (hs : ε < sqrt 2) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := fun j => -H.2.isHermitian.eigenvalues j
      let x := physicalArc ε
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ F : ℝ → Finset ℝ, (∀ t T, t ∈ F T ↔ σ<t ∧ t≤T ∧ t∈visitSet H 0 ε ∧
          ∃ a<t, ∀ u ∈ Ioo a t, orbitCircuitDistance H 1 u < ε ∧ ε < orbitCircuitDistance H 0 u) ∧
          Tendsto (fun T : ℝ => ((F T).card:ℝ)/(T-σ)) atTop (𝓝 (x^(2^N-2:ℕ)*pairTurnRate E)) := by
  filter_upwards [gaussian_one_gate_before_entry ε hε hs,gaussian_first_crossing_flux] with ω hone hcross
  filter_upwards [hcross] with k hk
  intro N H P E x
  obtain ⟨σ,hσ,he,hbefore,hF⟩ := hk
  obtain ⟨hmem,hrate⟩ := hF ε hε hs
  refine ⟨σ,hσ,he,hbefore,entriesAfter E x σ,?_,hrate⟩
  intro t T
  rw [hmem t T]
  constructor
  · rintro ⟨ht,hT,hv,δ,hδ,hh⟩
    have hentry : visitEntry (fun j => E j/(2*π)) x t :=
      ⟨(physical_visit H hε hs t).mpr hv,δ,hδ,fun u hu hf => hh u hu ((physical_visit H hε hs u).mp hf)⟩
    exact ⟨ht,hT,hv,mem_nhdsLT_iff_exists_Ioo_subset.mp (hone k t (hσ.trans ht) hentry)⟩
  · rintro ⟨ht,hT,hv,a,ha,h⟩
    refine ⟨ht,hT,hv,t-a,sub_pos.mpr ha,?_⟩
    intro u hu hcheap
    rw [sub_sub_cancel] at hu
    exact (h u hu).2.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hcheap)

#print axioms gaussian_one_to_zero_rate
end
end GaloisForLFunctions.HTGeometry.FirstGate
