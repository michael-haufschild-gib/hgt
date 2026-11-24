import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.DependentDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.PrecisionFloor

/-! # Spectral independence at genuine first physical visits -/

open Set MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
open AccuracyScales.MaximumIntervals PrecisionReturns
noncomputable section

/-- Relative eigenphases with the all-false spectral label as anchor. -/
def contactPhases (ω : PathPauliDisorder) (k : ℕ) (t : ℝ) :
    {i : Fin (k+3) → Bool // i ≠ fun _ => false} → ℂ :=
  let E := (chainGenerator ω k).2.isHermitian.eigenvalues
  fun i => energyPhase (projectiveFrequency E (fun _ => false) i) t

/-- Almost surely one countable set of coarse tolerances covers every
failure of spectral independence at a physical contact, simultaneously
over all dates, gate budgets and prefixes. -/
theorem gaussian_contact_spectral_independence :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ E : Set ℝ, E.Countable ∧ ∀ e ∉ E, ∀ (k s : ℕ) (t : ℝ),
      orbitCircuitDistance (chainGenerator ω k) s t=e → AlgebraicIndependent ℚ (contactPhases ω k t) := by
  classical
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  let Z (k : ℕ) := {t : ℝ | ¬ AlgebraicIndependent ℚ (contactPhases ω k t)}
  have hz (k : ℕ) : (Z k).Countable := countable_dependent_dates ℚ
    (maximallyProjectiveEnergy_projectiveFrequency_independent _ (hω k) (fun _ => false))
  let E := ⋃ (k : ℕ) (s : ℕ), orbitCircuitDistance (chainGenerator ω k) s '' Z k
  refine ⟨E,countable_iUnion (fun k : ℕ => countable_iUnion (fun _ : ℕ => (hz k).image _)),?_⟩
  intro e he k s t h
  by_contra ht
  exact he (mem_iUnion.mpr ⟨k,mem_iUnion.mpr ⟨s,t,ht,h⟩⟩)

/-- At each distinguished first return from outside the budget tube, all
2ᴺ−1 relative phases are algebraically independent over the rationals,
apart from countably many errors for the entire frozen chain. -/
theorem gaussian_first_visit_spectral_independence :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e ∉ E →
      ∀ (k s : ℕ) (a : ℝ), let H := chainGenerator ω k
      e < orbitCircuitDistance H s a → AlgebraicIndependent ℚ (contactPhases ω k (firstVisit H a s e)) := by
  filter_upwards [gaussian_contact_spectral_independence] with ω hω
  obtain ⟨E,hE,h⟩ := hω
  refine ⟨E,hE,?_⟩
  intro e he hreg k s a H hout
  exact h e hreg k s _ (firstVisit_distance H a s he hout)

#print axioms gaussian_first_visit_spectral_independence
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
