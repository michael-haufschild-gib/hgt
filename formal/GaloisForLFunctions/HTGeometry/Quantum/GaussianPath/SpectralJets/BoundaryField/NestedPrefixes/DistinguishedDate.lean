import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ConditionalEntries
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # Conditional null sets for the first physical scalar return after the plateau crossing -/

open Set MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrecisionReturns
noncomputable section

/-- Reveal every coupling except the terminal longitudinal field. A measurable family
of null dates misses the actual first scalar return at error one tenth after the
first near-Hilbert crossing, almost surely on all sufficiently long prefixes. -/
theorem gaussian_conditional_distinguished_date (S : ℕ → Set (PathPauliDisorder × ℝ))
    (hm : ∀ k, MeasurableSet (S k))
    (hS : ∀ k (η : PathPauliDisorder), volume (Prod.mk η ⁻¹' S k)=0) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        (eraseTerminal k ω,firstVisit H σ 0 (1/10))∉S k := by
  have he : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := ⟨by norm_num,
    by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]⟩
  filter_upwards [gaussian_first_crossing_precision_wait,
    ae_all_iff.mpr (fun k => gaussian_conditional_entries k he (S k) (hm k) (hS k))] with ω hσ hd
  filter_upwards [hσ] with k hk
  intro N H P
  obtain ⟨σ,hpos,hcross,hprior,_⟩ := hk
  refine ⟨σ,hpos,hcross,hprior,hd k σ hpos ?_⟩
  by_contra! h
  obtain ⟨c,hc,Q,hQ,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
  have hp : orbitCircuitDistance H P σ≤1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
    ⟨c,hc,Q,hQ.trans (Nat.zero_le _),herr⟩
  rw [show orbitCircuitDistance H P σ=9/80 from hcross] at hp
  norm_num at hp

#print axioms gaussian_conditional_distinguished_date
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
