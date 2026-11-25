import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.PhysicalClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.LatticeFraction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting

/-! # Finite gaps and doubly exponential average spacing on the first-excursion clock -/

open Filter Set MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
open SharpOccupation PrecisionReturns EntrySensitivity.PrescribedCharacters.VisitIndices
noncomputable section

/-- On the actual unshifted first-scalar-wait clock, at every budget
up to the crossing budget, consecutive affordable indices have bounded
gaps. The ith index eventually exceeds 16^(2^N)(i+1)−1. -/
theorem gaussian_unshifted_excursion_return_indices :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (PrecisionReturns.Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        let Δ := firstVisit H σ 0 (1/10)-σ
        0<Δ ∧ ∃ B : ℕ, ∀ s≤P,
          let hit (n : ℕ) := HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val (σ+(n:ℝ)*Δ))
          (setOf hit).Infinite ∧ (∀ i, Nat.nth hit (i+1)≤Nat.nth hit i+B) ∧
            ∀ᶠ i : ℕ in atTop, 16^D*(i+1)≤Nat.nth hit i := by
  filter_upwards [gaussian_unshifted_first_excursion_tick_gaps,gaussian_lattice_eighth_upper] with ω hg hu
  filter_upwards [hg,hu] with k hk hrate
  intro N D H P
  obtain ⟨σ,hσ,hc,hb,hstep,B,hgap⟩ := hk
  refine ⟨σ,hσ,hc,hb,?_⟩
  intro Δ
  refine ⟨hstep,B+1,?_⟩
  intro s hs hit
  let f (n : ℕ) := σ+(n:ℝ)*Δ
  let A := SharpOccupation.visitSet H s (1/10)
  have hA : MeasurableSet A := by
    rw [show A={t | orbitCircuitDistance H s t≤1/10} from Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist ..]
    exact (isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const).measurableSet
  have hgap' (n : ℕ) : ∃ l ∈ Icc n (n+B), hit l := by
    obtain ⟨l,hl,z,hz,C,hC,he⟩ := hgap n
    exact ⟨l,hl,z,hz,C,hC.trans (Nat.zero_le _),he⟩
  obtain ⟨hi,hupper⟩ := bounded_tick_indices hit hgap'
  refine ⟨hi,hupper,sparse_prefix_indices f A hA hi (by positivity) ?_⟩
  filter_upwards [hrate σ Δ (ne_of_gt hstep)] with M hm
  exact hm s hs (1/10) (by norm_num)

#print axioms gaussian_unshifted_excursion_return_indices
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence
