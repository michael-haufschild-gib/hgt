import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FineAffordability.CharacterFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ContactRecurrence.FineAffordability.ScalarVisits
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.FirstWait

/-! # Fine circuit affordability detects freeness on the first physical excursion clock -/

open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
open PrecisionReturns EntrySensitivity.PrescribedCharacters
noncomputable section

/-- Through the actual first scalar dip, either all fine scalar tubes
recur on the unshifted clock or a single positive error excludes every
disconnected budget at every signed index. -/
theorem gaussian_first_excursion_fine_dichotomy :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧ (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        let Δ := v-σ
        ∀ b : Fin N → Bool, let w := projectiveFrequency H.2.isHermitian.eigenvalues b
          (FreeAtStep w Δ ∧ ∀ ε>0,
            {n : ℕ | HasProjectiveCircuitApproximation N ε 0 (unitaryEvolution H.val (σ+(n:ℝ)*Δ))}.Infinite) ∨
          (¬FreeAtStep w Δ ∧ ∃ ε>0, ∀ n : ℤ, ∀ s : ℕ, s+1<N →
            ε<orbitCircuitDistance H s (σ+(n:ℝ)*Δ)) := by
  filter_upwards [gaussian_first_crossing_scalar_clock,DisconnectedReturns.gaussian_disconnected_scalar_return] with ω hc hs
  filter_upwards [hc] with k hk
  intro N H P
  obtain ⟨σ,hσ,hcross,hprior,hv⟩ := hk
  refine ⟨σ,hσ,hcross,hprior,?_⟩
  intro v Δ b w
  by_cases hf : FreeAtStep w Δ
  · exact Or.inl ⟨hf,fun _ he => free_scalar_visits H b σ Δ hf he⟩
  · obtain ⟨η,hη,hex⟩ := fine_gap_of_resonance w v Δ (hv b).1 hf
    obtain ⟨A,hA,ha⟩ := hs (k+1)
    let ε := η/A
    have he : 0<ε := div_pos hη hA
    refine Or.inr ⟨hf,ε,he,?_⟩
    intro n s hs'
    by_contra! hh
    have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mpr hh
    have hsc := ha (σ+(n:ℝ)*Δ) ε s (by dsimp only [N] at hs'; omega) hfit
    have htol : A*ε=η := by dsimp only [ε]; field_simp
    rw [htol] at hsc
    apply hex (n-1)
    intro i
    have ht : v+((n-1:ℤ):ℝ)*Δ=σ+(n:ℝ)*Δ := by dsimp only [Δ]; push_cast; ring
    rw [ht]
    exact anchored_gaps_of_empty H b hη hsc i.val

#print axioms gaussian_first_excursion_fine_dichotomy
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.FineAffordability
