import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.ReturnObservations
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrefixDeadlines.DifferenceWindows
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.VisitIndices.Counting

/-! # Exponential rarity of larger-prefix visits counted at smaller-prefix dips -/

open MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
open PrescribedTimes SharpOccupation
noncomputable section

/-- On one chain the rare-event exponent D log x survives observation
at genuine low returns of any strict smaller prefix. The reciprocal
frequency counts smaller-prefix dips per simultaneous affordable reading. -/
theorem gaussian_nested_return_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ g : ℕ → ℕ, subcriticalBudget g →
      ∀ ε ∈ Ioo (0:ℝ) 2, ∀ l b : ℝ, 0<l → l<physicalArc ε → physicalArc ε<b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
          isSelfAdjoint_pathHamiltonian _⟩
        ∀ (j : ℕ), j<k → ∀ (P s q : ℕ), q≤g N →
          let x := fun i => pathPauliDisorderShell ω (j+1) (pathCoeffEquiv (j+1) i)
          let t := returnClock (j+1) P s x
          let A := visitSet H q ε
          ∃ p ∈ Ioo (l^D) (b^D),
            Tendsto (fun M => (integerClockPrefixLaw t M : Measure ℝ).real A) atTop (𝓝 p) ∧
            {i | t i∈A}.Infinite ∧
            Tendsto (fun i : ℕ => (Nat.nth (fun h => t h∈A) i:ℝ)/i) atTop (𝓝 p⁻¹) := by
  obtain ⟨c,hc⟩ := FiniteRecords.gaussian_finite_physical_rates_full
  filter_upwards [hc,gaussian_return_observations] with ω hrate hobs
  intro g hg ε hε l b hl hlx hxb
  obtain ⟨u,hlu,hux⟩ := exists_between hlx
  obtain ⟨w,hxw,hwb⟩ := exists_between hxb
  filter_upwards [hrate g hg ε hε u w (hl.trans hlu) hux hxw] with k hk
  intro N D H j hj P s q hq x t A
  obtain ⟨p,hlim,hrec⟩ := hobs k j P s hj q ε
  have h := hlim (fun _ => 0)
  have hr := (hk q hq 0).1
  have he : ∀ᶠ T : ℝ in atTop, visitFraction H q ε 0 (0+T) ∈ Icc (u^D) (w^D) :=
    (eventually_ge_atTop _).mono fun T ht => ⟨(hr T ht).1.le,(hr T ht).2.le⟩
  have hp := isClosed_Icc.mem_of_tendsto h he
  have hD : D≠0 := (Nat.two_pow_pos N).ne'
  have hup : l^D<p := (pow_lt_pow_left₀ hlu hl.le hD).trans_le hp.1
  have hpb : p<b^D := hp.2.trans_lt (pow_lt_pow_left₀ hwb ((hl.trans hlx).trans hxw).le hD)
  have hm : MeasurableSet A := (ReturnExcursions.PrefixDeadlines.closed_visits H q ε).measurableSet
  exact ⟨p,⟨hup,hpb⟩,hrec,
    EntrySensitivity.PrescribedCharacters.VisitIndices.return_index_spacing t A hm
      ((pow_pos hl D).trans hup) hrec⟩

#print axioms gaussian_nested_return_rate
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
