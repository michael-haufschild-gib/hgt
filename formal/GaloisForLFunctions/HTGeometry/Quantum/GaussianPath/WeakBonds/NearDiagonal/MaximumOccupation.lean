import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.AllTimeMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.OccupationBand

/-! # Long-time occupation relative to the same-error orbit maximum on a Gaussian sector -/

open Set Filter Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open DiagonalSynthesis SharpOccupation PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- A Gaussian sector of explicit mass has an exponential actual
maximum at error 1/10. Outside an exponentially small-in-dimension
fraction of every sufficiently long record from any fixed origin,
the gate minimum exceeds the maximum divided by O(K²). -/
theorem strong_sector_maximum_occupation :
    ∃ C > (0:ℝ), ∃ b ∈ Ioo (0:ℝ) 1, ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      ∃ E : Set PathPauliDisorder, MeasurableSet E ∧
        (1/10:ℝ)^(10*n+12)*exp (-C*(K:ℝ)^2) ≤ pathPauliDisorderLaw.real E ∧
        ∀ᵐ ω ∂pathPauliDisorderLaw, ω∈E →
          let u := pathPauliDisorderShell ω n
          let H : selfAdjoint (DiagonalSynthesis.Register K) :=
            ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
          (fun i => u (pathCoeffEquiv n i)) ∈ allCoordStrongEvent n (1/100) ∧
          ∃ m : ℕ, P < m ∧ m ≤ (2*K+1)*2^K ∧ IsRecurrentOrbitCircuitMaximumAt H (1/10) m ∧
            ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ s : ℕ, s*(64*(K+1))*(2*K+1) ≤ m →
              visitFraction H s (1/10) a T < b^(2^K:ℕ) := by
  obtain ⟨C,hC,hsector⟩ := all_strong_all_time_mass
  obtain ⟨b,hb,hcut⟩ := capped_path_occupation
  refine ⟨C,hC,b,hb,?_⟩
  filter_upwards [hcut] with k hk
  intro n K P
  obtain ⟨F,hF,hm,hcheap⟩ := hsector n (1/10) (by constructor <;> norm_num)
  let Y := fun (ω : PathPauliDisorder) l => pathPauliDisorderShell ω n l
  have hY := measurePreserving_pathDisorder_labels n
  refine ⟨Y ⁻¹' F,hF.preimage hY.measurable,hm.trans_eq (congrArg ENNReal.toReal
    (hY.measure_preimage hF.nullMeasurableSet)).symm,?_⟩
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω
  intro he u H
  obtain ⟨hstrong,hfit⟩ := hcheap (Y ω) he
  exact ⟨hstrong,hk u (hω k) (2*K+1) (by omega) hfit⟩

#print axioms strong_sector_maximum_occupation
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
