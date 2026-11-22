import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Rate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.CrossingRecords

/-! # Depth distribution of continuous empty-circuit visits after the first crossing -/
open Filter MeasureTheory Real Set Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
open SharpOccupation EmptyVisitFlux
noncomputable section

/-- Count each distinct continuous visit once. The fraction reaching any
smaller tolerance is a power of the ratio of their enclosing arc lengths.
The exponent is two below the Hilbert dimension. -/
theorem gaussian_crossing_visit_depth :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let energy := fun j => -H.2.isHermitian.eigenvalues j
      ∃ σ > 0, orbitCircuitDistance H P σ = 9/80 ∧
        (∀ v ∈ Ico 0 σ, orbitCircuitDistance H P v < 9/80) ∧
        ∀ ε ∈ Ioc (0:ℝ) (1/10), ∀ δ ∈ Ioc (0:ℝ) ε,
          let A := entriesAfter energy (physicalArc ε) σ
          let M := fun T => marked (visitSet H 0 ε) (visitSet H 0 δ) (A T)
          Tendsto (fun T : ℝ => ((M T).card:ℝ)/(A T).card) atTop
            (𝓝 ((physicalArc δ/physicalArc ε)^(2^N-2:ℕ))) := by
  filter_upwards [eventual_unit_separation,gaussian_first_crossing_flux,gaussian_empty_visit_flux] with ω hs hc hp
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hs,hc] with k hs hc
  intro N H P energy
  obtain ⟨σ,hσ,he,hfirst,hflux⟩ := hc
  refine ⟨σ,hσ,he,hfirst,?_⟩
  intro ε hε δ hδ A M
  have hδ' : δ∈Ioc (0:ℝ) (1/10) := ⟨hδ.1,hδ.2.trans hε.2⟩
  have hsmall : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (show (0:ℝ)≤2 by norm_num),sqrt_nonneg 2])
  let B := entriesAfter energy (physicalArc δ) σ
  have closed (r : ℝ) : IsClosed (visitSet H 0 r) := by
    simp only [visitSet,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have ha : σ∉visitSet H 0 ε := by
    intro h
    have h' := (hasProjectiveCircuitApproximation_iff_infDist _ P ε).mp (h.mono_budget (Nat.zero_le P))
    change orbitCircuitDistance H P σ≤ε at h'
    linarith only [he,h',hε.2]
  have sub : visitSet H 0 δ ⊆ visitSet H 0 ε := by
    rintro u ⟨z,hz,C,hC,h⟩
    exact ⟨z,hz,C,hC,h.trans hδ.2⟩
  obtain ⟨hae,hag⟩ := hs ε hε
  have hbg := (hs δ hδ').2
  obtain ⟨hA,hlA⟩ := hflux ε hε.1 hsmall
  obtain ⟨hB,hlB⟩ := hflux δ hδ.1 (hδ.2.trans_lt hsmall)
  have hpos := (hp k ε hε.1 hsmall).2.1
  have hh := fraction_of_count_bounds (fun T => (A T).card) (fun T => (B T).card)
    (fun T => (M T).card) σ _ _ hpos hlA hlB
    (count_bounds (closed ε) (closed δ) sub ha hae hag hbg A B hA hB)
  have hn : pairTurnRate energy ≠ 0 := (mul_ne_zero_iff.mp hpos.ne').2
  rwa [mul_div_mul_right _ _ hn,←div_pow] at hh

#print axioms gaussian_crossing_visit_depth
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
