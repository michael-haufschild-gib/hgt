import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridClosure

/-!
# Completed finite-grid control for cuspidal Maass forms

The source-level grid approximation defines a closed cone in the completed
three-coordinate form domain.  Thus its quantitative estimate survives
completion without selecting an approximating source sequence.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- A reciprocal finite grid controls the first coordinate of every completed
cuspidal form vector by its full form norm. -/
theorem cuspidalFormDomain_infDist_le_reciprocal_grid_formBudget {N M K : ℕ}
    (hM : 0 < M)
    (hY : 1 ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
    (v : CuspidalFormDomain N) :
    Metric.infDist (cuspidalFormInclusion N v)
        (deckFiniteCellSpan (N := N)
          (upperChartGridCell (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
          (measurableSet_upperChartGridCell (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)) : Set (DeckL2 N)) ≤
      Real.sqrt
        ((((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ * (16 * ((M : ℝ)⁻¹) ^ (2 : ℕ))) *
          ‖(v : FormTriple N)‖ ^ (2 : ℕ)) +
      Real.sqrt
        ((((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) *
          (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ (2 : ℕ) *
            ‖(v : FormTriple N)‖ ^ (2 : ℕ)) := by
  let V : Submodule ℂ (DeckL2 N) :=
    deckFiniteCellSpan (N := N)
      (upperChartGridCell (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
      (measurableSet_upperChartGridCell (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
  let A : ℝ := ((Real.sqrt 3 / 2) ^ (2 : ℕ))⁻¹ * (16 * ((M : ℝ)⁻¹) ^ (2 : ℕ))
  let B : ℝ := (((N + 1 : ℝ) / (2 * Real.pi)) ^ (2 : ℕ)) *
    (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ (2 : ℕ)
  have hclosed : IsClosed {w : FormTriple N |
      Metric.infDist (w.ofLp 0) (V : Set (DeckL2 N)) ≤
        Real.sqrt (A * ‖w‖ ^ (2 : ℕ)) + Real.sqrt (B * ‖w‖ ^ (2 : ℕ))} :=
    isClosed_infDist_le_sqrt_formBudget (V : Set (DeckL2 N)) A B
  have hrange : ((LinearMap.range (cuspidalFormEmbeddingMap N) :
      Submodule ℂ (FormTriple N)) : Set (FormTriple N)) ⊆
      {w : FormTriple N |
        Metric.infDist (w.ofLp 0) (V : Set (DeckL2 N)) ≤
          Real.sqrt (A * ‖w‖ ^ (2 : ℕ)) + Real.sqrt (B * ‖w‖ ^ (2 : ℕ))} := by
    rintro w ⟨F, rfl⟩
    obtain ⟨C, hC⟩ := exists_reciprocal_grid_cuspidal_error_le_formNorm hM hY F
    calc
      Metric.infDist ((cuspidalFormEmbeddingMap N F).ofLp 0) (V : Set (DeckL2 N)) ≤
          dist ((cuspidalFormEmbeddingMap N F).ofLp 0)
            (deckGridStep (N := N) (M := M) (K := K)
              (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C) :=
        Metric.infDist_le_dist_of_mem
          (deckGridStep_mem_deckFiniteCellSpan (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C)
      _ = ‖toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) -
          deckGridStep (N := N) (M := M) (K := K)
            (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹) C‖ := by
        rw [dist_eq_norm]
        rfl
      _ ≤ Real.sqrt (A * ‖cuspidalFormEmbeddingMap N F‖ ^ (2 : ℕ)) +
          Real.sqrt (B * ‖cuspidalFormEmbeddingMap N F‖ ^ (2 : ℕ)) := by
        simpa [A, B] using hC
  have hclosure : (cuspidalFormDomainClosure N : Set (FormTriple N)) ⊆
      {w : FormTriple N |
        Metric.infDist (w.ofLp 0) (V : Set (DeckL2 N)) ≤
          Real.sqrt (A * ‖w‖ ^ (2 : ℕ)) + Real.sqrt (B * ‖w‖ ^ (2 : ℕ))} := by
    change closure ((LinearMap.range (cuspidalFormEmbeddingMap N) :
      Submodule ℂ (FormTriple N)) : Set (FormTriple N)) ⊆ _
    exact hclosed.closure_subset_iff.mpr hrange
  have hv := hclosure v.property
  change Metric.infDist (cuspidalFormInclusion N v) (V : Set (DeckL2 N)) ≤
    Real.sqrt (A * ‖(v : FormTriple N)‖ ^ (2 : ℕ)) +
      Real.sqrt (B * ‖(v : FormTriple N)‖ ^ (2 : ℕ)) at hv
  simpa [V, A, B] using hv

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
