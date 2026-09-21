import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridCompletion

/-!
# Finite-grid witnesses on the completed cuspidal form ball

The closed relative grid estimate yields an actual vector in the finite grid
space whenever its two geometric error terms fit below a prescribed tolerance.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- If the core and cusp budgets fit below `ε`, every completed cuspidal form
vector of norm at most one has an `ε`-close witness in the fixed reciprocal grid. -/
theorem exists_reciprocal_grid_cuspidal_witness_of_formNorm_le_one
    {N M K : ℕ} (hM : 0 < M)
    (hY : 1 ≤ Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)
    {ε : ℝ}
    (hbudget :
      Real.sqrt (((Real.sqrt 3 / 2) ^ 2)⁻¹ * (16 * ((M : ℝ)⁻¹) ^ 2)) +
        Real.sqrt ((((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
          (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2) < ε)
    (v : CuspidalFormDomain N) (hv : ‖(v : FormTriple N)‖ ≤ 1) :
    ∃ g : DeckL2 N,
      g ∈ deckFiniteCellSpan (N := N)
        (upperChartGridCell (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
        (measurableSet_upperChartGridCell (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹)) ∧
      ‖cuspidalFormInclusion N v - g‖ < ε := by
  let V : Submodule ℂ (DeckL2 N) :=
    deckFiniteCellSpan (N := N)
      (upperChartGridCell (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
      (measurableSet_upperChartGridCell (M := M) (K := K)
        (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
  let A : ℝ := ((Real.sqrt 3 / 2) ^ 2)⁻¹ * (16 * ((M : ℝ)⁻¹) ^ 2)
  let B : ℝ := (((N + 1 : ℝ) / (2 * Real.pi)) ^ 2) *
    (Real.sqrt 3 / 2 + (K : ℝ) * (M : ℝ)⁻¹)⁻¹ ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hnormsq : ‖(v : FormTriple N)‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (v : FormTriple N)]
  have hAunit : A * ‖(v : FormTriple N)‖ ^ 2 ≤ A := by
    calc
      A * ‖(v : FormTriple N)‖ ^ 2 ≤ A * 1 :=
        mul_le_mul_of_nonneg_left hnormsq hA
      _ = A := mul_one A
  have hBunit : B * ‖(v : FormTriple N)‖ ^ 2 ≤ B := by
    calc
      B * ‖(v : FormTriple N)‖ ^ 2 ≤ B * 1 :=
        mul_le_mul_of_nonneg_left hnormsq hB
      _ = B := mul_one B
  have hdist := cuspidalFormDomain_infDist_le_reciprocal_grid_formBudget hM hY v
  have hdist' : Metric.infDist (cuspidalFormInclusion N v) (V : Set (DeckL2 N)) ≤
      Real.sqrt A + Real.sqrt B := by
    calc
      Metric.infDist (cuspidalFormInclusion N v) (V : Set (DeckL2 N)) ≤
          Real.sqrt (A * ‖(v : FormTriple N)‖ ^ 2) +
            Real.sqrt (B * ‖(v : FormTriple N)‖ ^ 2) := by
        simpa [V, A, B] using hdist
      _ ≤ Real.sqrt A + Real.sqrt B :=
        add_le_add (Real.sqrt_le_sqrt hAunit) (Real.sqrt_le_sqrt hBunit)
  have hinf : Metric.infDist (cuspidalFormInclusion N v) (V : Set (DeckL2 N)) < ε := by
    refine hdist'.trans_lt ?_
    simpa [A, B] using hbudget
  obtain ⟨g, hgV, hg⟩ := (Metric.infDist_lt_iff (show (V : Set (DeckL2 N)).Nonempty from
      ⟨0, V.zero_mem⟩)).mp hinf
  refine ⟨g, ?_, ?_⟩
  · simpa [V] using hgV
  · rwa [dist_eq_norm] at hg

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
