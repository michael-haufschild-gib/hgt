import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualRouteTBudget

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- The literal diagonal dual summand in the exact square AFE has integrable squared norm
on every retained dyadic block. -/
theorem integrableOn_normSq_smoothAFEZetaSquareDualAFESummand
    {N : ℕ} (hN : 4 ≤ N) :
    IntegrableOn (fun t : ℝ => ‖smoothAFEZetaSquareDualAFESummand N t‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) := by
  let S : Set ℝ := Set.Icc (N : ℝ) (2 * N : ℝ)
  let F : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualSourceField (N : ℝ) (N : ℝ) t
  let V : ℝ → ℂ := fun t =>
    smoothAFEZetaSquareDualVariationSourceField (N : ℝ) (N : ℝ) t t
  have hFint : Integrable (fun t => ‖F t‖ ^ 2) (volume.restrict S) :=
    integrableOn_normSq_smoothAFEZetaSquareDualFrozenSourceField hN
  have hVint : Integrable (fun t => ‖V t‖ ^ 2) (volume.restrict S) :=
    integrableOn_normSq_smoothAFEZetaSquareDualVariationSourceField_diagonal hN
  have hFm : AEStronglyMeasurable F (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualFrozenSourceField N).aestronglyMeasurable.restrict
  have hVm : AEStronglyMeasurable V (volume.restrict S) :=
    (measurable_smoothAFEZetaSquareDualVariationSourceField_diagonal hN).aestronglyMeasurable.restrict
  have hsumInt := GaloisForLFunctions.HTGeometry.integrable_normSq_add_measure
    hFm hVm hFint hVint
  refine hsumInt.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  dsimp only [F, V, S]
  rw [norm_smoothAFEZetaSquareDualAFESummand_eq_sourceField,
    smoothAFEZetaSquareDualSourceField_diagonal_eq_frozen_add_variation hN ht]

end RHTower
