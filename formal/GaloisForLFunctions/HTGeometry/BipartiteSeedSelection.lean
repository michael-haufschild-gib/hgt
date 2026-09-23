import GaloisForLFunctions.HTGeometry.BipartitePhaseSeedCollision

/-!
# Selecting one good product phase seed

The mean spectral collision of a product phase seed against an orthonormal family of the bipartite
space is at most `4 |ι| / D²`.  The phase box carries unit volume, so this mean is an average, and
some seed is at least as good as the average: at family size `D` there is a product seed whose
spectral collision is at most `4 / D`.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Selection

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

instance isProbabilityMeasure_restrict_torusBox (d : Type*) [Fintype d] [DecidableEq d] :
    IsProbabilityMeasure ((volume : Measure (d → ℝ)).restrict (torusBox d)) :=
  ⟨by rw [Measure.restrict_apply_univ, volume_torusBox]⟩

theorem integrableOn_box_inner_prodPhaseSeed_fourth (e : α × β → ℂ) :
    IntegrableOn (fun θ : (α ⊕ β) → ℝ => ‖finiteComplexInner e (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      (torusBox (α ⊕ β)) volume := by
  classical
  have hcont : Continuous fun θ : (α ⊕ β) → ℝ =>
      ‖finiteComplexInner e (prodPhaseSeed θ)‖ ^ (4 : ℕ) := by
    have hc : Continuous fun θ : (α ⊕ β) → ℝ => finiteComplexInner e (prodPhaseSeed θ) := by
      refine continuous_finsetSum (Finset.univ : Finset (α × β)) fun p _ => ?_
      exact continuous_const.mul (continuous_const.mul (continuous_phaseVec_apply p))
    exact (hc.norm).pow 4
  refine integrableOn_box_of_bounded_real hcont
    (C := (∑ p, ‖e p‖ * ‖((Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) : ℝ) : ℂ)⁻¹‖) ^ (4 : ℕ))
    fun θ => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
  rw [prodPhaseSeed, norm_mul, RCLike.norm_conj, norm_mul, norm_phaseVec, mul_one]

theorem integrableOn_box_sum_inner_prodPhaseSeed_fourth {ι : Type*} [Fintype ι]
    (e : ι → α × β → ℂ) :
    IntegrableOn (fun θ : (α ⊕ β) → ℝ =>
        ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ)) (torusBox (α ⊕ β)) volume :=
  integrable_finsetSum _ fun j _ => integrableOn_box_inner_prodPhaseSeed_fourth (e j)

/-- **One product seed below the mean.**  Some product phase seed has spectral collision at most
`4 |ι| / D²` in the given orthonormal family. -/
theorem exists_prodPhaseSeed_collision_le {ι : Type*} [Fintype ι]
    (e : ι → α × β → ℂ) (he : ∀ j, (∑ p, ‖e j p‖ ^ (2 : ℕ)) = 1) :
    ∃ θ : (α ⊕ β) → ℝ,
      (∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
        ≤ 4 * (Fintype.card ι : ℝ) / ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) := by
  classical
  set μ : Measure ((α ⊕ β) → ℝ) := (volume : Measure ((α ⊕ β) → ℝ)).restrict (torusBox (α ⊕ β))
    with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_restrict_torusBox (α ⊕ β)
  have hne : μ ≠ 0 := IsProbabilityMeasure.ne_zero μ
  obtain ⟨θ, hθ⟩ := exists_le_average (μ := μ)
    (f := fun θ : (α ⊕ β) → ℝ => ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ)) hne
    (integrableOn_box_sum_inner_prodPhaseSeed_fourth e)
  refine ⟨θ, le_trans hθ ?_⟩
  rw [average_eq_integral]
  exact integral_box_sum_inner_prodPhaseSeed_fourth_le e he

/-- **Theorem B in selected form.**  For an orthonormal basis of the bipartite space there is a
product phase seed whose spectral collision is at most `4 / D`. -/
theorem exists_prodPhaseSeed_collision_le_four_div {ι : Type*} [Fintype ι]
    (e : ι → α × β → ℂ) (he : ∀ j, (∑ p, ‖e j p‖ ^ (2 : ℕ)) = 1)
    (hcard : Fintype.card ι = Fintype.card α * Fintype.card β)
    (hα : 0 < Fintype.card α) (hβ : 0 < Fintype.card β) :
    ∃ θ : (α ⊕ β) → ℝ,
      (∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
        ≤ 4 / ((Fintype.card α : ℝ) * Fintype.card β) := by
  obtain ⟨θ, hθ⟩ := exists_prodPhaseSeed_collision_le e he
  refine ⟨θ, le_trans hθ (le_of_eq ?_)⟩
  have hαR : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast hα
  have hβR : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hβ
  rw [hcard]
  push_cast
  field_simp

end Selection

end GaloisForLFunctions.HTGeometry

end
