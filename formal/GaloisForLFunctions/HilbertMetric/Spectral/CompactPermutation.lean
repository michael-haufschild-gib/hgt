import GaloisForLFunctions.HTGeometry.ConstitutiveDependentLpGaugeTransport
import GaloisForLFunctions.HilbertMetric.SeparatedConfigurations
import GaloisForLFunctions.HTGeometry.BoundedFredholmStability

/-!
# Compact perturbations by coordinate permutations

A permutation of square-summable coordinates differs compactly from identity
exactly when it moves finitely many coordinates. Distinct moved coordinate
vectors have uniformly separated displacement columns. Finite support gives
an explicit finite-dimensional range for the converse.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric.PermutationCompact
open scoped lp
open Set

abbrev Space (ι : Type*) := ℓ²(ι, ℂ)

/-- Permuting coordinates is an isometry of the square-summable space. -/
def permutationOperator {ι : Type*} (e : Equiv.Perm ι) : Space ι →L[ℂ] Space ι :=
  (HTGeometry.lpDependentDomCongrIsometry (𝕜 := ℂ) (E := fun _ : ι => ℂ)
    (p := 2) (by norm_num) e).toContinuousLinearMap

/-- The unit coordinate vector. -/
def coordinate {ι : Type*} (i : ι) : Space ι := by
  classical
  exact lp.single 2 i (1 : ℂ)

private theorem norm_coordinate {ι : Type*} (i : ι) : ‖coordinate i‖ = 1 := by
  classical
  rw [coordinate, lp.norm_single (by norm_num), norm_one]

theorem permutationOperator_apply {ι : Type*} (e : Equiv.Perm ι) (x : Space ι) (i : ι) :
    permutationOperator e x i = x (e i) := rfl

private theorem defect_apply {ι : Type*} (e : Equiv.Perm ι) (x : Space ι) (i : ι) :
    ((permutationOperator e - 1) x) i = x (e i) - x i := rfl

/-- The displacement of a coordinate vector under a permutation. -/
def column {ι : Type*} (e : Equiv.Perm ι) (i : ι) : Space ι :=
  (permutationOperator e - 1) (coordinate i)

private theorem column_separated {ι : Type*} (e : Equiv.Perm ι) {i j : ι}
    (hi : e i ≠ i) (hij : i ≠ j) : 1 ≤ ‖column e i - column e j‖ := by
  classical
  have hc : 1 ≤ ‖(column e i - column e j) i‖ := by
    change 1 ≤ ‖(coordinate i (e i) - coordinate i i) -
      (coordinate j (e i) - coordinate j i)‖
    by_cases he : e i = j
    · norm_num [coordinate, lp.single_apply, Pi.single_apply, hi, he, hij, Ne.symm hij]
    · norm_num [coordinate, lp.single_apply, Pi.single_apply, hi, he, hij, Ne.symm hij]
  exact hc.trans (lp.norm_apply_le_norm (by norm_num) _ i)

/-- A coordinate permutation is a compact perturbation of identity exactly when its support is finite. -/
theorem isCompact_permutationOperator_sub_one_iff {ι : Type*} (e : Equiv.Perm ι) :
    IsCompactOperator (permutationOperator e - 1 : Space ι →L[ℂ] Space ι) ↔
      {i : ι | e i ≠ i}.Finite := by
  classical
  constructor
  · intro hcompact
    have hK := IsCompactOperator.isCompact_closure_image_closedBall
      (f := (permutationOperator e - 1).toLinearMap) hcompact 1
    have hfinite : (column e '' {i : ι | e i ≠ i}).Finite :=
      finite_of_dist_separated_of_subset_compact (by norm_num : (0 : ℝ) < 1)
        (by
          rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩ hne
          have hij : i ≠ j := fun h => hne (congrArg (column e) h)
          simpa only [dist_eq_norm] using column_separated e hi hij)
        hK (by
          rintro x ⟨i, hi, rfl⟩
          exact subset_closure ⟨coordinate i,
            by simp only [Metric.mem_closedBall, dist_zero_right, norm_coordinate, le_refl], rfl⟩)
    apply Set.Finite.of_finite_image hfinite
    intro i hi j hj heq
    by_contra hij
    have hs := column_separated e hi hij
    rw [heq, sub_self, norm_zero] at hs
    norm_num at hs
  · intro hfinite
    let V : Submodule ℂ (Space ι) := Submodule.span ℂ (coordinate '' {i : ι | e i ≠ i})
    haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (hfinite.image coordinate)
    have hrange : LinearMap.range (permutationOperator e - 1).toLinearMap ≤ V := by
      rintro y ⟨x, rfl⟩
      change (permutationOperator e - 1) x ∈ V
      have hx : (permutationOperator e - 1) x =
          ∑ i ∈ hfinite.toFinset, ((permutationOperator e - 1) x i) • coordinate i := by
        apply lp.ext
        funext j
        simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply,
          coordinate, lp.single_apply, Pi.single_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq]
        by_cases hj : e j = j
        · simp [permutationOperator_apply, hj]
        · simp [hj]
      rw [hx]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, (hfinite.mem_toFinset).mp hi, rfl⟩
    exact HTGeometry.isCompactOperator_of_finiteDimensional_range
      (Submodule.finiteDimensional_of_le hrange)

#print axioms isCompact_permutationOperator_sub_one_iff
end GaloisForLFunctions.HilbertMetric.PermutationCompact
