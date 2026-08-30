import GaloisForLFunctions.HTGeometry.NumberFieldPrincipalIdealNormBound
import GaloisForLFunctions.HTGeometry.NumberFieldUnitPlaceLog

/-!
# Finite bounded principal ideals and weighted coordinate bounds

Bounded nonzero principal ideals form a finite type.  Choosing one nonzero generator for each
ideal turns equality of principal ideals into a finite representative bound.  A separate weighted
finite-coordinate lemma converts a nonnegative weighted sum and uniform upper coordinate bounds
into a two-sided sup-norm bound.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Nonzero principal ideals with absolute norm at most `N`. -/
def boundedNonzeroPrincipalIdeals (K : Type*) [Field K] [NumberField K] (N : ℕ) :=
  {I : Ideal (𝓞 K) // Ideal.absNorm I ≤ N ∧ I ≠ ⊥ ∧
    ∃ α : 𝓞 K, α ≠ 0 ∧ Ideal.span {α} = I}

noncomputable instance (N : ℕ) : Fintype (boundedNonzeroPrincipalIdeals K N) := by
  apply Set.Finite.fintype
  exact (Ideal.finite_setOf_absNorm_le N).subset fun I hI => hI.1

/-- A chosen nonzero generator of a bounded principal ideal. -/
def boundedPrincipalIdealGenerator {N : ℕ}
    (I : boundedNonzeroPrincipalIdeals K N) : 𝓞 K :=
  Classical.choose I.property.2.2

theorem boundedPrincipalIdealGenerator_ne_zero {N : ℕ}
    (I : boundedNonzeroPrincipalIdeals K N) :
    boundedPrincipalIdealGenerator I ≠ 0 :=
  (Classical.choose_spec I.property.2.2).1

theorem span_boundedPrincipalIdealGenerator {N : ℕ}
    (I : boundedNonzeroPrincipalIdeals K N) :
    Ideal.span {boundedPrincipalIdealGenerator I} = I.1 :=
  (Classical.choose_spec I.property.2.2).2

/-- A nonnegative weighted sum plus uniform coordinate upper bounds gives a two-sided norm bound. -/
theorem norm_le_weightedSum_mul_of_weightedSum_nonneg_of_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (hm : ∀ i, 1 ≤ m i) (x : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hsum : 0 ≤ ∑ i, m i * x i) (hupper : ∀ i, x i ≤ M) :
    ‖x‖ ≤ (∑ i, m i) * M := by
  have hm0 (i : ι) : 0 ≤ m i := le_trans zero_le_one (hm i)
  have htotal0 : 0 ≤ (∑ i, m i) * M :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hm0 i) hM
  apply (pi_norm_le_iff_of_nonneg htotal0).2
  intro i
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have hrest : (∑ j ∈ Finset.univ.erase i, m j * x j) ≤
        (∑ j ∈ Finset.univ.erase i, m j) * M := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hupper j) (hm0 j)
    have hsplit : m i * x i + ∑ j ∈ Finset.univ.erase i, m j * x j =
        ∑ j, m j * x j :=
      Finset.add_sum_erase Finset.univ (fun j => m j * x j) (Finset.mem_univ i)
    have hkey : -((∑ j, m j) * M) ≤ m i * x i := by
      have herase : (∑ j ∈ Finset.univ.erase i, m j) * M ≤
          (∑ j, m j) * M := by
        exact mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
            (fun j _ _ => hm0 j)) hM
      linarith [hsum, hrest, herase, hsplit]
    by_cases hxi : 0 ≤ x i
    · exact le_trans (neg_nonpos.mpr htotal0) hxi
    · have hmxi : m i * x i ≤ x i := by
        have hxnonpos : x i ≤ 0 := le_of_not_ge hxi
        simpa [one_mul] using mul_le_mul_of_nonpos_right (hm i) hxnonpos
      exact le_trans hkey hmxi
  · exact le_trans (hupper i) (by
      have hmSum : 1 ≤ ∑ j, m j :=
        le_trans (hm i) (Finset.single_le_sum (fun j _ => hm0 j) (Finset.mem_univ i))
      nlinarith)

/-- The weighted archimedean log sum of a nonzero algebraic integer is nonnegative. -/
theorem weightedSum_numberFieldIntegerPlaceLog_nonneg
    (α : 𝓞 K) (hα : α ≠ 0) :
    0 ≤ ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (w (α : K)) := by
  have hprod : 1 ≤ ∏ σ : K →+* ℂ, ‖σ (α : K)‖ :=
    one_le_prod_norm_embeddings α hα
  have hne (σ : K →+* ℂ) : ‖σ (α : K)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro hσ
    have hα0 : (α : K) = 0 := σ.injective (hσ.trans (map_zero σ).symm)
    exact hα (by exact_mod_cast hα0)
  have hlog : 0 ≤ ∑ σ : K →+* ℂ, Real.log ‖σ (α : K)‖ := by
    rw [← Real.log_prod (fun σ _ => hne σ)]
    exact Real.log_nonneg hprod
  rw [numberFieldEmbeddingSum_eq_placeSum (F := Real.log) (α : K)] at hlog
  exact hlog

end

end GaloisForLFunctions.HTGeometry
