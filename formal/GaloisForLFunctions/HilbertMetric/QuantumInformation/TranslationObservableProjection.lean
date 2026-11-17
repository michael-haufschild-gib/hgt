import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationObservableAlgebra

/-!
# The translation average is a unital norm-one projection

The average maps the concrete closed observable algebra onto the closed
linear span of its translation generators. It fixes that span pointwise,
annihilates rank-one generators, and is an idempotent operator of norm one.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

/-- A concrete generator regarded as an element of the closed domain. -/
def generatorElement (g : ObservableGenerator) : ObservableDomain :=
  ⟨generatorObservable g, generatorObservable_mem_domain g⟩

/-- The average with its proved range restriction to the generated domain. -/
def averageEnd : ObservableDomain →L[ℂ] ObservableDomain :=
  (closedObservableAverage.toLinearMap.codRestrict observableDomain
    closedObservableAverage_mem_domain : ObservableDomain →ₗ[ℂ] ObservableDomain).mkContinuous 1
      (fun A => by
        change ‖closedObservableAverage A‖ ≤ 1 * ‖A‖
        exact (closedObservableAverage.le_opNorm A).trans
          (mul_le_mul_of_nonneg_right norm_closedObservableAverage_le_one (norm_nonneg _)))

@[simp] theorem coe_averageEnd (A : ObservableDomain) :
    (averageEnd A : Observable) = closedObservableAverage A := rfl

/-- The average fixes translation generators and removes all remaining generators. -/
theorem averageEnd_generator (g : ObservableGenerator) :
    averageEnd (generatorElement g) =
      match g with
      | .inl (_, k) => if k = 0 then generatorElement g else 0
      | .inr _ => 0 := by
  cases g with
  | inl p =>
    rcases p with ⟨a, k⟩
    change averageEnd (generatorElement (.inl (a, k))) =
      if k = 0 then generatorElement (.inl (a, k)) else 0
    by_cases hk : k = 0
    · subst k
      rw [if_pos rfl]
      apply Subtype.ext
      change closedObservableAverage (generatorElement (.inl (a, 0))) =
        generatorObservable (.inl (a, 0))
      rw [generatorElement, closedObservableAverage_generator]
      simp only [retainedGenerator, generatorObservable, if_true, Int.cast_zero,
        mul_zero, weylWord_zero_frequency]
    · rw [if_neg hk]
      apply Subtype.ext
      change closedObservableAverage (generatorElement (.inl (a, k))) = 0
      rw [generatorElement, closedObservableAverage_generator]
      change (if k = 0 then translation a else 0) = 0
      rw [if_neg hk]
  | inr p =>
    apply Subtype.ext
    change closedObservableAverage (generatorElement (.inr p)) = 0
    rw [generatorElement, closedObservableAverage_generator]
    rfl

/-- The finite span of the actual translation generators inside the closed observable domain. -/
def translationCore : Submodule ℂ ObservableDomain :=
  Submodule.span ℂ (Set.range fun a : ℝ => generatorElement (.inl (a, 0)))

/-- The closed translation space retained by the averaging projection. -/
def translationClosed : Submodule ℂ ObservableDomain := translationCore.topologicalClosure

private theorem average_generator_mem_core (g : ObservableGenerator) :
    averageEnd (generatorElement g) ∈ translationCore := by
  rw [averageEnd_generator]
  cases g with
  | inl p =>
    rcases p with ⟨a, k⟩
    change (if k = 0 then generatorElement (.inl (a, k)) else 0) ∈ translationCore
    by_cases hk : k = 0
    · subst k
      rw [if_pos rfl]
      exact Submodule.subset_span ⟨a, rfl⟩
    · rw [if_neg hk]
      exact translationCore.zero_mem
  | inr p => exact translationCore.zero_mem

private theorem symbolEmbedding_expansion (p : ObservableSymbol) :
    symbolEmbedding p = ∑ g ∈ p.support, p g • generatorElement g := by
  apply Subtype.ext
  change evaluateSymbol p = observableInclusion (∑ g ∈ p.support, p g • generatorElement g)
  rw [map_sum]
  simp only [map_smul]
  rw [evaluateSymbol, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g _
  rfl

private theorem average_symbol_mem_core (p : ObservableSymbol) :
    averageEnd (symbolEmbedding p) ∈ translationCore := by
  rw [symbolEmbedding_expansion, map_sum]
  apply translationCore.sum_mem
  intro g _
  rw [map_smul]
  exact translationCore.smul_mem _ (average_generator_mem_core g)

/-- Every averaged observable belongs to the closed span of actual translations. -/
theorem averageEnd_mem_translationClosed (A : ObservableDomain) :
    averageEnd A ∈ translationClosed := by
  have hm : ∀ B : ObservableDomain, B ∈ Set.range symbolEmbedding →
      averageEnd B ∈ translationClosed := by
    rintro B ⟨p, rfl⟩
    exact translationCore.le_topologicalClosure (average_symbol_mem_core p)
  have hc : IsClosed {B : ObservableDomain | averageEnd B ∈ translationClosed} :=
    translationCore.isClosed_topologicalClosure.preimage averageEnd.continuous
  exact symbolEmbedding_denseRange.induction hm hc A

private theorem average_fixes_core {A : ObservableDomain} (hA : A ∈ translationCore) :
    averageEnd A = A := by
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨a, rfl⟩ := hA
    simpa only [if_true] using averageEnd_generator (.inl (a, 0))
  | zero => exact map_zero _
  | add A B _ _ hA hB => rw [map_add, hA, hB]
  | smul c A _ hA => rw [map_smul, hA]

/-- Fixed observables are exactly the closed translation space. -/
theorem averageEnd_fixed_iff (A : ObservableDomain) :
    averageEnd A = A ↔ A ∈ translationClosed := by
  constructor
  · intro h
    rw [← h]
    exact averageEnd_mem_translationClosed A
  · intro hA
    have hc : IsClosed {B : ObservableDomain | averageEnd B = B} :=
      isClosed_eq averageEnd.continuous continuous_id
    have hs : closure (translationCore : Set ObservableDomain) ⊆
        {B : ObservableDomain | averageEnd B = B} :=
      hc.closure_subset_iff.mpr fun B hB => average_fixes_core hB
    exact hs hA

/-- Actual weak averaging is idempotent throughout its closed domain. -/
theorem averageEnd_idempotent (A : ObservableDomain) :
    averageEnd (averageEnd A) = averageEnd A :=
  (averageEnd_fixed_iff _).mpr (averageEnd_mem_translationClosed A)

/-- The exact range of averaging is the closed span of translation observables. -/
theorem averageEnd_range : LinearMap.range averageEnd.toLinearMap = translationClosed := by
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    exact averageEnd_mem_translationClosed B
  · intro hA
    exact ⟨A, (averageEnd_fixed_iff A).mpr hA⟩

/-- Identity as an actual element of the generated closed operator algebra. -/
def identityElement : ObservableDomain := ⟨1, closedObservableAlgebra.one_mem⟩

/-- The closed-domain averaging projection preserves the actual identity operator. -/
theorem averageEnd_identity : averageEnd identityElement = identityElement := by
  have he : identityElement = generatorElement (.inl (0, 0)) := by
    apply Subtype.ext
    change (1 : Observable) = generatorObservable (.inl (0, 0))
    simp only [generatorObservable, Int.cast_zero, mul_zero, weylWord_zero_frequency]
    apply ContinuousLinearMap.ext
    intro v
    exact (shift_zero v).symm
  rw [he]
  simpa only [if_true] using averageEnd_generator (.inl (0, 0))

/-- The unital averaging projection has operator norm exactly one. -/
theorem norm_averageEnd : ‖averageEnd‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    change ‖closedObservableAverage A‖ ≤ 1 * ‖A‖
    exact (closedObservableAverage.le_opNorm A).trans
      (mul_le_mul_of_nonneg_right norm_closedObservableAverage_le_one (norm_nonneg _))
  · have h := averageEnd.le_opNorm identityElement
    have hi : ‖identityElement‖ = 1 := by
      change ‖(1 : Observable)‖ = 1
      letI : Nontrivial Space := by
        refine ⟨⟨lp.single 2 (0 : ℝ) (1 : ℂ), 0, ?_⟩⟩
        intro h
        have he := congrArg (fun x : Space => x 0) h
        simp at he
      exact norm_one
    rw [averageEnd_identity, hi, mul_one] at h
    exact h

#print axioms averageEnd_generator
#print axioms averageEnd_mem_translationClosed
#print axioms averageEnd_fixed_iff
#print axioms averageEnd_idempotent
#print axioms averageEnd_range
#print axioms averageEnd_identity
#print axioms norm_averageEnd
end GaloisForLFunctions.HilbertMetric.ShiftAverage
