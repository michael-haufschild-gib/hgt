import GaloisForLFunctions.RHTower.PaperSliceCoefficientOperator

/-! # Exact negative index of the full coefficient operator

The negative coordinate space is an explicit witness. Restriction to those
coordinates embeds every negative-definite subspace into a space of the same
finite dimension. Every positive repair must act injectively on that witness.
-/

noncomputable section

open Set
open scoped BigOperators

namespace RHTower.PaperSliceCoefficient

def negativeSpace (t : Height) : Submodule ℂ EllTwo :=
  Submodule.span ℂ (Set.range fun i : negatives t => (lp.single 2 i.val (1 : ℂ) : EllTwo))

instance finiteDimensional_negativeSpace (t : Height) : FiniteDimensional ℂ (negativeSpace t) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem finrank_negativeSpace (t : Height) :
    Module.finrank ℂ (negativeSpace t) = negativeCount t := by
  classical
  have h := (HilbertSchmidt.lpBasis ℕ).orthonormal.linearIndependent.comp
    (fun i : negatives t => i.val) Subtype.val_injective
  change LinearIndependent ℂ (fun i : negatives t => (HilbertSchmidt.lpBasis ℕ) i.val) at h
  have h' : LinearIndependent ℂ (fun i : negatives t => (lp.single 2 i.val (1 : ℂ) : EllTwo)) := by
    simpa only [HilbertSchmidt.lpBasis_apply] using h
  convert finrank_span_eq_card h' using 1 <;>
    simp only [negativeSpace, negativeCount, Fintype.card_coe]
  congr 1

theorem negativeSpace_vanishes (t : Height) {f : EllTwo} (hf : f ∈ negativeSpace t)
    {n : ℕ} (hn : n ∉ negatives t) : f n = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hf
  rw [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hni : n ≠ i.val := fun h => hn (h ▸ i.property)
  simp [lp.single_apply, hni]

theorem negativeSpace_strict (t : Height) {f : EllTwo}
    (hf : f ∈ negativeSpace t) (hf0 : f ≠ 0) : quadratic t f < 0 := by
  have hsupport : ∀ n ∉ negatives t, coefficient t n * Complex.normSq (f n) = 0 := by
    intro n hn
    rw [negativeSpace_vanishes t hf hn, Complex.normSq_zero, mul_zero]
  rw [quadratic_eq_tsum, tsum_eq_sum hsupport]
  have hex : ∃ n, f n ≠ 0 := by
    by_contra h
    push Not at h
    apply hf0
    ext n
    exact h n
  obtain ⟨n, hn⟩ := hex
  have hmem : n ∈ negatives t := by
    by_contra h
    exact hn (negativeSpace_vanishes t hf h)
  apply Finset.sum_neg'
  · intro k hk
    exact mul_nonpos_of_nonpos_of_nonneg ((mem_negatives t k).1 hk).le (Complex.normSq_nonneg _)
  · exact ⟨n, hmem, mul_neg_of_neg_of_pos ((mem_negatives t n).1 hmem)
      (Complex.normSq_pos.mpr hn)⟩

theorem quadratic_nonneg_of_negative_coordinates_zero (t : Height) (f : EllTwo)
    (hf : ∀ n ∈ negatives t, f n = 0) : 0 ≤ quadratic t f := by
  rw [quadratic_eq_tsum]
  apply tsum_nonneg
  intro n
  by_cases hn : n ∈ negatives t
  · rw [hf n hn, Complex.normSq_zero, mul_zero]
  · exact mul_nonneg (nonneg_of_not_mem_negatives t hn) (Complex.normSq_nonneg _)

/-- All negative subspaces inject into the actual negative source coordinates. -/
theorem negative_subspace_finite_dimension (t : Height) (W : Submodule ℂ EllTwo)
    (hW : ∀ f ∈ W, f ≠ 0 → quadratic t f < 0) :
    FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeCount t := by
  let L : W →ₗ[ℂ] (negatives t → ℂ) :=
    { toFun := fun f n => (f : EllTwo) n.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    by_contra h0
    have hneg := hW f f.property (fun h => h0 (Subtype.ext h))
    have hpos := quadratic_nonneg_of_negative_coordinates_zero t f (fun n hn => ?_)
    · exact not_lt_of_ge hpos hneg
    · exact congrFun hf ⟨n, hn⟩
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  refine ⟨FiniteDimensional.of_injective L hinj, ?_⟩
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, negativeCount] using hdim

theorem negative_subspace_dimension_le (t : Height) (W : Submodule ℂ EllTwo)
    (hW : ∀ f ∈ W, f ≠ 0 → quadratic t f < 0) :
    Module.finrank ℂ W ≤ negativeCount t := (negative_subspace_finite_dimension t W hW).2

theorem exact_negative_index (t : Height) :
    (∀ W : Submodule ℂ EllTwo,
      (∀ f ∈ W, f ≠ 0 → quadratic t f < 0) →
        FiniteDimensional ℂ W ∧ Module.finrank ℂ W ≤ negativeCount t) ∧
    ∃ W : Submodule ℂ EllTwo, Module.finrank ℂ W = negativeCount t ∧
      ∀ f ∈ W, f ≠ 0 → quadratic t f < 0 :=
  ⟨negative_subspace_finite_dimension t,
    negativeSpace t, finrank_negativeSpace t, fun _ hf h0 => negativeSpace_strict t hf h0⟩

/-- Arbitrary coordinate-mixing repairs must pay the full negative dimension. -/
theorem negativeCount_le_repair_rank (t : Height) (K : EllTwo →L[ℂ] EllTwo) {r : ℕ}
    (hr : HasRankLE K r) (hpos : (operator t + K).IsPositive) : negativeCount t ≤ r := by
  obtain ⟨V, hV, hdim, hmem⟩ := hr
  letI := hV
  let L : negativeSpace t →ₗ[ℂ] V :=
    (K.toLinearMap.comp (negativeSpace t).subtype).codRestrict V (fun f => hmem f)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    by_contra h0
    have hK : K (f : EllTwo) = 0 := congrArg Subtype.val hf
    have hneg := negativeSpace_strict t f.property (fun h => h0 (Subtype.ext h))
    have hp := hpos.re_inner_nonneg_left (f : EllTwo)
    change 0 ≤ (inner ℂ ((operator t + K) (f : EllTwo)) (f : EllTwo)).re at hp
    rw [add_apply, hK, add_zero] at hp
    exact not_lt_of_ge hp hneg
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [finrank_negativeSpace] at h
  exact h.trans hdim

end RHTower.PaperSliceCoefficient
