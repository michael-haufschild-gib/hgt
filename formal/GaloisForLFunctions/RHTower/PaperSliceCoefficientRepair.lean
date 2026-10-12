import GaloisForLFunctions.RHTower.PaperSliceCoefficientInertia

/-! # Optimal positive repair of the literal coefficient operator

Finite repair always exists, but its minimum rank is exactly the number of
negative source coefficients. The lower bound includes coordinate-mixing repairs.
-/

noncomputable section

open scoped BigOperators

namespace RHTower.PaperSliceCoefficient

theorem mem_negativeSpace_of_vanishes (t : Height) (f : EllTwo)
    (hf : ∀ n ∉ negatives t, f n = 0) : f ∈ negativeSpace t := by
  classical
  have hsum : f = ∑ i : negatives t, f i.val • (lp.single 2 i.val (1 : ℂ) : EllTwo) := by
    ext n
    rw [lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
    by_cases hn : n ∈ negatives t
    · rw [Finset.sum_eq_single (⟨n, hn⟩ : negatives t)]
      · simp
      · intro i _ hi
        have hni : n ≠ i.val := fun h => hi (Subtype.ext h.symm)
        simp [hni]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    · rw [hf n hn]
      symm
      apply Finset.sum_eq_zero
      intro i _
      have hni : n ≠ i.val := fun h => hn (h ▸ i.property)
      simp [hni]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def repairCoefficient (t : Height) (n : ℕ) : ℝ :=
  if coefficient t n < 0 then -coefficient t n else 0

theorem repairCoefficient_nonneg (t : Height) (n : ℕ) : 0 ≤ repairCoefficient t n := by
  unfold repairCoefficient
  split_ifs with hn
  · exact neg_nonneg.mpr hn.le
  · exact le_rfl

theorem norm_repairCoefficient_le (t : Height) (n : ℕ) :
    ‖(repairCoefficient t n : ℂ)‖ ≤ budget t := by
  unfold repairCoefficient
  split_ifs
  · simpa only [Complex.ofReal_neg, norm_neg] using norm_coefficient_cast_le t n
  · simpa using budget_nonneg t

/-- Cancel exactly the negative entries, leaving the original operator unchanged. -/
def repair (t : Height) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (fun n => (repairCoefficient t n : ℂ)) (norm_repairCoefficient_le t)

theorem repair_apply (t : Height) (f : EllTwo) (n : ℕ) :
    repair t f n = (repairCoefficient t n : ℂ) * f n := rfl

theorem positive_repair (t : Height) : (repair t).IsPositive :=
  GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal _ _ (repairCoefficient_nonneg t)

theorem hasRankLE_repair (t : Height) : HasRankLE (repair t) (negativeCount t) := by
  refine ⟨negativeSpace t, inferInstance, (finrank_negativeSpace t).le, fun f => ?_⟩
  apply mem_negativeSpace_of_vanishes
  intro n hn
  have hnot : ¬ coefficient t n < 0 := fun h => hn ((mem_negatives t n).2 h)
  rw [repair_apply, repairCoefficient, if_neg hnot]
  simp

theorem positive_repaired_operator (t : Height) : (operator t + repair t).IsPositive := by
  have hb : ∀ n, ‖((coefficient t n + repairCoefficient t n : ℝ) : ℂ)‖ ≤ budget t + budget t := by
    intro n
    push_cast
    exact (norm_add_le _ _).trans (add_le_add (norm_coefficient_cast_le t n)
      (norm_repairCoefficient_le t n))
  have heq : operator t + repair t =
      diagonalOperator (fun n => ((coefficient t n + repairCoefficient t n : ℝ) : ℂ)) hb := by
    ext f n
    simp only [add_apply, lp.coeFn_add, Pi.add_apply, operator_apply, repair_apply,
      diagonalOperator_apply, Complex.ofReal_add, add_mul]
  rw [heq]
  apply GaloisForLFunctions.RHTower.isPositive_diagonalOperator_ofReal
  intro n
  unfold repairCoefficient
  split_ifs with hn
  · simp
  · simpa using le_of_not_gt hn

/-- Sharp rank classification, with no diagonal restriction on the repair. -/
theorem positive_repair_rank_iff (t : Height) (r : ℕ) :
    (∃ K : EllTwo →L[ℂ] EllTwo, HasRankLE K r ∧ (operator t + K).IsPositive) ↔
      negativeCount t ≤ r := by
  constructor
  · rintro ⟨K, hr, hp⟩
    exact negativeCount_le_repair_rank t K hr hp
  · intro hr
    exact ⟨repair t, (hasRankLE_repair t).mono hr, positive_repaired_operator t⟩

theorem repair_exact_rank (t : Height) (r : ℕ) :
    HasRankLE (repair t) r ↔ negativeCount t ≤ r :=
  ⟨fun h => negativeCount_le_repair_rank t _ h (positive_repaired_operator t),
    fun h => (hasRankLE_repair t).mono h⟩

theorem exists_finite_positive_repair (t : Height) :
    ∃ r : ℕ, ∃ K : EllTwo →L[ℂ] EllTwo, HasRankLE K r ∧ (operator t + K).IsPositive :=
  ⟨negativeCount t, repair t, hasRankLE_repair t, positive_repaired_operator t⟩

theorem all_rank_zero_repair_iff :
    (∀ t : Height, ∃ K : EllTwo →L[ℂ] EllTwo,
      HasRankLE K 0 ∧ (operator t + K).IsPositive) ↔ RiemannHypothesis := by
  simp only [positive_repair_rank_iff, Nat.le_zero, all_negativeCount_zero_iff]

end RHTower.PaperSliceCoefficient
