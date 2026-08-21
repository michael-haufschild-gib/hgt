/-
# Chen--Gupta--Li Lemma 4.5 certified finite zero-mode aggregation

Packages a finite family of complex terms with a closed pointwise budget, then
instantiates it for all non-all-equal CGL fibre rows.  The subtype carrier keeps
the finite off-diagonal condition certified, avoiding repeated expansion of the
cubic filtered sum during later source-level estimates.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FibreZeroModeBound

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- A finite complex family with one certified uniform real norm budget. -/
structure CGLFiniteComplexBudget (α : Type*) where
  index : Finset α
  term : α → ℂ
  budget : ℝ
  point_bound (a : α) : a ∈ index → ‖term a‖ ≤ budget

namespace CGLFiniteComplexBudget

/-- Sum of the finite complex family. -/
def value {α : Type*} (B : CGLFiniteComplexBudget α) : ℂ :=
  ∑ a ∈ B.index, B.term a

/-- Sum of the uniform real budget over the same finite index set. -/
def totalBudget {α : Type*} (B : CGLFiniteComplexBudget α) : ℝ :=
  ∑ _a ∈ B.index, B.budget

/-- Triangle inequality for a certified finite complex budget. -/
theorem norm_value_le_totalBudget {α : Type*}
    (B : CGLFiniteComplexBudget α) :
    ‖B.value‖ ≤ B.totalBudget := by
  unfold value totalBudget
  refine le_trans (norm_sum_le _ _) ?_
  apply Finset.sum_le_sum
  intro a ha
  exact B.point_bound a ha

/-- Exact closed form for the total of a uniform finite budget. -/
theorem totalBudget_eq_card_mul {α : Type*}
    (B : CGLFiniteComplexBudget α) :
    B.totalBudget = (B.index.card : ℝ) * B.budget := by
  simp [totalBudget]

end CGLFiniteComplexBudget

/-- The finite certified family of all non-all-equal CGL fibre zero-mode row
terms, with its arbitrary-order reciprocal-decay budget. -/
def cglLemma45FibreZeroModeFiniteBudget
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    CGLFiniteComplexBudget (CGLLemma45FibreOffDiagonalTriple R) := by
  letI : Fintype (CGLLemma45FibreOffDiagonalTriple R) :=
    cglLemma45FibreOffDiagonalTripleFintype R
  exact
    { index := Finset.univ
      term := fun u => cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) u.1
      budget := cglLemma45FibreZeroModeRowBound P w N n
      point_bound := fun u _ => norm_cglLemma45FibreOffDiagonalZeroModeRow_le P w N n u }

/-- Closed finite aggregation of the CGL Lemma 4.5 zero-frequency row bounds. -/
theorem norm_cglLemma45FibreZeroModeFiniteBudgetValue_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ‖(cglLemma45FibreZeroModeFiniteBudget P w N n).value‖ ≤
      (cglLemma45FibreZeroModeFiniteBudget P w N n).totalBudget :=
  CGLFiniteComplexBudget.norm_value_le_totalBudget
    (cglLemma45FibreZeroModeFiniteBudget P w N n)

/-- Exact cardinal-times-row-budget form of the finite CGL zero-mode total. -/
theorem cglLemma45FibreZeroModeFiniteBudget_totalBudget_eq
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    (cglLemma45FibreZeroModeFiniteBudget P w N n).totalBudget =
      ((cglLemma45FibreZeroModeFiniteBudget P w N n).index.card : ℝ) *
        cglLemma45FibreZeroModeRowBound P w N n :=
  CGLFiniteComplexBudget.totalBudget_eq_card_mul
    (cglLemma45FibreZeroModeFiniteBudget P w N n)

/-- Exact reindexing from CGL's literal filtered off-diagonal row sum to the
certified subtype aggregate. -/
theorem cglLemma45FibreZeroModeFilteredSum_eq_budgetValue
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ∑ rst ∈ (cglCharacterDyadicGramCubicIndexSet R).filter
        (fun rst => ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)),
      cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) rst =
      (cglLemma45FibreZeroModeFiniteBudget P w N n).value := by
  classical
  letI : Fintype (CGLLemma45FibreOffDiagonalTriple R) :=
    cglLemma45FibreOffDiagonalTripleFintype R
  unfold cglLemma45FibreZeroModeFiniteBudget CGLFiniteComplexBudget.value
  apply Finset.sum_subtype
  intro rst
  simp [cglCharacterDyadicGramCubicIndexSet]

/-- Exact identification of the CGL Lemma 4.5 off-diagonal origin term with
its certified finite zero-mode aggregate. -/
theorem cglLemma45OffDiagonalFrequencyTerm_zero_eq_budgetValue
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0 =
      (cglLemma45FibreZeroModeFiniteBudget P w N n).value := by
  rw [cglLemma45OffDiagonalFrequencyTerm_zero_eq_sum_zeroModeRowTerm]
  exact cglLemma45FibreZeroModeFilteredSum_eq_budgetValue P w N n

/-- Closed finite bound for the literal zero-frequency CGL off-diagonal term. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_totalBudget
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLemma45FibreZeroModeFiniteBudget P w N n).totalBudget := by
  rw [cglLemma45OffDiagonalFrequencyTerm_zero_eq_budgetValue P w N n]
  exact norm_cglLemma45FibreZeroModeFiniteBudgetValue_le P w N n

/-- CGL's literal zero-frequency off-diagonal term is at most the number of
certified non-all-equal triples times the all-order row budget. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_cardRowBudget
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      ((cglLemma45FibreZeroModeFiniteBudget P w N n).index.card : ℝ) *
        cglLemma45FibreZeroModeRowBound P w N n := by
  refine le_trans
    (norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_totalBudget P w N n) ?_
  rw [cglLemma45FibreZeroModeFiniteBudget_totalBudget_eq]

/-- The stored finite aggregate index has exactly the certified off-diagonal
cubic-row cardinality. -/
theorem cglLemma45FibreZeroModeFiniteBudget_index_card
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    (cglLemma45FibreZeroModeFiniteBudget P w N n).index.card =
      cglLemma45FibreOffDiagonalTripleCard R := by
  classical
  letI : Fintype (CGLLemma45FibreOffDiagonalTriple R) :=
    cglLemma45FibreOffDiagonalTripleFintype R
  rfl

/-- Closed cubic-cardinality form of CGL's zero-frequency off-diagonal
estimate. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_cubicRowBudget
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (R : ℝ) ^ 3 * cglLemma45FibreZeroModeRowBound P w N n := by
  calc
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) 0‖ ≤
        ((cglLemma45FibreZeroModeFiniteBudget P w N n).index.card : ℝ) *
          cglLemma45FibreZeroModeRowBound P w N n :=
      norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_cardRowBudget P w N n
    _ = (cglLemma45FibreOffDiagonalTripleCard R : ℝ) *
          cglLemma45FibreZeroModeRowBound P w N n := by
      rw [cglLemma45FibreZeroModeFiniteBudget_index_card]
    _ ≤ (R : ℝ) ^ 3 * cglLemma45FibreZeroModeRowBound P w N n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast cglLemma45FibreOffDiagonalTriple_card_le R
      · exact cglLemma45FibreZeroModeRowBound_nonneg P w N n

end RHTower
