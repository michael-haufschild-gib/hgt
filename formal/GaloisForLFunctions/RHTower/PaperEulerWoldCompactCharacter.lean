import GaloisForLFunctions.RHTower.PaperEulerWoldDepthHistory

/-!
# The Euler--Wold blind plane is exactly the compact ideal

The full source history is compact precisely when its coefficient vanishes or its reporter lies
in the native blind plane. The budgeted compensated reporter is compact; the endpoint and the
source-budgeted transverse reporter survive the compact quotient. Their exact positive separation
cannot be repaired by any compact mixing of source depths.
-/

namespace RHTower

noncomputable section
open Complex Classical
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

/-- The zero coefficient and the native blind plane exhaust character vanishing. -/
theorem paperEulerWold_character_eq_zero_iff (a b d : ℝ) (c : ℂ) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter a b d c = 0 ↔
      c = 0 ∨ -a + b + 2*d = 0 := by
  by_cases hc : c = 0
  · subst c
    simp [sourceHorizontalEulerWoldJordanConormalCofinalCharacter]
  · rw [sourceHorizontalEulerWoldJordanConormalCofinalCharacter_eq_zero_iff hc]
    simp only [hc, false_or]

/-- The blind plane is the exact intersection of source histories with the compact ideal. -/
theorem paperEulerWoldHistoryOperator_compact_iff (a b d : ℝ) (c : ℂ) :
    IsCompactOperator (paperEulerWoldHistoryOperator a b d c) ↔
      c = 0 ∨ -a + b + 2*d = 0 := by
  rw [paperEulerWoldHistoryOperator, paperConvergentDiagonal_compact_iff,
    Complex.ofReal_eq_zero, paperEulerWold_character_eq_zero_iff]

/-- Exact ideal cost of the full, source-only, infinite depth history. -/
theorem paperEulerWoldHistoryOperator_traceCost (a b d : ℝ) (c : ℂ) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperEulerWoldHistoryOperator a b d c) =
        if c = 0 ∨ -a + b + 2*d = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperEulerWoldHistoryOperator_compact_iff]
  split_ifs <;> rfl

/-- Compact changes may mix all depths but cannot alter the exact blind-plane classification. -/
theorem paperEulerWoldHistoryOperator_traceCost_add_compact (a b d : ℝ) (c : ℂ)
    (K : compactOperatorStarAlgebra (lp (fun _ : ℕ => ℂ) 2)) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperEulerWoldHistoryOperator a b d c + K.1) =
        if c = 0 ∨ -a + b + 2*d = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, paperEulerWoldHistoryOperator_traceCost]

/-- The essential norm measures the exact amplitude transverse to the blind plane. -/
theorem paperEulerWoldHistoryOperator_essential_amplitude (a b d : ℝ) (c : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator a b d c) =
      (8 / 3 : ℝ) * Complex.normSq c * |-a + b + 2*d| := by
  rw [paperEulerWoldHistoryOperator_compactIdealDistance,
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter, abs_mul, abs_mul]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 / 3),
    abs_of_nonneg (Complex.normSq_nonneg c)]

/-- The native compensated primitive-budget lane is compact as a complete depth history. -/
theorem paperEulerWoldHistoryOperator_budgeted_compact (c : ℂ) :
    IsCompactOperator (paperEulerWoldHistoryOperator 1 (-1) 1 c) := by
  rw [paperEulerWoldHistoryOperator_compact_iff]
  exact Or.inr (by ring)

/-- Its paper ideal cost vanishes at every coefficient, including nonzero ones. -/
theorem paperEulerWoldHistoryOperator_budgeted_traceCost (c : ℂ) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperEulerWoldHistoryOperator 1 (-1) 1 c) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr
    (paperEulerWoldHistoryOperator_budgeted_compact c)

/-- The endpoint survives with its entire source-computable orbit quantum. -/
theorem paperEulerWoldHistoryOperator_endpoint_gap (c : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator 0 0 1 c) =
      (16 / 3 : ℝ) * Complex.normSq c := by
  rw [paperEulerWoldHistoryOperator_essential_amplitude]
  norm_num
  ring

/-- The source-budgeted transverse history survives with exactly half the primitive budget. -/
theorem paperEulerWoldHistoryOperator_transverse_gap (c : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator (-1) (-1)
      (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c) =
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 := by
  rw [paperEulerWoldHistoryOperator_compactIdealDistance,
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget]
  apply abs_of_nonneg
  unfold sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg c))
    routePPrimitiveBaseCauchyCubicTraceBudget_pos.le) (by norm_num)

/-- Exact positive cost of replacing the endpoint history by the transverse budgeted one. -/
theorem paperEulerWoldHistoryOperator_endpoint_transverse_gap (c : ℂ) :
    compactIdealDistance (paperEulerWoldHistoryOperator 0 0 1 c -
      paperEulerWoldHistoryOperator (-1) (-1)
        (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c) =
      (16 / 3 : ℝ) * Complex.normSq c -
        sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 := by
  rw [paperEulerWoldHistoryOperator_compactIdealDistance_sub,
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget]
  have he : sourceHorizontalEulerWoldJordanConormalCofinalCharacter 0 0 1 c =
      (16 / 3 : ℝ) * Complex.normSq c := by
    unfold sourceHorizontalEulerWoldJordanConormalCofinalCharacter
    ring
  rw [he]
  apply abs_of_nonneg
  by_cases hc : c = 0
  · subst c
    simp [sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  · have hb := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc
    have hq := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum hc
    linarith

/-- Endpoint and transverse histories are compact-equivalent only at the zero source coefficient. -/
theorem paperEulerWoldHistoryOperator_endpoint_transverse_compact_iff (c : ℂ) :
    IsCompactOperator (paperEulerWoldHistoryOperator 0 0 1 c -
      paperEulerWoldHistoryOperator (-1) (-1)
        (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c) ↔ c = 0 := by
  rw [paperEulerWoldHistoryOperator_compact_sub_iff,
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget]
  have he : sourceHorizontalEulerWoldJordanConormalCofinalCharacter 0 0 1 c =
      (16 / 3 : ℝ) * Complex.normSq c := by
    unfold sourceHorizontalEulerWoldJordanConormalCofinalCharacter
    ring
  rw [he]
  by_cases hc : c = 0
  · subst c
    simp [sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  · simp only [hc, iff_false]
    have hb := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc
    have hq := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_lt_quantum hc
    linarith

/-- The paper ideal trace detects every nonzero endpoint-to-transverse replacement. -/
theorem paperEulerWoldHistoryOperator_endpoint_transverse_traceCost (c : ℂ) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperEulerWoldHistoryOperator 0 0 1 c -
        paperEulerWoldHistoryOperator (-1) (-1)
          (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c) =
      if c = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperEulerWoldHistoryOperator_endpoint_transverse_compact_iff]

/-- All actual multiplicity-split Xi coefficients inherit the same exact ideal law. -/
theorem paperEulerWoldHistoryOperator_actualXi_traceCost
    (a b d x u r : ℝ) (q : XiRightZeroCopy) :
    compactOperatorTraceCost (lp (fun _ : ℕ => ℂ) 2)
      (paperEulerWoldHistoryOperator a b d (sourceHorizontalActualXiConormalCoefficient x u q r)) =
      if sourceHorizontalActualXiConormalCoefficient x u q r = 0 ∨ -a + b + 2*d = 0
      then 0 else ∞ :=
  paperEulerWoldHistoryOperator_traceCost _ _ _ _

/-- Histories on one actual Xi support fibre agree before any compact quotient is taken. -/
theorem paperEulerWoldHistoryOperator_actualXi_eq_of_support
    (a b d x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) :
    paperEulerWoldHistoryOperator a b d (sourceHorizontalActualXiConormalCoefficient x u s r) =
      paperEulerWoldHistoryOperator a b d (sourceHorizontalActualXiConormalCoefficient x u q r) := by
  rw [sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h]

/-- Summing complete histories over the support fibre restores analytic multiplicity exactly. -/
theorem paperEulerWoldHistoryOperator_actualXi_fiber_sum
    (a b d x u r : ℝ) (q : XiRightZeroCopy) :
    (∑ s : XiRightSupportFiber q,
      paperEulerWoldHistoryOperator a b d (sourceHorizontalActualXiConormalCoefficient x u s.1 r)) =
    xiSupportMultiplicity q.1.1 •
      paperEulerWoldHistoryOperator a b d (sourceHorizontalActualXiConormalCoefficient x u q r) := by
  have he (s : XiRightSupportFiber q) :=
    paperEulerWoldHistoryOperator_actualXi_eq_of_support a b d x u r s.2
  simp only [he, Finset.sum_const, Finset.card_univ,
    routePPrimitiveGammaJuliaXiActualSupportFiber_card]

end
end RHTower
