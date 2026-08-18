import GaloisForLFunctions.RHTower.SourceHorizontalEulerWoldJordanConormalCoShortAdmission

/-!
# Source-budgeted transverse Euler--Wold reporter

The admitted Euler--Wold compression defect has exact source provenance and is nonnegative, but
its cofinal character is zero.  This module couples that defect to a universal fraction of the
literal primitive Euler budget.  The resulting reporter is transverse and converges to exactly
half the source budget on every nonzero Xi conormal.

This closes existence of a source-budgeted transverse linear reporter.  A second theorem records
its sharp limitation: no linear reporter can both remain inside this source budget and dominate
the literal endpoint response cofinally.  Thus this construction does not assume or prove RH.
-/

open Complex Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- The coefficient-faithful Euler--Wold compression defect, coupled to one quarter of the
universal primitive Euler budget through the endpoint leg. -/
def sourceHorizontalEulerWoldTransverseDefectBudgetReporter
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) : ℝ :=
  sourceHorizontalEulerWoldJordanConormalLinearReporter
    (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c q N

/-- Finite source identity: the reporter is exactly post-compression Euler--Wold variation times
the literal conormal short, plus its primitive-budget-calibrated endpoint channel. -/
theorem sourceHorizontalEulerWoldTransverseDefectBudgetReporter_eq
    (c : ℂ) (q : XiRightZeroCopy) (N : ℕ) :
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N =
      sourceHorizontalEulerWoldJordanPostCompressionVariation N *
          sourceHorizontalLiteralConormalShort c +
        (routePPrimitiveBaseCauchyCubicTraceBudget / 4) *
          sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N := by
  have hvariation :
      sourceHorizontalEulerWoldJordanNegativeMass N -
          sourceHorizontalEulerWoldJordanPositiveMass N =
        sourceHorizontalEulerWoldJordanPostCompressionVariation N := by
    rw [sourceHorizontalEulerWoldJordanNegativeMass_sub_positiveMass_eq,
      sourceHorizontalEulerWoldJordanPostCompressionVariation_eq]
  rw [sourceHorizontalEulerWoldTransverseDefectBudgetReporter,
    sourceHorizontalEulerWoldJordanConormalLinearReporter,
    sourceHorizontalEulerWoldJordanConormalAdmission]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hvariation]
  ring

/-- Its cofinal character is exactly half the literal primitive source budget. -/
theorem sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget
    (c : ℂ) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter
        (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c =
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 := by
  rw [sourceHorizontalEulerWoldJordanConormalCofinalCharacter,
    sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget]
  ring

/-- The reporter converges to the midpoint of the open primitive-budget interval. -/
theorem tendsto_sourceHorizontalEulerWoldTransverseDefectBudgetReporter
    (c : ℂ) (q : XiRightZeroCopy) :
    Tendsto (sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q)
      atTop
      (nhds (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2)) := by
  have h := tendsto_sourceHorizontalEulerWoldJordanConormalLinearReporter
    (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c q
  rw [sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget] at h
  change Tendsto (fun N =>
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N) atTop
      (nhds (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2))
  simpa only [sourceHorizontalEulerWoldTransverseDefectBudgetReporter] using h

/-- On a nonzero conormal the new character is genuinely transverse to the old blind plane. -/
theorem sourceHorizontalEulerWoldTransverseDefectBudgetReporter_transverse
    {c : ℂ} (hc : c ≠ 0) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter
        (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4) c ≠ 0 := by
  rw [sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget]
  exact div_ne_zero
    (ne_of_gt (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc))
    (by norm_num)

/-- Every nonzero admitted conormal eventually has strictly positive reporter value strictly below
its literal primitive source budget. -/
theorem eventually_sourceHorizontalEulerWoldTransverseDefectBudgetReporter_between
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) :
    ∀ᶠ N : ℕ in atTop,
      0 < sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N ∧
        sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q N <
          sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c := by
  have hbudget := sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget_pos hc
  have hzero : 0 < sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 :=
    half_pos hbudget
  have hhalf : sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c / 2 <
      sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c :=
    half_lt_self hbudget
  have hlim := tendsto_sourceHorizontalEulerWoldTransverseDefectBudgetReporter c q
  filter_upwards [hlim.eventually_const_lt hzero, hlim.eventually_lt_const hhalf]
    with N hN0 hNB
  exact ⟨hN0, hNB⟩

/-- **Linear reporter firewall.** No admitted linear reporter can eventually stay below the
primitive source budget and also eventually dominate the literal endpoint response. -/
theorem not_eventually_sourceBudgeted_and_endpointDominating_linearReporter
    {c : ℂ} (hc : c ≠ 0) (q : XiRightZeroCopy) (a b d : ℝ) :
    ¬ ((∀ᶠ N : ℕ in atTop,
        sourceHorizontalEulerWoldJordanConormalLinearReporter a b d c q N ≤
          sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget c) ∧
      (∀ᶠ N : ℕ in atTop,
        sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse c q N ≤
          sourceHorizontalEulerWoldJordanConormalLinearReporter a b d c q N)) := by
  rintro ⟨hbudgeted, hdominates⟩
  have hoverspend :=
    eventually_sourceBudget_lt_sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse hc q
  obtain ⟨N, hLB, hRL, hBR⟩ :=
    (hbudgeted.and (hdominates.and hoverspend)).exists
  linarith

/-- Reporter specialized to the actual multiplicity-split completed Gamma--Julia Xi coordinate. -/
def sourceHorizontalActualXiTransverseDefectBudgetReporter
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) : ℝ :=
  sourceHorizontalEulerWoldTransverseDefectBudgetReporter
    (sourceHorizontalActualXiConormalCoefficient x u q r) q N

/-- Reporter is independent of multiplicity-copy choice inside one Xi support fibre. -/
theorem sourceHorizontalActualXiTransverseDefectBudgetReporter_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) (N : ℕ) :
    sourceHorizontalActualXiTransverseDefectBudgetReporter x u s r N =
      sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N := by
  simp only [sourceHorizontalActualXiTransverseDefectBudgetReporter,
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter,
    sourceHorizontalEulerWoldJordanConormalLinearReporter,
    sourceZeroHorizontalWoldRegularizedJuliaOrbitResponse_eq_endpointThirdJet]
  rw [sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h]

/-- Support-fibre sum restores analytic Xi multiplicity exactly. -/
theorem sourceHorizontalActualXiTransverseDefectBudgetReporter_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiTransverseDefectBudgetReporter x u s.1 r N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiTransverseDefectBudgetReporter x u s.1 r N) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalActualXiTransverseDefectBudgetReporter_eq_of_support
              x u r s.2 N
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- **Actual Xi-fibre producer.** The source-derived reporter has nonzero character, converges to
half budget, eventually lies strictly inside budget, and preserves analytic multiplicity. -/
theorem sourceHorizontalActualXiTransverseDefectBudgetReporter_producer
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0) :
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter
        (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4)
        (sourceHorizontalActualXiConormalCoefficient x u q r) =
          sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget
            (sourceHorizontalActualXiConormalCoefficient x u q r) / 2 ∧
    sourceHorizontalEulerWoldJordanConormalCofinalCharacter
        (-1) (-1) (routePPrimitiveBaseCauchyCubicTraceBudget / 4)
        (sourceHorizontalActualXiConormalCoefficient x u q r) ≠ 0 ∧
    Tendsto (sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r)
      atTop
      (nhds (sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget
        (sourceHorizontalActualXiConormalCoefficient x u q r) / 2)) ∧
    (∀ᶠ N : ℕ in atTop,
      0 < sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N ∧
        sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N <
          sourceHorizontalWoldRegularizedJuliaOrbitSourceBudget
            (sourceHorizontalActualXiConormalCoefficient x u q r)) ∧
    (∀ N : ℕ,
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiTransverseDefectBudgetReporter x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiTransverseDefectBudgetReporter x u q r N) := by
  have hc := sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  exact ⟨
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter_character_eq_half_budget _,
    sourceHorizontalEulerWoldTransverseDefectBudgetReporter_transverse hc,
    tendsto_sourceHorizontalEulerWoldTransverseDefectBudgetReporter _ q,
    eventually_sourceHorizontalEulerWoldTransverseDefectBudgetReporter_between hc q,
    fun N => sourceHorizontalActualXiTransverseDefectBudgetReporter_fiber_sum x u q r N⟩

end

end RHTower
