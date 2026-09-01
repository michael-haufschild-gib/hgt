import GaloisForLFunctions.RHTower.WindowBudget

/-!
# Shifted greedy filling from Stadlmann's factor-partition lemmas

Lemmas 11--13 repeatedly enlarge an existing logarithmic mass by nonnegative smooth-prime steps
until it enters a prescribed interval.  This packages the exact finite combinatorial engine.
-/

namespace RHTower

open Finset

noncomputable section

/-- Closed input package for shifted greedy interval filling over any finite carrier. -/
structure StadlmannShiftedFillData {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (S : Finset ι) where
  stepCap : ℝ
  lower : ℝ
  upper : ℝ
  base : ℝ
  stepCap_nonneg : 0 ≤ stepCap
  width : stepCap ≤ upper - lower
  base_le_upper : base ≤ upper
  step_nonneg : ∀ i ∈ S, 0 ≤ f i
  step_le : ∀ i ∈ S, f i ≤ stepCap
  total : lower ≤ base + ∑ i ∈ S, f i

private theorem exists_subset_sum_between_finite
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ) {target step : ℝ}
    (htarget : 0 ≤ target) (hstep : 0 ≤ step)
    (hf0 : ∀ i ∈ S, 0 ≤ f i) (hfstep : ∀ i ∈ S, f i ≤ step)
    (htotal : target ≤ ∑ i ∈ S, f i) :
    ∃ J ⊆ S, target ≤ ∑ i ∈ J, f i ∧ ∑ i ∈ J, f i ≤ target + step := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at htotal
      exact ⟨∅, Finset.Subset.rfl, by simpa using htotal, by simp; linarith⟩
  | @insert i S hi ih =>
      by_cases hS : target ≤ ∑ j ∈ S, f j
      · obtain ⟨J, hJS, hlo, hhi⟩ := ih
          (fun j hj => hf0 j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfstep j (Finset.mem_insert_of_mem hj)) hS
        exact ⟨J, fun _ hj => Finset.mem_insert_of_mem (hJS hj), hlo, hhi⟩
      · refine ⟨insert i S, Finset.Subset.rfl, htotal, ?_⟩
        rw [Finset.sum_insert hi]
        have hiStep := hfstep i (Finset.mem_insert_self i S)
        linarith

/-- Shifted greedy fill used in each smooth-factor allocation stage of Lemmas 11--13. -/
theorem StadlmannShiftedFillData.exists_subset_in_interval
    {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {S : Finset ι}
    (d : StadlmannShiftedFillData f S) :
    ∃ J ⊆ S,
      d.lower ≤ d.base + ∑ i ∈ J, f i ∧
        d.base + ∑ i ∈ J, f i ≤ d.upper := by
  by_cases hbase : d.lower ≤ d.base
  · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
    · simpa using hbase
    · simpa using d.base_le_upper
  · have htarget : 0 ≤ d.lower - d.base := by linarith
    have hsum : d.lower - d.base ≤ ∑ i ∈ S, f i := by linarith [d.total]
    obtain ⟨J, hJS, hlo, hhi⟩ := exists_subset_sum_between_finite S f
      htarget d.stepCap_nonneg d.step_nonneg d.step_le hsum
    refine ⟨J, hJS, ?_, ?_⟩
    · linarith
    · linarith [d.width]


/-- Closed input package for two sequential shifted fills. -/
structure StadlmannTwoStageFillData {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (S : Finset ι) where
  stepCap : ℝ
  lowerOne : ℝ
  upperOne : ℝ
  baseOne : ℝ
  lowerTwo : ℝ
  upperTwo : ℝ
  baseTwo : ℝ
  stepCap_nonneg : 0 ≤ stepCap
  widthOne : stepCap ≤ upperOne - lowerOne
  widthTwo : stepCap ≤ upperTwo - lowerTwo
  baseOne_le_upperOne : baseOne ≤ upperOne
  baseTwo_le_upperTwo : baseTwo ≤ upperTwo
  step_nonneg : ∀ i ∈ S, 0 ≤ f i
  step_le : ∀ i ∈ S, f i ≤ stepCap
  stageTwoTotal : lowerTwo ≤ baseTwo + ∑ i ∈ S, f i
  jointTotal : lowerOne + upperTwo ≤ baseOne + baseTwo + ∑ i ∈ S, f i

/-- Two disjoint shifted interval fills, selected in the order `J₂` then `J₁`. -/
theorem StadlmannTwoStageFillData.exists_disjoint_subsets_in_intervals
    {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {S : Finset ι}
    (d : StadlmannTwoStageFillData f S) :
    ∃ J₁ J₂ : Finset ι,
      J₁ ⊆ S ∧ J₂ ⊆ S ∧ Disjoint J₁ J₂ ∧
        d.lowerOne ≤ d.baseOne + ∑ i ∈ J₁, f i ∧
        d.baseOne + ∑ i ∈ J₁, f i ≤ d.upperOne ∧
        d.lowerTwo ≤ d.baseTwo + ∑ i ∈ J₂, f i ∧
        d.baseTwo + ∑ i ∈ J₂, f i ≤ d.upperTwo := by
  let stageTwo : StadlmannShiftedFillData f S := {
    stepCap := d.stepCap
    lower := d.lowerTwo
    upper := d.upperTwo
    base := d.baseTwo
    stepCap_nonneg := d.stepCap_nonneg
    width := d.widthTwo
    base_le_upper := d.baseTwo_le_upperTwo
    step_nonneg := d.step_nonneg
    step_le := d.step_le
    total := d.stageTwoTotal
  }
  obtain ⟨J₂, hJ₂S, hJ₂lo, hJ₂hi⟩ := stageTwo.exists_subset_in_interval
  have hsplit :
      (∑ i ∈ S \ J₂, f i) + ∑ i ∈ J₂, f i = ∑ i ∈ S, f i :=
    Finset.sum_sdiff hJ₂S
  have hstageOneTotal : d.lowerOne ≤ d.baseOne + ∑ i ∈ S \ J₂, f i := by
    dsimp [stageTwo] at hJ₂hi
    linarith [d.jointTotal]
  let stageOne : StadlmannShiftedFillData f (S \ J₂) := {
    stepCap := d.stepCap
    lower := d.lowerOne
    upper := d.upperOne
    base := d.baseOne
    stepCap_nonneg := d.stepCap_nonneg
    width := d.widthOne
    base_le_upper := d.baseOne_le_upperOne
    step_nonneg := fun i hi => d.step_nonneg i (Finset.mem_sdiff.mp hi).1
    step_le := fun i hi => d.step_le i (Finset.mem_sdiff.mp hi).1
    total := hstageOneTotal
  }
  obtain ⟨J₁, hJ₁rest, hJ₁lo, hJ₁hi⟩ := stageOne.exists_subset_in_interval
  have hJ₁S : J₁ ⊆ S := hJ₁rest.trans Finset.sdiff_subset
  have hdisj : Disjoint J₁ J₂ := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    exact (Finset.mem_sdiff.mp (hJ₁rest hi₁)).2 hi₂
  dsimp [stageOne] at hJ₁lo hJ₁hi
  dsimp [stageTwo] at hJ₂lo hJ₂hi
  exact ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj,
    hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi⟩

/-- Positive product data whose logarithms satisfy the two-stage fill law. -/
structure StadlmannTwoStageProductData {ι : Type*} [DecidableEq ι]
    (Q : ι → ℝ) (S : Finset ι) where
  fill : StadlmannTwoStageFillData (fun i => Real.log (Q i)) S
  factor_pos : ∀ i ∈ S, 0 < Q i

/-- Multiplicative two-stage allocation obtained by exponentiating the additive law. -/
theorem StadlmannTwoStageProductData.exists_disjoint_subproducts_in_intervals
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι}
    (d : StadlmannTwoStageProductData Q S) :
    ∃ J₁ J₂ : Finset ι,
      J₁ ⊆ S ∧ J₂ ⊆ S ∧ Disjoint J₁ J₂ ∧
        Real.exp d.fill.lowerOne ≤
          Real.exp d.fill.baseOne * ∏ i ∈ J₁, Q i ∧
        Real.exp d.fill.baseOne * ∏ i ∈ J₁, Q i ≤
          Real.exp d.fill.upperOne ∧
        Real.exp d.fill.lowerTwo ≤
          Real.exp d.fill.baseTwo * ∏ i ∈ J₂, Q i ∧
        Real.exp d.fill.baseTwo * ∏ i ∈ J₂, Q i ≤
          Real.exp d.fill.upperTwo := by
  obtain ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi⟩ :=
    d.fill.exists_disjoint_subsets_in_intervals
  have hJ₁prodPos : 0 < ∏ i ∈ J₁, Q i :=
    Finset.prod_pos fun i hi => d.factor_pos i (hJ₁S hi)
  have hJ₂prodPos : 0 < ∏ i ∈ J₂, Q i :=
    Finset.prod_pos fun i hi => d.factor_pos i (hJ₂S hi)
  have hJ₁exp :
      Real.exp (d.fill.baseOne + ∑ i ∈ J₁, Real.log (Q i)) =
        Real.exp d.fill.baseOne * ∏ i ∈ J₁, Q i := by
    rw [Real.exp_add, ← Real.log_prod
      (fun i hi => (d.factor_pos i (hJ₁S hi)).ne'), Real.exp_log hJ₁prodPos]
  have hJ₂exp :
      Real.exp (d.fill.baseTwo + ∑ i ∈ J₂, Real.log (Q i)) =
        Real.exp d.fill.baseTwo * ∏ i ∈ J₂, Q i := by
    rw [Real.exp_add, ← Real.log_prod
      (fun i hi => (d.factor_pos i (hJ₂S hi)).ne'), Real.exp_log hJ₂prodPos]
  refine ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, ?_, ?_, ?_, ?_⟩
  · rw [← hJ₁exp]
    exact Real.exp_le_exp.mpr hJ₁lo
  · rw [← hJ₁exp]
    exact Real.exp_le_exp.mpr hJ₁hi
  · rw [← hJ₂exp]
    exact Real.exp_le_exp.mpr hJ₂lo
  · rw [← hJ₂exp]
    exact Real.exp_le_exp.mpr hJ₂hi

/-- Closed input for the divisor-inside-a-selected-factor refinement in Stadlmann Lemma 13. -/
structure StadlmannNestedRefinementData {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (S : Finset ι) where
  stepCap : ℝ
  outerLower : ℝ
  outerUpper : ℝ
  innerLower : ℝ
  innerUpper : ℝ
  base : ℝ
  stepCap_nonneg : 0 ≤ stepCap
  innerWidth : stepCap ≤ innerUpper - innerLower
  baseAtLower : base ≤ 2 * outerLower + innerUpper
  totalAtUpper : 2 * outerUpper + innerLower ≤ base + ∑ i ∈ S, f i
  step_nonneg : ∀ i ∈ S, 0 ≤ f i
  step_le : ∀ i ∈ S, f i ≤ stepCap

/-- Every outer scale in the interval has a nested subset in its translated doubled interval. -/
theorem StadlmannNestedRefinementData.exists_subset_at_every_outer_scale
    {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {S : Finset ι}
    (d : StadlmannNestedRefinementData f S) :
    ∀ c : {c : ℝ // d.outerLower ≤ c ∧ c ≤ d.outerUpper},
      ∃ J ⊆ S,
        2 * c.1 + d.innerLower ≤ d.base + ∑ i ∈ J, f i ∧
        d.base + ∑ i ∈ J, f i ≤ 2 * c.1 + d.innerUpper := by
  intro c
  let fill : StadlmannShiftedFillData f S := {
    stepCap := d.stepCap
    lower := 2 * c.1 + d.innerLower
    upper := 2 * c.1 + d.innerUpper
    base := d.base
    stepCap_nonneg := d.stepCap_nonneg
    width := by linarith [d.innerWidth]
    base_le_upper := by linarith [d.baseAtLower, c.2.1]
    step_nonneg := d.step_nonneg
    step_le := d.step_le
    total := by linarith [d.totalAtUpper, c.2.2]
  }
  simpa [fill] using fill.exists_subset_in_interval

/-- Positive product data for the nested refinement law. -/
structure StadlmannNestedProductData {ι : Type*} [DecidableEq ι]
    (Q : ι → ℝ) (S : Finset ι) where
  refinement : StadlmannNestedRefinementData (fun i => Real.log (Q i)) S
  factor_pos : ∀ i ∈ S, 0 < Q i

/-- Multiplicative nested divisor window at every outer scale. -/
theorem StadlmannNestedProductData.exists_subproduct_at_every_outer_scale
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι}
    (d : StadlmannNestedProductData Q S) :
    ∀ c : {c : ℝ // d.refinement.outerLower ≤ c ∧
        c ≤ d.refinement.outerUpper},
      ∃ J ⊆ S,
        Real.exp (2 * c.1 + d.refinement.innerLower) ≤
          Real.exp d.refinement.base * ∏ i ∈ J, Q i ∧
        Real.exp d.refinement.base * ∏ i ∈ J, Q i ≤
          Real.exp (2 * c.1 + d.refinement.innerUpper) := by
  intro c
  obtain ⟨J, hJS, hlo, hhi⟩ := d.refinement.exists_subset_at_every_outer_scale c
  have hprodPos : 0 < ∏ i ∈ J, Q i :=
    Finset.prod_pos fun i hi => d.factor_pos i (hJS hi)
  have hexp :
      Real.exp (d.refinement.base + ∑ i ∈ J, Real.log (Q i)) =
        Real.exp d.refinement.base * ∏ i ∈ J, Q i := by
    rw [Real.exp_add, ← Real.log_prod
      (fun i hi => (d.factor_pos i (hJS hi)).ne'), Real.exp_log hprodPos]
  refine ⟨J, hJS, ?_, ?_⟩
  · rw [← hexp]
    exact Real.exp_le_exp.mpr hlo
  · rw [← hexp]
    exact Real.exp_le_exp.mpr hhi

/-- Full finite input package for Stadlmann Lemma 13: two disjoint fills plus nested refinement. -/
structure StadlmannLemmaThirteenFillData {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (S : Finset ι) where
  allocation : StadlmannTwoStageFillData f S
  innerLower : ℝ
  innerUpper : ℝ
  innerBase : ℝ
  innerWidth : allocation.stepCap ≤ innerUpper - innerLower
  innerBaseAtLower : innerBase ≤ 2 * allocation.lowerOne + innerUpper
  selectedLowerAtUpper :
    2 * allocation.upperOne + innerLower + allocation.baseOne ≤
      innerBase + allocation.lowerOne

/-- Full finite combinatorial content of Lemma 13: `J₂`, disjoint `J₁`, then `J' ⊆ J₁`
for every admissible outer scale. -/
theorem StadlmannLemmaThirteenFillData.exists_disjoint_and_nested_subsets
    {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {S : Finset ι}
    (d : StadlmannLemmaThirteenFillData f S) :
    ∃ J₁ J₂ : Finset ι,
      J₁ ⊆ S ∧ J₂ ⊆ S ∧ Disjoint J₁ J₂ ∧
        d.allocation.lowerOne ≤
          d.allocation.baseOne + ∑ i ∈ J₁, f i ∧
        d.allocation.baseOne + ∑ i ∈ J₁, f i ≤
          d.allocation.upperOne ∧
        d.allocation.lowerTwo ≤
          d.allocation.baseTwo + ∑ i ∈ J₂, f i ∧
        d.allocation.baseTwo + ∑ i ∈ J₂, f i ≤
          d.allocation.upperTwo ∧
        ∀ c : {c : ℝ // d.allocation.lowerOne ≤ c ∧
            c ≤ d.allocation.upperOne},
          ∃ J' ⊆ J₁,
            2 * c.1 + d.innerLower ≤ d.innerBase + ∑ i ∈ J', f i ∧
            d.innerBase + ∑ i ∈ J', f i ≤ 2 * c.1 + d.innerUpper := by
  obtain ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi⟩ :=
    d.allocation.exists_disjoint_subsets_in_intervals
  have hnestedTotal :
      2 * d.allocation.upperOne + d.innerLower ≤
        d.innerBase + ∑ i ∈ J₁, f i := by
    linarith [d.selectedLowerAtUpper]
  let nested : StadlmannNestedRefinementData f J₁ := {
    stepCap := d.allocation.stepCap
    outerLower := d.allocation.lowerOne
    outerUpper := d.allocation.upperOne
    innerLower := d.innerLower
    innerUpper := d.innerUpper
    base := d.innerBase
    stepCap_nonneg := d.allocation.stepCap_nonneg
    innerWidth := d.innerWidth
    baseAtLower := d.innerBaseAtLower
    totalAtUpper := hnestedTotal
    step_nonneg := fun i hi => d.allocation.step_nonneg i (hJ₁S hi)
    step_le := fun i hi => d.allocation.step_le i (hJ₁S hi)
  }
  refine ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj,
    hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi, ?_⟩
  simpa [nested] using nested.exists_subset_at_every_outer_scale

/-- Positive product data for the full two-stage and nested allocation in Stadlmann Lemma 13. -/
structure StadlmannLemmaThirteenProductData {ι : Type*} [DecidableEq ι]
    (Q : ι → ℝ) (S : Finset ι) where
  fill : StadlmannLemmaThirteenFillData (fun i => Real.log (Q i)) S
  factor_pos : ∀ i ∈ S, 0 < Q i

/-- Multiplicative form of the full finite content of Stadlmann Lemma 13. -/
theorem StadlmannLemmaThirteenProductData.exists_disjoint_and_nested_subproducts
    {ι : Type*} [DecidableEq ι] {Q : ι → ℝ} {S : Finset ι}
    (d : StadlmannLemmaThirteenProductData Q S) :
    ∃ J₁ J₂ : Finset ι,
      J₁ ⊆ S ∧ J₂ ⊆ S ∧ Disjoint J₁ J₂ ∧
        Real.exp d.fill.allocation.lowerOne ≤
          Real.exp d.fill.allocation.baseOne * ∏ i ∈ J₁, Q i ∧
        Real.exp d.fill.allocation.baseOne * ∏ i ∈ J₁, Q i ≤
          Real.exp d.fill.allocation.upperOne ∧
        Real.exp d.fill.allocation.lowerTwo ≤
          Real.exp d.fill.allocation.baseTwo * ∏ i ∈ J₂, Q i ∧
        Real.exp d.fill.allocation.baseTwo * ∏ i ∈ J₂, Q i ≤
          Real.exp d.fill.allocation.upperTwo ∧
        ∀ c : {c : ℝ // d.fill.allocation.lowerOne ≤ c ∧
            c ≤ d.fill.allocation.upperOne},
          ∃ J' ⊆ J₁,
            Real.exp (2 * c.1 + d.fill.innerLower) ≤
              Real.exp d.fill.innerBase * ∏ i ∈ J', Q i ∧
            Real.exp d.fill.innerBase * ∏ i ∈ J', Q i ≤
              Real.exp (2 * c.1 + d.fill.innerUpper) := by
  obtain ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, hJ₁lo, hJ₁hi, hJ₂lo, hJ₂hi, hnested⟩ :=
    d.fill.exists_disjoint_and_nested_subsets
  have hJ₁prodPos : 0 < ∏ i ∈ J₁, Q i :=
    Finset.prod_pos fun i hi => d.factor_pos i (hJ₁S hi)
  have hJ₂prodPos : 0 < ∏ i ∈ J₂, Q i :=
    Finset.prod_pos fun i hi => d.factor_pos i (hJ₂S hi)
  have hJ₁exp :
      Real.exp (d.fill.allocation.baseOne + ∑ i ∈ J₁, Real.log (Q i)) =
        Real.exp d.fill.allocation.baseOne * ∏ i ∈ J₁, Q i := by
    rw [Real.exp_add, ← Real.log_prod
      (fun i hi => (d.factor_pos i (hJ₁S hi)).ne'), Real.exp_log hJ₁prodPos]
  have hJ₂exp :
      Real.exp (d.fill.allocation.baseTwo + ∑ i ∈ J₂, Real.log (Q i)) =
        Real.exp d.fill.allocation.baseTwo * ∏ i ∈ J₂, Q i := by
    rw [Real.exp_add, ← Real.log_prod
      (fun i hi => (d.factor_pos i (hJ₂S hi)).ne'), Real.exp_log hJ₂prodPos]
  refine ⟨J₁, J₂, hJ₁S, hJ₂S, hdisj, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hJ₁exp]
    exact Real.exp_le_exp.mpr hJ₁lo
  · rw [← hJ₁exp]
    exact Real.exp_le_exp.mpr hJ₁hi
  · rw [← hJ₂exp]
    exact Real.exp_le_exp.mpr hJ₂lo
  · rw [← hJ₂exp]
    exact Real.exp_le_exp.mpr hJ₂hi
  · intro c
    obtain ⟨J', hJ'J₁, hJ'lo, hJ'hi⟩ := hnested c
    have hJ'prodPos : 0 < ∏ i ∈ J', Q i :=
      Finset.prod_pos fun i hi => d.factor_pos i (hJ₁S (hJ'J₁ hi))
    have hJ'exp :
        Real.exp (d.fill.innerBase + ∑ i ∈ J', Real.log (Q i)) =
          Real.exp d.fill.innerBase * ∏ i ∈ J', Q i := by
      rw [Real.exp_add, ← Real.log_prod
        (fun i hi => (d.factor_pos i (hJ₁S (hJ'J₁ hi))).ne'), Real.exp_log hJ'prodPos]
    refine ⟨J', hJ'J₁, ?_, ?_⟩
    · rw [← hJ'exp]
      exact Real.exp_le_exp.mpr hJ'lo
    · rw [← hJ'exp]
      exact Real.exp_le_exp.mpr hJ'hi

end

end RHTower
