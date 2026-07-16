import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Finite probability Gini layer-cake identity

For a finite probability vector `p` on nonnegative heights `h`, the integral of the lower-cut
mass times its complementary mass is half the pairwise mean absolute height difference.  The
strict lower-cut convention changes only finitely many threshold values and makes the interval
decomposition exact on half-open intervals.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace HTGeometry

noncomputable section

/-- Mass below the strict height cut `t` in a finite weighted packet. -/
def finiteStrictLowerCutMass {α : Type*} [Fintype α]
    (p h : α → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if h i < t then p i else 0

private def finiteStrictLowerCutCrossMass {α : Type*} [Fintype α]
    (p h : α → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, if h i < t ∧ t ≤ h j then p i * p j else 0

private theorem one_sub_finiteStrictLowerCutMass_eq
    {α : Type*} [Fintype α] {p h : α → ℝ}
    (hp : ∑ i, p i = 1) (t : ℝ) :
    1 - finiteStrictLowerCutMass p h t =
      ∑ i, if t ≤ h i then p i else 0 := by
  rw [← hp]
  unfold finiteStrictLowerCutMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : h i < t
  · simp [hit, not_le.mpr hit]
  · simp [hit, le_of_not_gt hit]

private theorem finiteStrictLowerCutCrossMass_eq_mul_one_sub
    {α : Type*} [Fintype α] {p h : α → ℝ}
    (hp : ∑ i, p i = 1) (t : ℝ) :
    finiteStrictLowerCutCrossMass p h t =
      finiteStrictLowerCutMass p h t *
        (1 - finiteStrictLowerCutMass p h t) := by
  rw [one_sub_finiteStrictLowerCutMass_eq hp]
  unfold finiteStrictLowerCutCrossMass finiteStrictLowerCutMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hit : h i < t <;> by_cases hjt : t ≤ h j <;>
    simp [hit, hjt]

private theorem integrableOn_Ioi_indicator_Ioc_const {a b c : ℝ} :
    IntegrableOn (fun t : ℝ => if a < t ∧ t ≤ b then c else 0) (Ioi 0) := by
  rw [show (fun t : ℝ => if a < t ∧ t ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext t
    simp [indicator, mem_Ioc]]
  exact ((integrableOn_const (by simp [Real.volume_Ioc]) :
    IntegrableOn (fun _ : ℝ => c) (Ioc a b))).integrable_indicator
      measurableSet_Ioc |>.integrableOn

private theorem integral_Ioi_indicator_Ioc_const {a b c : ℝ} (ha : 0 ≤ a) :
    (∫ t : ℝ in Ioi 0, if a < t ∧ t ≤ b then c else 0) =
      c * max (b - a) 0 := by
  rw [show (fun t : ℝ => if a < t ∧ t ≤ b then c else 0) =
      (Ioc a b).indicator (fun _ => c) by
    funext t
    simp [indicator, mem_Ioc]]
  rw [setIntegral_indicator measurableSet_Ioc]
  have hinter : Ioi 0 ∩ Ioc a b = Ioc a b := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun ht => ht.2
    · exact fun ht => ⟨ha.trans_lt ht.1, ht⟩
  rw [hinter, setIntegral_const]
  unfold Measure.real
  rw [Real.volume_Ioc, ENNReal.toReal_ofReal']
  ring

private theorem integral_Ioi_finiteStrictLowerCutCrossMass
    {α : Type*} [Fintype α] {p h : α → ℝ}
    (hh : ∀ i, 0 ≤ h i) :
    (∫ t : ℝ in Ioi 0, finiteStrictLowerCutCrossMass p h t) =
      ∑ i, ∑ j, p i * p j * max (h j - h i) 0 := by
  unfold finiteStrictLowerCutCrossMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_Ioi_indicator_Ioc_const (hh i)]
    · intro j _
      exact integrableOn_Ioi_indicator_Ioc_const
  · intro i _
    exact integrable_finsetSum Finset.univ (fun _ _ =>
      integrableOn_Ioi_indicator_Ioc_const)

private theorem two_mul_sum_max_sub_eq_sum_abs_sub
    {α : Type*} [Fintype α] (p h : α → ℝ) :
    2 * (∑ i, ∑ j, p i * p j * max (h j - h i) 0) =
      ∑ i, ∑ j, p i * p j * |h i - h j| := by
  have hswap :
      (∑ i, ∑ j, p i * p j * max (h i - h j) 0) =
        ∑ i, ∑ j, p i * p j * max (h j - h i) 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    2 * (∑ i, ∑ j, p i * p j * max (h j - h i) 0) =
        (∑ i, ∑ j, p i * p j * max (h j - h i) 0) +
          ∑ i, ∑ j, p i * p j * max (h j - h i) 0 := by ring
    _ = (∑ i, ∑ j, p i * p j * max (h j - h i) 0) +
          ∑ i, ∑ j, p i * p j * max (h i - h j) 0 := by rw [hswap]
    _ = ∑ i, ∑ j,
          (p i * p j * max (h j - h i) 0 +
            p i * p j * max (h i - h j) 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_add_distrib]
    _ = ∑ i, ∑ j, p i * p j * |h i - h j| := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      have habs : max (h j - h i) 0 + max (h i - h j) 0 =
          |h i - h j| := by
        rcases le_total (h i) (h j) with hij | hji
        · rw [max_eq_left (sub_nonneg.mpr hij),
            max_eq_right (sub_nonpos.mpr hij),
            abs_of_nonpos (sub_nonpos.mpr hij)]
          ring
        · rw [max_eq_right (sub_nonpos.mpr hji),
            max_eq_left (sub_nonneg.mpr hji),
            abs_of_nonneg (sub_nonneg.mpr hji)]
          ring
      rw [← mul_add, habs]

/-- Finite layer-cake/Gini identity: the integral of the strict lower-cut mass times its
complement is half the pairwise mean absolute height difference. -/
theorem integral_Ioi_finiteStrictLowerCutMass_mul_one_sub
    {α : Type*} [Fintype α] {p h : α → ℝ}
    (hp : ∑ i, p i = 1) (hh : ∀ i, 0 ≤ h i) :
    (∫ t : ℝ in Ioi 0,
      finiteStrictLowerCutMass p h t *
        (1 - finiteStrictLowerCutMass p h t)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * |h i - h j| := by
  have hfun : (fun t : ℝ =>
      finiteStrictLowerCutMass p h t *
        (1 - finiteStrictLowerCutMass p h t)) =
      finiteStrictLowerCutCrossMass p h := by
    funext t
    exact (finiteStrictLowerCutCrossMass_eq_mul_one_sub hp t).symm
  rw [hfun, integral_Ioi_finiteStrictLowerCutCrossMass hh]
  have hsymm := two_mul_sum_max_sub_eq_sum_abs_sub p h
  linarith

end

end HTGeometry
