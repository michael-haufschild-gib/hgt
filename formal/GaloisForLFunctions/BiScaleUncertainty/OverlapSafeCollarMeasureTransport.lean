import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Left collar substitution for a nonnegative extended density. No integrability
or measurability assumption on the density is needed. -/
theorem lintegral_collar_left (F : ℝ → ℝ≥0∞) (t δ : ℝ) :
    (∫⁻ y in Ioo 0 δ, F (t - y)) = ∫⁻ x in Ioo (t - δ) t, F x := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have heq : (Ioo 0 δ).indicator (fun y => F (t - y)) =
      fun y => (Ioo (t - δ) t).indicator F (t - y) := by
    funext y
    have hm : t - y ∈ Ioo (t - δ) t ↔ y ∈ Ioo 0 δ := by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hm]
  rw [heq, lintegral_sub_left_eq_self]

/-- Right collar substitution for a nonnegative extended density. -/
theorem lintegral_collar_right (F : ℝ → ℝ≥0∞) (t δ : ℝ) :
    (∫⁻ y in Ioo 0 δ, F (t + y)) = ∫⁻ x in Ioo t (t + δ), F x := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have heq : (Ioo 0 δ).indicator (fun y => F (t + y)) =
      fun y => (Ioo t (t + δ)).indicator F (t + y) := by
    funext y
    have hm : t + y ∈ Ioo t (t + δ) ↔ y ∈ Ioo 0 δ := by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hm]
  rw [heq, lintegral_add_left_eq_self]

/-- Both collar signs recover the full physical collar, including infinite
energy. The omitted centre is a Lebesgue null set. -/
theorem lintegral_collar_both (F : ℝ → ℝ≥0∞) (t δ : ℝ) :
    (∫⁻ y in Ioo 0 δ, F (t - y)) + (∫⁻ y in Ioo 0 δ, F (t + y)) =
      ∫⁻ x in Ioo (t - δ) (t + δ), F x := by
  rw [lintegral_collar_left, lintegral_collar_right]
  have hd : Disjoint (Ioo (t - δ) t) (Ioo t (t + δ)) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2.le) hy.1
  rw [← lintegral_union measurableSet_Ioo hd]
  apply setLIntegral_congr
  filter_upwards [volume.ae_ne t] with x hxt
  apply propext
  change ((t - δ < x ∧ x < t) ∨ (t < x ∧ x < t + δ)) ↔
    (t - δ < x ∧ x < t + δ)
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rcases lt_or_gt_of_ne hxt with hlt | hgt
    · exact Or.inl ⟨h1, hlt⟩
    · exact Or.inr ⟨hgt, h2⟩

variable {ι : Type*}

/-- Number of active physical collars, represented as a real number. -/
def collarMultiplicity (s : Finset ι) (E : ι → Set ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ s, (E i).indicator (fun _ => (1 : ℝ)) x

/-- Equal-multiplicity physical share; outside every collar all shares are zero. -/
def collarPhysicalShare (s : Finset ι) (E : ι → Set ℝ) (i : ι) (x : ℝ) : ℝ :=
  (E i).indicator (fun _ => (1 : ℝ)) x / collarMultiplicity s E x

/-- Equal-multiplicity collar shares spend exactly one unit at each covered
physical point and zero outside the union, for any finite family of sets. -/
theorem collarPhysicalShare_partition (s : Finset ι) (E : ι → Set ℝ) (x : ℝ) :
    (∑ i ∈ s, collarPhysicalShare s E i x) =
      (⋃ i ∈ s, E i).indicator (fun _ => (1 : ℝ)) x := by
  classical
  have hn (i : ι) : 0 ≤ (E i).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ E i <;> simp [hx]
  simp only [collarPhysicalShare, ← Finset.sum_div]
  change collarMultiplicity s E x / collarMultiplicity s E x = _
  by_cases hx : x ∈ ⋃ i ∈ s, E i
  · obtain ⟨i, hi, hxi⟩ : ∃ i ∈ s, x ∈ E i := by simpa using hx
    have hi_le := Finset.single_le_sum (fun j (_ : j ∈ s) => hn j) hi
    have hpos : 0 < collarMultiplicity s E x := by
      exact lt_of_lt_of_le
        (show (0 : ℝ) < (E i).indicator (fun _ => (1 : ℝ)) x by simp [hxi]) hi_le
    rw [div_self hpos.ne', indicator_of_mem hx]
  · have hz : collarMultiplicity s E x = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hxi : x ∉ E i := by
        intro hxi
        exact hx (by simp only [mem_iUnion]; exact ⟨i, hi, hxi⟩)
      exact indicator_of_notMem hxi _
    rw [hz, zero_div, indicator_of_notMem hx]

/-- Physical shares are nonnegative for every finite collar family. -/
theorem collarPhysicalShare_nonneg (s : Finset ι) (E : ι → Set ℝ) (i : ι) (x : ℝ) :
    0 ≤ collarPhysicalShare s E i x := by
  have hn (j : ι) : 0 ≤ (E j).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ E j <;> simp [hx]
  exact div_nonneg (hn i) (Finset.sum_nonneg fun j _ => hn j)

/-- Physical shares never overspend the density, even on overlapping collars. -/
theorem collarPhysicalShare_capacity (s : Finset ι) (E : ι → Set ℝ) (x : ℝ) :
    (∑ i ∈ s, collarPhysicalShare s E i x) ≤ 1 := by
  rw [collarPhysicalShare_partition]
  by_cases hx : x ∈ ⋃ i ∈ s, E i <;> simp [hx]

/-- A collar clipped to the finite physical interval. -/
def truncatedPhysicalCollar (t δ L : ℝ) : Set ℝ :=
  Ioo (t - δ) (t + δ) ∩ Ioo 0 L

/-- For every nonnegative extended density, multiplicity-normalized overlapping
collars recover exactly its measure on their union. No finite-energy premise is needed. -/
theorem lintegral_collarPhysicalShare_partition (s : Finset ι) (t : ι → ℝ)
    (δ L : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ x, ∑ i ∈ s, ENNReal.ofReal
      (collarPhysicalShare s (fun j => truncatedPhysicalCollar (t j) δ L) i x) * F x) =
      ∫⁻ x in ⋃ i ∈ s, truncatedPhysicalCollar (t i) δ L, F x := by
  classical
  let E := fun j => truncatedPhysicalCollar (t j) δ L
  have hE (i : ι) : MeasurableSet (E i) := measurableSet_Ioo.inter measurableSet_Ioo
  have hU : MeasurableSet (⋃ i ∈ s, E i) := s.measurableSet_biUnion (fun i _ => hE i)
  rw [← lintegral_indicator hU]
  apply lintegral_congr
  intro x
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun i (_ : i ∈ s) => collarPhysicalShare_nonneg s E i x),
    collarPhysicalShare_partition]
  by_cases hx : x ∈ ⋃ i ∈ s, E i <;> simp [hx]

/-- The physical density assigned to one truncated collar. -/
def allocatedCollarDensity (s : Finset ι) (t : ι → ℝ) (δ L : ℝ)
    (F : ℝ → ℝ≥0∞) (i : ι) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (collarPhysicalShare s
    (fun j => truncatedPhysicalCollar (t j) δ L) i x) * F x

/-- Measurable physical sets give measurable multiplicity-normalized shares. -/
theorem measurable_collarPhysicalShare (s : Finset ι) (E : ι → Set ℝ)
    (hE : ∀ j, MeasurableSet (E j)) (i : ι) :
    Measurable (collarPhysicalShare s E i) := by
  have hM : Measurable (collarMultiplicity s E) :=
    s.measurable_sum (fun j _ => measurable_const.indicator (hE j))
  exact (measurable_const.indicator (hE i)).div hM

/-- Measurability of each allocated physical density. -/
theorem measurable_allocatedCollarDensity (s : Finset ι) (t : ι → ℝ) (δ L : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (i : ι) :
    Measurable (allocatedCollarDensity s t δ L F i) := by
  have hE (j : ι) : MeasurableSet (truncatedPhysicalCollar (t j) δ L) :=
    measurableSet_Ioo.inter measurableSet_Ioo
  exact ((measurable_collarPhysicalShare s _ hE i).ennreal_ofReal).mul hF

private theorem allocatedCollarDensity_collar_indicator (s : Finset ι) (t : ι → ℝ)
    (δ L : ℝ) (F : ℝ → ℝ≥0∞) (i : ι) :
    (Ioo (t i - δ) (t i + δ)).indicator (allocatedCollarDensity s t δ L F i) =
      allocatedCollarDensity s t δ L F i := by
  funext x
  by_cases hx : x ∈ Ioo (t i - δ) (t i + δ)
  · exact indicator_of_mem hx _
  · have hE : x ∉ truncatedPhysicalCollar (t i) δ L := fun h => hx h.1
    simp [hx, allocatedCollarDensity, collarPhysicalShare, hE]

/-- Both affine branches, summed over overlapping collars, spend exactly the
physical density on their union after multiplicity normalization. -/
theorem normalized_collar_measure_transport (s : Finset ι) (t : ι → ℝ) (δ L : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∑ i ∈ s,
      ((∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L F i (t i - y)) +
       (∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L F i (t i + y)))) =
      ∫⁻ x in ⋃ i ∈ s, truncatedPhysicalCollar (t i) δ L, F x := by
  have hterm (i : ι) :
      ((∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L F i (t i - y)) +
       (∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L F i (t i + y))) =
       ∫⁻ x, allocatedCollarDensity s t δ L F i x := by
    rw [lintegral_collar_both, ← lintegral_indicator measurableSet_Ioo,
      allocatedCollarDensity_collar_indicator]
  simp_rw [hterm]
  rw [← lintegral_finsetSum s (fun i _ => measurable_allocatedCollarDensity s t δ L F hF i)]
  exact lintegral_collarPhysicalShare_partition s t δ L F

/-- The nonnegative archimedean increment density of a continuous real kernel.
It remains meaningful when its integral is infinite. -/
def continuousArchIncrementDensity (h : C(ℝ, ℝ)) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((h 0 - h x) * (Real.exp (x / 2) / Real.sinh x))

/-- The extended increment density is measurable even when its integral is infinite. -/
theorem measurable_continuousArchIncrementDensity (h : C(ℝ, ℝ)) :
    Measurable (continuousArchIncrementDensity h) :=
  ((measurable_const.sub h.continuous.measurable).mul
    ((Real.continuous_exp.measurable.comp (measurable_id.div_const 2)).div
      Real.continuous_sinh.measurable)).ennreal_ofReal

/-- Exact archimedean transport on truncated overlapping collars. Measurability
is discharged from continuity of the kernel; no integrability premise is assumed. -/
theorem archimedean_collar_measure_transport (s : Finset ι) (t : ι → ℝ)
    (δ L : ℝ) (h : C(ℝ, ℝ)) :
    (∑ i ∈ s,
      ((∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L
        (continuousArchIncrementDensity h) i (t i - y)) +
       (∫⁻ y in Ioo 0 δ, allocatedCollarDensity s t δ L
        (continuousArchIncrementDensity h) i (t i + y)))) =
      ∫⁻ x in ⋃ i ∈ s, truncatedPhysicalCollar (t i) δ L,
        continuousArchIncrementDensity h x := by
  apply normalized_collar_measure_transport
  exact ((measurable_const.sub h.continuous.measurable).mul
    ((Real.continuous_exp.measurable.comp (measurable_id.div_const 2)).div
      Real.continuous_sinh.measurable)).ennreal_ofReal

end
end GaloisForLFunctions.BiScaleUncertainty
