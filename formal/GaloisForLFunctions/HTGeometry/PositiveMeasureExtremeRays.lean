import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Extreme rays of the cone of finite positive measures

A nonzero finite measure spans an extreme ray of the positive cone exactly when it is a point mass.
The forward direction is the only substantive one: extremality forces every measurable set to carry
either no mass or the total mass, and a two-valued measure on a Hausdorff second-countable space has
a one-point support, because two distinct support points would carry disjoint open sets of full
mass.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal NNReal

/-- A measure spans an extreme ray of the cone of positive measures when it is nonzero and every
measure it dominates is one of its nonnegative multiples. -/
def IsExtremeRayMeasure {X : Type*} [MeasurableSpace X] (mu : Measure X) : Prop :=
  mu ≠ 0 ∧ ∀ nu : Measure X, nu ≤ mu → ∃ c : ℝ≥0∞, nu = c • mu

section

variable {X : Type*} [MeasurableSpace X]

/-- A measure vanishing off a point is the corresponding multiple of the Dirac mass there. -/
theorem eq_smul_dirac_of_compl_singleton_null (mu : Measure X) {y : X}
    (h : mu {y}ᶜ = 0) : mu = mu {y} • Measure.dirac y := by
  ext A hA
  have hsplit : mu A = mu (A ∩ {y}) := by
    have hle : mu A ≤ mu (A ∩ {y}) + mu (A \ {y}) := by
      have hcover : A ⊆ (A ∩ {y}) ∪ (A \ {y}) := by
        intro x hx
        by_cases hxy : x = y
        · exact Or.inl ⟨hx, hxy⟩
        · exact Or.inr ⟨hx, hxy⟩
      exact (measure_mono hcover).trans (measure_union_le _ _)
    have hdiff : mu (A \ {y}) = 0 :=
      measure_mono_null (fun x hx => hx.2) h
    have hge : mu (A ∩ {y}) ≤ mu A := measure_mono Set.inter_subset_left
    rw [hdiff, add_zero] at hle
    exact le_antisymm hle hge
  by_cases hy : y ∈ A
  · have h1 : A ∩ {y} = {y} := by
      ext x
      constructor
      · rintro ⟨-, hx⟩
        exact hx
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        exact ⟨hx ▸ hy, hx⟩
    rw [hsplit, h1, Measure.smul_apply, Measure.dirac_apply' _ hA,
      Set.indicator_of_mem hy]
    simp
  · have h1 : A ∩ {y} = ∅ := by
      ext x
      constructor
      · rintro ⟨hxA, hx⟩
        rw [Set.mem_singleton_iff] at hx
        exact absurd (hx ▸ hxA) hy
      · intro hx
        exact absurd hx (Set.notMem_empty x)
    rw [hsplit, h1, measure_empty, Measure.smul_apply, Measure.dirac_apply' _ hA,
      Set.indicator_of_notMem hy]
    simp

/-- **Point masses are extreme.** -/
theorem isExtremeRayMeasure_smul_dirac [MeasurableSingletonClass X] {c : ℝ≥0∞} (hc : c ≠ 0)
    (hc' : c ≠ ⊤) (y : X) :
    IsExtremeRayMeasure (c • Measure.dirac y) := by
  constructor
  · intro h
    have := congrArg (fun m : Measure X => m {y}) h
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton y),
      Measure.coe_zero, Pi.zero_apply, smul_eq_mul, mul_one] at this
    exact hc this
  · intro nu hnu
    have hnull : nu {y}ᶜ = 0 := by
      have hle := hnu {y}ᶜ
      have : (c • Measure.dirac y) {y}ᶜ = 0 := by
        simp [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton y).compl]
      rw [this] at hle
      simpa using hle
    refine ⟨nu {y} / c, ?_⟩
    rw [smul_smul, ENNReal.div_mul_cancel hc hc']
    exact eq_smul_dirac_of_compl_singleton_null nu hnull

/-- Extremality forces a two-valued measure: every measurable set carries either no mass or the
whole mass. -/
theorem measure_eq_zero_or_eq_univ_of_isExtremeRayMeasure {mu : Measure X} [IsFiniteMeasure mu]
    (hex : IsExtremeRayMeasure mu) {S : Set X} (hS : MeasurableSet S) :
    mu S = 0 ∨ mu S = mu univ := by
  obtain ⟨-, hray⟩ := hex
  obtain ⟨c, hc⟩ := hray (mu.restrict S) (Measure.restrict_le_self)
  by_cases hzero : mu S = 0
  · exact Or.inl hzero
  · right
    have hSS : mu S = c * mu S := by
      have := congrArg (fun m : Measure X => m S) hc
      simpa [Measure.restrict_apply hS, Set.inter_self] using this
    have hSuniv : mu S = c * mu univ := by
      have := congrArg (fun m : Measure X => m univ) hc
      simpa [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using this
    have hc1 : c = 1 := by
      have hfin : mu S ≠ ⊤ := measure_ne_top mu S
      have hone : (1 : ℝ≥0∞) * mu S = c * mu S := by rw [one_mul]; exact hSS
      exact ((ENNReal.mul_left_inj hzero hfin).1 hone).symm
    rw [hSuniv, hc1, one_mul]

end

section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- **The extreme rays of the cone of finite positive measures are the point masses.** -/
theorem exists_smul_dirac_of_isExtremeRayMeasure {mu : Measure X} [IsFiniteMeasure mu]
    (hex : IsExtremeRayMeasure mu) :
    ∃ (y : X) (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ⊤ ∧ mu = c • Measure.dirac y := by
  have hne : mu ≠ 0 := hex.1
  obtain ⟨y, hy⟩ := Measure.nonempty_support hne
  have hsingle : mu.support = {y} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.2 hy)
    by_contra hzy
    rw [Set.mem_singleton_iff] at hzy
    obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := t2_separation (Ne.symm hzy)
    have hUpos : 0 < mu U := (Measure.mem_support_iff_forall y).1 hy U (hU.mem_nhds hyU)
    have hVpos : 0 < mu V := (Measure.mem_support_iff_forall z).1 hz V (hV.mem_nhds hzV)
    have hUfull : mu U = mu univ :=
      (measure_eq_zero_or_eq_univ_of_isExtremeRayMeasure hex hU.measurableSet).resolve_left
        (ne_of_gt hUpos)
    have hVfull : mu V = mu univ :=
      (measure_eq_zero_or_eq_univ_of_isExtremeRayMeasure hex hV.measurableSet).resolve_left
        (ne_of_gt hVpos)
    have hadd : mu (U ∪ V) = mu U + mu V :=
      measure_union hUV hV.measurableSet
    have hle : mu (U ∪ V) ≤ mu univ := measure_mono (Set.subset_univ _)
    rw [hadd, hUfull, hVfull] at hle
    have hpos : 0 < mu univ := lt_of_lt_of_le hUpos (measure_mono (Set.subset_univ _))
    have hfin : mu univ ≠ ⊤ := measure_ne_top mu univ
    have : mu univ + mu univ ≤ mu univ + 0 := by simpa using hle
    exact absurd (ENNReal.le_of_add_le_add_left hfin this) (not_le.2 hpos)
  have hnull : mu {y}ᶜ = 0 := by
    rw [← hsingle]
    exact Measure.measure_compl_support (μ := mu)
  refine ⟨y, mu {y}, ?_, measure_ne_top mu _, eq_smul_dirac_of_compl_singleton_null mu hnull⟩
  intro hzero
  apply hne
  have := eq_smul_dirac_of_compl_singleton_null mu hnull
  rw [hzero, zero_smul] at this
  exact this

/-- **Classification of extreme rays.**  A finite measure spans an extreme ray of the positive cone
if and only if it is a nonzero finite multiple of a point mass. -/
theorem isExtremeRayMeasure_iff_smul_dirac [MeasurableSingletonClass X] {mu : Measure X}
    [IsFiniteMeasure mu] :
    IsExtremeRayMeasure mu ↔
      ∃ (y : X) (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ⊤ ∧ mu = c • Measure.dirac y := by
  constructor
  · exact exists_smul_dirac_of_isExtremeRayMeasure
  · rintro ⟨y, c, hc, hc', rfl⟩
    exact isExtremeRayMeasure_smul_dirac hc hc' y

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal NNReal

/-- **A two-valued probability measure is a point mass.**  On a Hausdorff second-countable space a
probability measure taking only the values `0` and `1` is the Dirac mass at the unique point of its
support. -/
theorem exists_eq_dirac_of_measure_eq_zero_or_one {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [MeasurableSingletonClass X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (h01 : ∀ S : Set X, MeasurableSet S → mu S = 0 ∨ mu S = 1) :
    ∃ y : X, mu = Measure.dirac y := by
  have hne : mu ≠ 0 := by
    intro h
    have := congrArg (fun m : Measure X => m univ) h
    simp [measure_univ] at this
  obtain ⟨y, hy⟩ := Measure.nonempty_support hne
  have hsingle : mu.support = {y} := by
    refine Set.Subset.antisymm (fun z hz => ?_) (Set.singleton_subset_iff.2 hy)
    by_contra hzy
    rw [Set.mem_singleton_iff] at hzy
    obtain ⟨U, V, hU, hV, hyU, hzV, hUV⟩ := t2_separation (Ne.symm hzy)
    have hUpos : 0 < mu U := (Measure.mem_support_iff_forall y).1 hy U (hU.mem_nhds hyU)
    have hVpos : 0 < mu V := (Measure.mem_support_iff_forall z).1 hz V (hV.mem_nhds hzV)
    have hUfull : mu U = 1 := (h01 U hU.measurableSet).resolve_left (ne_of_gt hUpos)
    have hVfull : mu V = 1 := (h01 V hV.measurableSet).resolve_left (ne_of_gt hVpos)
    have hadd : mu (U ∪ V) = mu U + mu V := measure_union hUV hV.measurableSet
    have hle : mu (U ∪ V) ≤ 1 := by
      have hmono : mu (U ∪ V) ≤ mu univ := measure_mono (subset_univ (U ∪ V))
      rwa [measure_univ] at hmono
    rw [hadd, hUfull, hVfull] at hle
    have : (2 : ℝ≥0∞) ≤ 1 := by
      calc (2 : ℝ≥0∞) = 1 + 1 := by norm_num
        _ ≤ 1 := hle
    norm_num at this
  have hnull : mu {y}ᶜ = 0 := by
    rw [← hsingle]
    exact Measure.measure_compl_support (μ := mu)
  refine ⟨y, ?_⟩
  have hmass : mu {y} = 1 := by
    have hcompl : mu {y} + mu {y}ᶜ = mu univ :=
      measure_add_measure_compl (measurableSet_singleton y)
    rw [hnull, add_zero, measure_univ] at hcompl
    exact hcompl
  have := eq_smul_dirac_of_compl_singleton_null mu hnull
  rw [hmass, one_smul] at this
  exact this

end GaloisForLFunctions.HTGeometry
