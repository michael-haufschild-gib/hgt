import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import GaloisForLFunctions.HTGeometry.ChronometricCausalSusceptibility

/-!
# Degenerate clock gradients are an exact boundary of the conservation budget

The clock-coframe conservation law assumes the scalar clock gradients define a linear equivalence
from adaptive source coefficients to conservation defects. This file proves that assumption sharp
in both of its halves.

* **Surjectivity is exactly absorbability.** Every conservation defect can be cancelled by some
  adaptive clock source precisely when the gradient map is surjective, that is, precisely when the
  clock gradients span the defect module. When they do not, an explicit defect survives every
  adaptive source.
* **Injectivity is exactly uniqueness.** The absorbing source is unique precisely when the gradient
  map is injective, that is, precisely when the clock gradients are linearly independent. When they
  are not, the same defect is cancelled by many sources and the source is not a datum.

In particular fewer clocks than the dimension of the defect module leaves a defect no adaptive
source can absorb, so degeneracy is an operational boundary and not a removable technicality.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

section Degeneracy

variable {R : Type u} {Clock : Type v} {Curv : Type w}
  [Ring R] [AddCommGroup Clock] [Module R Clock] [AddCommGroup Curv] [Module R Curv]

/-- A conservation defect is absorbable when some adaptive clock source cancels it exactly. -/
def AbsorbsDefect (clockMap : Clock →ₗ[R] Curv) (defect : Curv) : Prop :=
  ∃ source : Clock, defect + clockMap source = 0

theorem absorbsDefect_iff_mem_range (clockMap : Clock →ₗ[R] Curv) (defect : Curv) :
    AbsorbsDefect clockMap defect ↔ defect ∈ LinearMap.range clockMap := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_left ha
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    rw [map_neg, ha, add_neg_cancel]

/-- **Absorbing every conservation defect is exactly surjectivity of the clock gradient map.** -/
theorem forall_absorbsDefect_iff_surjective (clockMap : Clock →ₗ[R] Curv) :
    (∀ defect : Curv, AbsorbsDefect clockMap defect) ↔ Function.Surjective clockMap := by
  simp only [absorbsDefect_iff_mem_range]
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h
    exact Submodule.eq_top_iff'.mpr h
  · intro h d
    rw [h]
    trivial

/-- **Uniqueness of the absorbing source is exactly injectivity of the clock gradient map.** -/
theorem absorbing_source_unique_iff_injective (clockMap : Clock →ₗ[R] Curv) :
    (∀ (defect : Curv) (a a' : Clock),
        defect + clockMap a = 0 → defect + clockMap a' = 0 → a = a') ↔
      Function.Injective clockMap := by
  constructor
  · intro h x y hxy
    refine h (-clockMap x) x y (by rw [neg_add_cancel]) ?_
    rw [← hxy, neg_add_cancel]
  · intro hinj d a a' ha ha'
    exact hinj (add_left_cancel (ha.trans ha'.symm))

/-- Many absorbing sources exist as soon as the clock gradients are degenerate. -/
theorem exists_two_absorbing_sources_of_not_injective
    {clockMap : Clock →ₗ[R] Curv} (hnot : ¬ Function.Injective clockMap)
    {defect : Curv} (habs : AbsorbsDefect clockMap defect) :
    ∃ a a' : Clock, a ≠ a' ∧ defect + clockMap a = 0 ∧ defect + clockMap a' = 0 := by
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  obtain ⟨a, ha⟩ := habs
  refine ⟨a, a + (x - y), ?_, ha, ?_⟩
  · intro hEq
    have hzero : x - y = 0 := by
      have := hEq
      simpa using this.symm
    exact hne (sub_eq_zero.mp hzero)
  · have hker : clockMap (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    rw [map_add, hker, add_zero]
    exact ha

/-! ### Gradient families -/

variable {ι : Type*}

/-- The adaptive-source map of a family of scalar clock gradients. -/
noncomputable def clockGradientMap (grad : ι → Curv) : (ι →₀ R) →ₗ[R] Curv :=
  Finsupp.linearCombination R grad

/-- **Every defect is absorbable exactly when the clock gradients span the defect module.** -/
theorem forall_absorbsDefect_iff_span_eq_top (grad : ι → Curv) :
    (∀ defect : Curv, AbsorbsDefect (clockGradientMap (R := R) grad) defect) ↔
      Submodule.span R (Set.range grad) = ⊤ := by
  simp only [absorbsDefect_iff_mem_range, clockGradientMap, Finsupp.range_linearCombination]
  constructor
  · intro h
    exact Submodule.eq_top_iff'.mpr h
  · intro h d
    rw [h]
    trivial

/-- **The absorbing source is unique exactly when the clock gradients are independent.** -/
theorem absorbing_source_unique_iff_linearIndependent (grad : ι → Curv) :
    (∀ (defect : Curv) (a a' : ι →₀ R),
        defect + clockGradientMap (R := R) grad a = 0 →
          defect + clockGradientMap (R := R) grad a' = 0 → a = a') ↔
      LinearIndependent R grad := by
  rw [absorbing_source_unique_iff_injective, clockGradientMap,
    linearIndependent_iff_injective_finsuppLinearCombination]

end Degeneracy

/-! ### Too few clocks leave an unabsorbable defect -/

section Dimension

variable {K : Type u} {Clock : Type v} {Curv : Type w} [Field K]
  [AddCommGroup Clock] [Module K Clock] [AddCommGroup Curv] [Module K Curv]

open Module

/-- **Fewer clock channels than defect dimensions leaves a defect no adaptive source absorbs.** -/
theorem exists_unabsorbable_defect_of_finrank_lt [FiniteDimensional K Clock]
    (clockMap : Clock →ₗ[K] Curv) (hdim : finrank K Clock < finrank K Curv) :
    ∃ defect : Curv, ¬ AbsorbsDefect clockMap defect := by
  by_contra hall
  have hall' : ∀ defect : Curv, AbsorbsDefect clockMap defect := by
    intro d
    by_contra hd
    exact hall ⟨d, hd⟩
  have hsurj := (forall_absorbsDefect_iff_surjective clockMap).1 hall'
  have hrange : LinearMap.range clockMap = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hle := LinearMap.finrank_range_le clockMap
  rw [hrange, finrank_top] at hle
  omega

end Dimension

/-- The degeneracy boundary is inhabited: a single clock channel cannot absorb every conservation
defect of a two-dimensional defect module. -/
theorem exists_unabsorbable_defect_single_clock :
    ¬ AbsorbsDefect (LinearMap.inl ℝ ℝ ℝ) ((0, 1) : ℝ × ℝ) := by
  rintro ⟨t, ht⟩
  have hsnd := congrArg Prod.snd ht
  simp at hsnd

end GaloisForLFunctions.HTGeometry
