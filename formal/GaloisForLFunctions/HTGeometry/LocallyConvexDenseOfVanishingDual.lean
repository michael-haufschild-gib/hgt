import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Density from a vanishing dual, in a locally convex space

The Hahn–Banach density criterion does not need a norm: the geometric separation of a point from a
closed convex set holds in any locally convex real topological vector space, and a functional
bounded above on a subspace vanishes on it.  So a subspace annihilated only by the zero functional
is dense there too.

This is the form required when one factor of a product is a Fréchet space — for instance a space of
holomorphic functions, whose topology is given by seminorms and not by a norm.

* `HTGeometry.exists_dual_vanishing_of_notMem_closed_submodule_lcs`;
* `HTGeometry.topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs`;
* `HTGeometry.topologicalClosure_eq_top_of_forall_pair_dual_eq_zero_lcs`;
* `HTGeometry.topologicalClosure_span_eq_top_of_pair_dual_lcs`.
-/

noncomputable section

namespace HTGeometry

open Set

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A functional separating a point from a closed subspace can be chosen to vanish on it. -/
theorem exists_dual_vanishing_of_notMem_closed_submodule_lcs
    (p : Submodule ℝ E) (hp : IsClosed (p : Set E)) {x : E} (hx : x ∉ p) :
    ∃ f : E →L[ℝ] ℝ, (∀ y ∈ p, f y = 0) ∧ f x ≠ 0 := by
  have hconv : Convex ℝ (p : Set E) := fun a ha b hb s t hs ht hst =>
    p.add_mem (p.smul_mem s ha) (p.smul_mem t hb)
  obtain ⟨l, u, hl, hu⟩ := geometric_hahn_banach_closed_point hconv hp hx
  refine ⟨l, ?_, ?_⟩
  · intro y hy
    by_contra hne
    have hall : ∀ t : ℝ, t * l y < u := by
      intro t
      have := hl (t • y) (p.smul_mem t hy)
      simpa using this
    have hcontr := hall ((|u| + 1) / l y)
    rw [div_mul_cancel₀ _ hne] at hcontr
    have := le_abs_self u
    linarith
  · have h0 : (0 : ℝ) < u := by
      have := hl 0 p.zero_mem
      simpa using this
    intro h
    rw [h] at hu
    linarith

/-- **The density criterion in a locally convex space.** -/
theorem topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs
    (p : Submodule ℝ E)
    (h : ∀ f : E →L[ℝ] ℝ, (∀ x ∈ p, f x = 0) → f = 0) :
    p.topologicalClosure = ⊤ := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p.topologicalClosure := by
    by_contra h'
    rw [not_exists] at h'
    exact hne (Submodule.eq_top_iff'.2 fun x => not_not.1 (h' x))
  obtain ⟨f, hfvan, hfx⟩ :=
    exists_dual_vanishing_of_notMem_closed_submodule_lcs p.topologicalClosure
      p.isClosed_topologicalClosure hx
  have hvan : ∀ y ∈ p, f y = 0 := fun y hy => hfvan y (p.le_topologicalClosure hy)
  exact hfx (by rw [h f hvan]; rfl)

variable {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- **Joint density in a product of locally convex spaces.**  Only the absence of a nonzero
annihilating *pair* is needed; neither factor has to be normed. -/
theorem topologicalClosure_eq_top_of_forall_pair_dual_eq_zero_lcs
    (p : Submodule ℝ (E × F))
    (h : ∀ (f₁ : E →L[ℝ] ℝ) (f₂ : F →L[ℝ] ℝ),
      (∀ z ∈ p, f₁ z.1 + f₂ z.2 = 0) → (∀ x : E, f₁ x = 0) ∧ ∀ y : F, f₂ y = 0) :
    p.topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero_lcs p ?_
  intro f hf
  set f₁ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E F) with hf₁
  set f₂ : F →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inr ℝ E F) with hf₂
  have hval : ∀ (x : E) (y : F), f₁ x + f₂ y = f (x, y) := by
    intro x y
    rw [hf₁, hf₂]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    have hsplit : ((x, y) : E × F) = (x, 0) + (0, y) := by
      ext <;> simp
    rw [hsplit, map_add]
  have hann : ∀ z ∈ p, f₁ z.1 + f₂ z.2 = 0 := by
    intro z hz
    rw [hval z.1 z.2]
    have hzz : ((z.1, z.2) : E × F) = z := rfl
    rw [hzz]
    exact hf z hz
  obtain ⟨h1, h2⟩ := h f₁ f₂ hann
  refine ContinuousLinearMap.ext fun z => ?_
  have hv := hval z.1 z.2
  have hz : ((z.1, z.2) : E × F) = z := rfl
  rw [hz] at hv
  rw [← hv, h1 z.1, h2 z.2, add_zero]
  rfl

/-- **Joint density of a generated graph.**  For a family of pairs `(e i, v i)`, the span is dense
in the product as soon as the only pair of functionals annihilating *every generator* is the zero
pair.  This is the form a joint-graph completeness statement takes: the generators are the
finite-support elements, and the annihilation condition is checked one index at a time. -/
theorem topologicalClosure_span_eq_top_of_pair_dual_lcs {ι : Type*} (e : ι → E) (v : ι → F)
    (h : ∀ (f₁ : E →L[ℝ] ℝ) (f₂ : F →L[ℝ] ℝ),
      (∀ i, f₁ (e i) + f₂ (v i) = 0) → (∀ x : E, f₁ x = 0) ∧ ∀ y : F, f₂ y = 0) :
    (Submodule.span ℝ (Set.range fun i => ((e i, v i) : E × F))).topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_pair_dual_eq_zero_lcs _ ?_
  intro f₁ f₂ hspan
  refine h f₁ f₂ fun i => ?_
  refine hspan ((e i, v i)) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

end HTGeometry
