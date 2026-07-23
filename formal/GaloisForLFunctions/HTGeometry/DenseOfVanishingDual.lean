import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Density from a vanishing dual

The Hahn–Banach density criterion: a submodule of a real normed space whose
only vanishing continuous functional is zero is dense.  Obtained from the
geometric Hahn–Banach point/closed-set separation: a functional bounded above
on a submodule vanishes on it, so a point outside the closure is separated by
a functional annihilating the submodule.

This is the closure engine for joint-graph completeness statements: the
annihilator computation (dual reduction, oversampling, carrier separation)
shows every vanishing functional is zero, and this criterion converts that
into density of the finite-support graph.
-/

noncomputable section

namespace HTGeometry

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous functional separating a point from a closed submodule can be
chosen to vanish on the submodule. -/
theorem exists_dual_vanishing_of_notMem_closed_submodule
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
  · have h0 : (0:ℝ) < u := by
      have := hl 0 p.zero_mem
      simpa using this
    intro h
    rw [h] at hu
    linarith

/-- **Hahn–Banach density criterion**: a submodule annihilated only by the
zero functional is dense. -/
theorem topologicalClosure_eq_top_of_forall_dual_eq_zero
    (p : Submodule ℝ E)
    (h : ∀ f : E →L[ℝ] ℝ, (∀ x ∈ p, f x = 0) → f = 0) :
    p.topologicalClosure = ⊤ := by
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p.topologicalClosure := by
    by_contra h'
    rw [not_exists] at h'
    exact hne (Submodule.eq_top_iff'.2 fun x => not_not.1 (h' x))
  obtain ⟨f, hf0, hfx⟩ := exists_dual_vanishing_of_notMem_closed_submodule
    p.topologicalClosure (Submodule.isClosed_topologicalClosure p) hx
  have hzero : f = 0 := h f fun y hy =>
    hf0 y (Submodule.le_topologicalClosure p hy)
  rw [hzero] at hfx
  simp at hfx

end HTGeometry
