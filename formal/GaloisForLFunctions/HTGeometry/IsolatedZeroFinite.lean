import Mathlib

/-!
# Isolated zeros in a compact interval are finitely many

A set inside a compact interval all of whose points are isolated is finite, and a simple zero of a
differentiable function is isolated.  Together these turn "every zero is simple" into "there are
finitely many zeros", which is the hypothesis the Sturm variation law consumes.
-/

noncomputable section

open Set

namespace HTGeometry

/-- **A compact set with isolated points is finite.** -/
theorem finite_of_isolated_in_compact {s : Set ℝ} (hcomp : IsCompact s)
    (hiso : ∀ y ∈ s, ∃ ε > 0, ∀ z ∈ s, |z - y| < ε → z = y) : s.Finite := by
  refine hcomp.finite ?_
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro y hy
  obtain ⟨ε, hε, h⟩ := hiso y hy
  refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    have hd : |z - y| < ε := by
      rw [Metric.mem_ball, Real.dist_eq] at hz1
      exact hz1
    exact h z hz2 hd
  · rintro rfl
    exact ⟨Metric.mem_ball_self hε, hy⟩

/-- **A simple zero is isolated.**  If the derivative is nonzero at a zero, no other zero lies
nearby. -/
theorem isolated_of_simple_zero {f f' : ℝ → ℝ} {x : ℝ}
    (hf : HasDerivAt f (f' x) x) (hzero : f x = 0) (hne : f' x ≠ 0) :
    ∃ ε > 0, ∀ z : ℝ, f z = 0 → |z - x| < ε → z = x := by
  have hev : ∀ᶠ z in nhdsWithin x ({x}ᶜ : Set ℝ), f z ≠ f x :=
    (hf.tendsto_nhdsNE hne).eventually
      (by filter_upwards [self_mem_nhdsWithin] with y hy using hy)
  rw [Filter.eventually_iff, mem_nhdsWithin] at hev
  obtain ⟨u, hu, hxu, hsub⟩ := hev
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hxu
  refine ⟨ε, hε, fun z hz hdist => ?_⟩
  by_contra hne'
  have hzu : z ∈ u := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    exact hdist
  have hzc : z ∈ ({x}ᶜ : Set ℝ) := hne'
  have hmem := hsub ⟨hzu, hzc⟩
  have : f z ≠ f x := hmem
  rw [hz, hzero] at this
  exact this rfl

/-- **Simple zeros in a compact interval are finitely many.** -/
theorem finite_zeros_of_simple {f f' : ℝ → ℝ} {a b : ℝ} (hf : Continuous f)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hsimple : ∀ x ∈ Icc a b, f x = 0 → f' x ≠ 0) :
    {x : ℝ | x ∈ Icc a b ∧ f x = 0}.Finite := by
  have hset : {x : ℝ | x ∈ Icc a b ∧ f x = 0} = Icc a b ∩ f ⁻¹' {0} := by
    ext x
    simp [Set.mem_inter_iff, Set.mem_preimage]
  have hclosed : IsClosed (f ⁻¹' {0}) := (isClosed_singleton).preimage hf
  have hcomp : IsCompact (Icc a b ∩ f ⁻¹' {0}) :=
    (isCompact_Icc.inter_right hclosed)
  rw [hset]
  refine finite_of_isolated_in_compact hcomp (fun y hy => ?_)
  obtain ⟨hyIcc, hyzero⟩ := hy
  have hy0 : f y = 0 := hyzero
  obtain ⟨ε, hε, h⟩ := isolated_of_simple_zero (hderiv y hyIcc) hy0 (hsimple y hyIcc hy0)
  exact ⟨ε, hε, fun z hz hd => h z hz.2 hd⟩

end HTGeometry
