import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.Basic

/-! # Uniform tails close the noncompact Arzela--Ascoli argument

Local equicontinuity and uniform vanishing at both ends give compactness in
the actual global supremum norm. No completion or weighted norm is introduced.
-/

open Set Metric Topology
open scoped BoundedContinuousFunction

namespace HTGeometry
noncomputable section

theorem totallyBounded_bcf_of_uniform_tails (A : Set (ℝ →ᵇ ℂ))
    {M : ℝ} (hM : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ M)
    (hE : Equicontinuous (fun f : A => (f.val : ℝ → ℂ)))
    (hT : ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ f ∈ A, ∀ x,
      R ≤ |x| → ‖f x‖ ≤ ε) : TotallyBounded A := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  let η := ε/8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R, hR⟩ := hT η hη
  have hU : ∀ x : ℝ, ∃ U : Set ℝ, x ∈ U ∧ IsOpen U ∧
      ∀ y ∈ U, ∀ z ∈ U, ∀ f ∈ A, dist (f y) (f z) < η := by
    intro x
    obtain ⟨U, hUx, hdist⟩ := (Metric.equicontinuousAt_iff_pair.mp (hE x)) η hη
    obtain ⟨V, hVU, hVo, hxV⟩ := _root_.mem_nhds_iff.mp hUx
    exact ⟨V, hxV, hVo, fun y hy z hz f hf => hdist y (hVU hy) z (hVU hz) ⟨f, hf⟩⟩
  choose U hU using hU
  obtain ⟨tα, _, htα, hcover⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).elim_finite_subcover_image
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hU x).2.1)
    (fun x _ => mem_biUnion (mem_univ x) (hU x).1)
  obtain ⟨_⟩ := htα.nonempty_fintype
  let B := closedBall (0 : ℂ) M
  obtain ⟨tβ, _, htβ, hβcover⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : ℂ) M) hη
  obtain ⟨_⟩ := htβ.nonempty_fintype
  have hgrid : ∀ y : B, ∃ z : tβ, dist (y : ℂ) (z : ℂ) < η := by
    intro y
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hβcover y.property)
    exact ⟨⟨z, hz⟩, by simpa only [mem_ball, dist_comm] using hyz⟩
  choose F hF using hgrid
  let Q (f : A) (a : tα) : B :=
    ⟨f.val a, by simpa only [B, mem_closedBall, dist_zero_right] using hM f.val f.property a⟩
  refine ⟨tα → tβ, inferInstance, (fun f a => F (Q f a)), ?_⟩
  intro f g hfg
  apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity : 0 ≤ ε/2)).mpr ?_)
    (by linarith)
  intro x
  by_cases hx : x ∈ Icc (-R) R
  · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover hx)
    have hf : dist (f.val x) (f.val a) < η :=
      (hU a).2.2 x hxa a (hU a).1 f.val f.property
    have hg : dist (g.val x) (g.val a) < η :=
      (hU a).2.2 x hxa a (hU a).1 g.val g.property
    have he : (F (Q f ⟨a, ha⟩) : ℂ) = (F (Q g ⟨a, ha⟩) : ℂ) :=
      congrArg (fun p : tα → tβ => (p ⟨a, ha⟩ : ℂ)) hfg
    have hfa : dist (f.val a) (F (Q f ⟨a, ha⟩) : ℂ) < η := hF (Q f ⟨a, ha⟩)
    have hga : dist (g.val a) (F (Q f ⟨a, ha⟩) : ℂ) < η := by
      rw [he]
      exact hF (Q g ⟨a, ha⟩)
    have hab := dist_triangle_right (f.val a) (g.val a) (F (Q f ⟨a, ha⟩) : ℂ)
    have hab' := dist_triangle4_right (f.val x) (g.val x) (f.val a) (g.val a)
    dsimp [η] at hf hg hfa hga
    linarith
  · have hxR : R ≤ |x| := le_of_lt (lt_of_not_ge (fun h => hx (abs_le.mp h)))
    have hf := hR f.val f.property x hxR
    have hg := hR g.val g.property x hxR
    have hd := dist_triangle_right (f.val x) (g.val x) (0 : ℂ)
    simp only [dist_zero_right] at hd
    dsimp [η] at hf hg
    linarith

theorem isCompact_closure_bcf_of_uniform_tails (A : Set (ℝ →ᵇ ℂ))
    {M : ℝ} (hM : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ M)
    (hE : Equicontinuous (fun f : A => (f.val : ℝ → ℂ)))
    (hT : ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ f ∈ A, ∀ x,
      R ≤ |x| → ‖f x‖ ≤ ε) : IsCompact (closure A) :=
  (totallyBounded_bcf_of_uniform_tails A hM hE hT).closure.isCompact_of_isClosed isClosed_closure

end
end HTGeometry
