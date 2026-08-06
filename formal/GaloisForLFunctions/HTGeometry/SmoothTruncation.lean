import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Truncating a locally smooth function to a globally smooth one

A function that is smooth at a point agrees near that point with a function that is smooth
everywhere: multiply it by a bump function supported in a ball on which it is smooth, and extend by
zero.  The two open sets — the ball, and the complement of the closed ball carrying the bump —
cover the space, and on each of them the truncation is smooth, on the first because it is a product
of smooth functions and on the second because it vanishes.

* `HTGeometry.exists_contDiff_eventuallyEq` : a germ of a smooth function is the germ of a globally
  smooth function.
-/

namespace HTGeometry

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A function smooth on an open set agrees, near each of its points, with a globally smooth
function.** -/
theorem exists_contDiff_eventuallyEq {h : E → F} {u : Set E} (hu : IsOpen u) {x : E} (hx : x ∈ u)
    (hcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h u) :
    ∃ g : E → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ᶠ y in nhds x, g y = h y := by
  classical
  obtain ⟨R, hR, hRu⟩ := Metric.mem_nhds_iff.1 (hu.mem_nhds hx)
  set χ : ContDiffBump x := ⟨R / 3, R / 2, by positivity, by linarith⟩ with hχ
  set g : E → F := Set.indicator (ball x R) (fun y => (χ y) • h y) with hg
  have hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : E → ℝ) := χ.contDiff (n := ⊤)
  refine ⟨g, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ ball x R
    · have heq : ∀ᶠ z in nhds y, g z = (fun z => (χ z) • h z) z :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun z hz =>
          Set.indicator_of_mem hz (fun y => (χ y) • h y)
      refine ContDiffAt.congr_of_eventuallyEq ?_ heq
      exact hχsmooth.contDiffAt.smul (hcd.contDiffAt (Filter.mem_of_superset
        (isOpen_ball.mem_nhds hy) hRu))
    · have hdist : R / 2 < dist y x := by
        rw [mem_ball] at hy
        have := not_lt.1 hy
        linarith
      have hopen : IsOpen ((closedBall x (R / 2))ᶜ) := isClosed_closedBall.isOpen_compl
      have hymem : y ∈ (closedBall x (R / 2))ᶜ := by
        rw [Set.mem_compl_iff, mem_closedBall]
        exact not_le.2 hdist
      have heq : ∀ᶠ z in nhds y, g z = (fun _ : E => (0 : F)) z := by
        refine Filter.eventually_of_mem (hopen.mem_nhds hymem) fun z hz => ?_
        rw [Set.mem_compl_iff, mem_closedBall, not_le] at hz
        by_cases hzb : z ∈ ball x R
        · rw [hg, Set.indicator_of_mem hzb, χ.zero_of_le_dist (le_of_lt hz), zero_smul]
        · rw [hg, Set.indicator_of_notMem hzb]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq
  · refine Filter.eventually_of_mem
      (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < R / 3))) fun y hy => ?_
    have hyR : y ∈ ball x R := ball_subset_ball (by linarith) hy
    rw [hg, Set.indicator_of_mem hyR]
    have hone : (χ : E → ℝ) y = 1 := by
      refine χ.one_of_mem_closedBall ?_
      rw [mem_closedBall]
      rw [mem_ball] at hy
      exact le_of_lt hy
    rw [hone, one_smul]

end HTGeometry
