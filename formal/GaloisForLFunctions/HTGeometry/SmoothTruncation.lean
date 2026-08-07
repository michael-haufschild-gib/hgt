import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity

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


section Family

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A family of functions smooth on an open set is globally smooth after truncation**, and the
truncation agrees with the family on an open neighbourhood of any compact subset.  One cutoff, equal
to one near the compact set and supported in the open set, is used for the whole family. -/
theorem exists_contDiff_family_eqOn {ι : Type*} {h : ι → E → F} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hh : ∀ (i : ι), ∀ z ∈ W, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h i) z) :
    ∃ (g : ι → E → F) (V : Set E), IsOpen V ∧ K ⊆ V ∧
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g i)) ∧ (∀ (i : ι), ∀ z ∈ V, g i z = h i z) ∧
      ∀ (i : ι) (z : E), h i z = 0 → g i z = 0 := by
  classical
  obtain ⟨L, hLc, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨L', hL'c, hKL', hL'L⟩ := exists_compact_between hK isOpen_interior hKL
  obtain ⟨χ, hχ0, hχ1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed (modelWithCornersSelf ℝ E) (n := ⊤)
      (s := (interior L)ᶜ) (t := L') isOpen_interior.isClosed_compl hL'c.isClosed
      (Set.disjoint_left.2 fun a ha hb => ha (hL'L hb))
  have hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : E → ℝ) :=
    contMDiff_iff_contDiff.1 χ.contMDiff
  refine ⟨fun i => Set.indicator W (fun z => (χ z) • h i z), interior L', isOpen_interior, hKL',
    ?_, ?_, ?_⟩
  · intro i
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ W
    · have heq : ∀ᶠ z in nhds y,
          Set.indicator W (fun z => (χ z) • h i z) z = (fun z => (χ z) • h i z) z :=
        Filter.eventually_of_mem (hW.mem_nhds hy) fun z hz => Set.indicator_of_mem hz _
      refine ContDiffAt.congr_of_eventuallyEq ?_ heq
      exact hχsmooth.contDiffAt.smul (hh i y hy)
    · have hyL : y ∈ Lᶜ := fun hyL => hy (hLW hyL)
      have heq : ∀ᶠ z in nhds y,
          Set.indicator W (fun z => (χ z) • h i z) z = (fun _ : E => (0 : F)) z := by
        refine Filter.eventually_of_mem ((hLc.isClosed.isOpen_compl).mem_nhds hyL)
          fun z hz => ?_
        by_cases hzW : z ∈ W
        · rw [Set.indicator_of_mem hzW]
          have hzL : z ∈ (interior L)ᶜ := fun hzi => hz (interior_subset hzi)
          rw [hχ0 hzL]
          exact zero_smul _ _
        · rw [Set.indicator_of_notMem hzW]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq
  · intro i z hz
    have hzL' : z ∈ L' := interior_subset hz
    have hzW : z ∈ W := hLW (interior_subset (hL'L hzL'))
    show Set.indicator W (fun z => (χ z) • h i z) z = h i z
    rw [Set.indicator_of_mem hzW, hχ1 hzL']
    exact one_smul _ _
  · intro i z hz0
    show Set.indicator W (fun z => (χ z) • h i z) z = 0
    by_cases hzW : z ∈ W
    · rw [Set.indicator_of_mem hzW, hz0, smul_zero]
    · rw [Set.indicator_of_notMem hzW]

end Family

end HTGeometry
