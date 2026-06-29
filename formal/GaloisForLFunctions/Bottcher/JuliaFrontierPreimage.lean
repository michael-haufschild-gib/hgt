/-
# Julia frontier pulls back under quadratic preimages

This file proves the local invariance fact needed by the fixed-anchor preimage route:
if an iterate sends `z` to a repelling fixed point on `∂K_c`, then `z` itself is on
`∂K_c`.
-/
import GaloisForLFunctions.Bottcher.RepellingFixedPoint
import Mathlib.Analysis.Complex.OpenMapping

open Set Filter Topology Metric Polynomial

namespace Bottcher

noncomputable section

/-- A nonconstant complex polynomial map is open; in particular `z ↦ z² + c` is open. -/
theorem isOpenMap_quadratic (c : ℂ) : IsOpenMap (quadratic c) := by
  let P : Polynomial ℂ := Polynomial.X ^ 2 + Polynomial.C c
  have hdeg : P.natDegree ≠ 0 := by
    dsimp [P]
    norm_num
  have hopenP : IsOpenMap (fun z : ℂ => Polynomial.eval z P) :=
    (Polynomial.isOpenQuotientMap_eval P hdeg).isOpenMap
  convert hopenP using 1
  ext z
  simp [quadratic, P]

/-- The Julia frontier is totally invariant under taking quadratic preimages. -/
theorem mem_frontier_of_quadratic_mem_frontier {c z : ℂ}
    (hfront : quadratic c z ∈ frontier (filledJulia c)) :
    z ∈ frontier (filledJulia c) := by
  rw [frontier_eq_closure_inter_closure] at hfront ⊢
  have himageK : quadratic c z ∈ filledJulia c := by
    have hclosed : IsClosed (filledJulia c) := isClosed_filledJulia c
    simpa [hclosed.closure_eq] using hfront.1
  have hzK : z ∈ filledJulia c := (mem_filledJulia_iff_quadratic_mem c z).mpr himageK
  refine ⟨subset_closure hzK, ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hfreq : ∃ᶠ w in 𝓝 (quadratic c z), w ∈ (filledJulia c)ᶜ :=
    mem_closure_iff_frequently.mp hfront.2
  have himg : quadratic c '' ball z ε ∈ 𝓝 (quadratic c z) :=
    (isOpenMap_quadratic c).image_mem_nhds (Metric.ball_mem_nhds z hε)
  obtain ⟨w, hwcomp, hwimg⟩ := (hfreq.and_eventually himg).exists
  rcases hwimg with ⟨y, hyball, rfl⟩
  refine ⟨y, ?_, ?_⟩
  · rw [mem_compl_iff]
    intro hyK
    exact hwcomp ((mem_filledJulia_iff_quadratic_mem c y).mp hyK)
  · simpa [dist_comm] using hyball

/-- The quadratic map sends the Julia frontier into itself. -/
theorem quadratic_mem_frontier_of_mem_frontier {c z : ℂ}
    (hfront : z ∈ frontier (filledJulia c)) :
    quadratic c z ∈ frontier (filledJulia c) := by
  rw [frontier_eq_closure_inter_closure] at hfront ⊢
  have hzK : z ∈ filledJulia c := by
    have hclosed : IsClosed (filledJulia c) := isClosed_filledJulia c
    simpa [hclosed.closure_eq] using hfront.1
  refine ⟨subset_closure ((mem_filledJulia_iff_quadratic_mem c z).mp hzK), ?_⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hfreq : ∃ᶠ y in 𝓝 z, y ∈ (filledJulia c)ᶜ :=
    mem_closure_iff_frequently.mp hfront.2
  have hnear : ∀ᶠ y in 𝓝 z, quadratic c y ∈ ball (quadratic c z) ε :=
    (continuous_quadratic c).continuousAt (Metric.ball_mem_nhds (quadratic c z) hε)
  obtain ⟨y, hycomp, hyball⟩ := (hfreq.and_eventually hnear).exists
  refine ⟨quadratic c y, ?_, ?_⟩
  · rw [mem_compl_iff]
    intro hyK
    exact hycomp ((mem_filledJulia_iff_quadratic_mem c y).mpr hyK)
  · simpa [Metric.mem_ball, dist_comm] using hyball

/-- The Julia frontier is totally invariant under the quadratic map. -/
theorem quadratic_mem_frontier_iff {c z : ℂ} :
    quadratic c z ∈ frontier (filledJulia c) ↔ z ∈ frontier (filledJulia c) :=
  ⟨mem_frontier_of_quadratic_mem_frontier, quadratic_mem_frontier_of_mem_frontier⟩

/-- The Julia frontier pulls back along every finite quadratic iterate. -/
theorem mem_frontier_of_iterate_mem_frontier {c z : ℂ} {n : ℕ}
    (hfront : (quadratic c)^[n] z ∈ frontier (filledJulia c)) :
    z ∈ frontier (filledJulia c) := by
  induction n generalizing z with
  | zero =>
      simpa using hfront
  | succ n ih =>
      have hpre : (quadratic c)^[n] z ∈ frontier (filledJulia c) := by
        apply mem_frontier_of_quadratic_mem_frontier
        simpa [Function.iterate_succ_apply'] using hfront
      exact ih hpre

/-- A point whose forward orbit hits a repelling fixed point lies on `∂K_c`. -/
theorem mem_frontier_of_forward_hit_repelling_fixed {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α) (hfix : quadratic c α = α)
    (hrep : 1 < ‖(2 : ℂ) * α‖) :
    z ∈ frontier (filledJulia c) := by
  refine mem_frontier_of_iterate_mem_frontier (n := n) ?_
  simpa [hhit] using mem_frontier_of_repelling_fixed hfix hrep

end

end Bottcher
