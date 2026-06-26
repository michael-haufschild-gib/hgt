/-
# Three-value Montel, conditional form — normality of an omitting family from disk lifts

The **fundamental normality test** (a family omitting `0, 1` is normal) follows from lifting through the
universal covering `μ : 𝔻 → ℂ∖{0,1}` (the modular λ): each member lifts to a disk-valued (hence bounded)
holomorphic map, the bounded family is normal (`montel_subseq`), and pushing back down by the continuous
`μ` preserves uniform convergence.

This file proves that argument **modulo the lift**: given that each `f_n` admits a holomorphic lift
`g_n : ball c R → 𝔻` with `μ ∘ g_n = f_n` (exactly what the covering `μ` provides — continuously via
mathlib's `existsUnique_continuousMap_lifts`, holomorphically via `differentiableOn_of_continuousOn_lift`),
the family `f_n` is normal. The only remaining input to three-value Montel is then the **covering μ
itself** (the modular λ from Jacobi theta).

New file (Montel/Julia lane — three-value Montel). Consumes `MontelNormal`.
-/
import GaloisForLFunctions.Bottcher.MontelNormal

open Complex Metric Set Filter Topology

namespace Bottcher

theorem normal_of_omitting_lift {f : ℕ → ℂ → ℂ} {c : ℂ} {R r : ℝ} {μ : ℂ → ℂ}
    (hr0 : 0 < r) (hrR : r < R / 2) (hμcont : Continuous μ)
    (hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, ‖g z‖ ≤ 1) ∧ Set.EqOn (fun z => μ (g z)) (f n) (ball c R)) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → ℂ), StrictMono φ ∧
      TendstoUniformlyOn (fun k => f (φ k)) G atTop (closedBall c r) := by
  choose g hg_diff hg_bd hg_eq using hlift
  obtain ⟨φ, gl, hφ, hgconv, -⟩ :=
    montel_subseq hr0 hrR hg_diff (fun n z hz => hg_bd n z hz)
  have hsubR : closedBall c r ⊆ ball c R := closedBall_subset_ball (by linarith)
  -- membership of values in the compact unit ball
  have hgk_mem : ∀ k (z : ℂ), z ∈ closedBall c r → g (φ k) z ∈ closedBall (0:ℂ) 1 := by
    intro k z hz; rw [mem_closedBall, dist_zero_right]; exact hg_bd (φ k) z (hsubR hz)
  have hgl_mem : ∀ z ∈ closedBall c r, gl z ∈ closedBall (0:ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    refine le_of_tendsto ((hgconv.tendsto_at hz).norm) ?_
    exact Eventually.of_forall (fun k => hg_bd (φ k) z (hsubR hz))
  -- μ uniformly continuous on the compact unit ball
  have hUC : UniformContinuousOn μ (closedBall (0:ℂ) 1) :=
    (isCompact_closedBall 0 1).uniformContinuousOn_of_continuous hμcont.continuousOn
  -- compose
  have hcomp : TendstoUniformlyOn (fun k z => μ (g (φ k) z)) (fun z => μ (gl z))
      atTop (closedBall c r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.uniformContinuousOn_iff] at hUC
    obtain ⟨δ, hδ, hδμ⟩ := hUC ε hε
    rw [Metric.tendstoUniformlyOn_iff] at hgconv
    filter_upwards [hgconv δ hδ] with k hk
    intro z hz
    exact hδμ (gl z) (hgl_mem z hz) (g (φ k) z) (hgk_mem k z hz) (hk z hz)
  refine ⟨φ, fun z => μ (gl z), hφ, ?_⟩
  -- f (φ k) = μ ∘ g (φ k) on closedBall c r
  refine hcomp.congr ?_
  filter_upwards with k z hz
  exact hg_eq (φ k) (hsubR hz)

end Bottcher
