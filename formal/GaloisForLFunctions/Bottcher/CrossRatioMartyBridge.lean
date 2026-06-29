/-
# Marty obstruction for frontier cross-ratios

This file records the derivative-bound form of the spherical cross-ratio obstruction.  A uniform
spherical-derivative bound would make Marty produce a spherical locally uniform subsequential limit
of the cross-ratio family, but `CrossRatioNormalBridge` forbids such a limit on a Julia-frontier ball.
-/
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- Marty-form obstruction for a genuine frontier cross-ratio family.

On a frontier neighborhood where `Rseq` is the genuine iterate cross-ratio and the inverse-Mobius
nondegeneracy hypotheses hold, the spherical derivatives of `Rseq` cannot be uniformly bounded. -/
theorem not_sphericalDeriv_bounded_crossRatio_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hdiff : ∀ n z, z ∈ ball z₀ Rball → DifferentiableAt ℂ (Rseq n) z) :
    ¬ ∀ n z, z ∈ ball z₀ Rball → sphericalDeriv (Rseq n) z ≤ M := by
  intro hM
  obtain ⟨φ, G, hφ, hconv⟩ :=
    marty_normal_subseq (f := Rseq) (c := z₀) (R := Rball) (r := ρ) (M := M)
      hρ0 hρR hdiff hM
  have hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ) := by
    intro n z hz
    exact ((hdiff n z (closedBall_subset_ball hρR hz)).continuousAt).continuousWithinAt
  have hGcont : ContinuousOn G (closedBall z₀ ρ) := by
    refine hconv.continuousOn (Frequently.of_forall ?_)
    intro k
    exact continuous_stereo.comp_continuousOn (hRcont (φ k))
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hρ0 hU hαβ hβ hα
    hpreα hzβ hRcont hR ⟨φ, G, hφ, hGcont, hconv⟩

/-- Pointed form of `not_sphericalDeriv_bounded_crossRatio_on_frontier_ball`. -/
theorem exists_sphericalDeriv_gt_crossRatio_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hdiff : ∀ n z, z ∈ ball z₀ Rball → DifferentiableAt ℂ (Rseq n) z) :
    ∃ n z, z ∈ ball z₀ Rball ∧ M < sphericalDeriv (Rseq n) z := by
  by_contra h
  have hle : ∀ n z, z ∈ ball z₀ Rball → sphericalDeriv (Rseq n) z ≤ M := by
    intro n z hz
    by_contra hnot
    exact h ⟨n, z, hz, lt_of_not_ge hnot⟩
  exact not_sphericalDeriv_bounded_crossRatio_on_frontier_ball
    hzfront hρ0 hρR hU hαβ hβ hα hpreα hzβ hR hdiff hle

/-- Concrete derivative-bound obstruction for the raw iterate cross-ratio family. -/
theorem not_sphericalDeriv_bounded_iterate_crossRatio_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rball, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rball, z ≠ β) :
    ¬ ∀ n z, z ∈ ball z₀ Rball →
      sphericalDeriv
        (fun y => ((quadratic c)^[n] y - α) * (y - β) /
          (((quadratic c)^[n] y - β) * (y - α))) z ≤ M := by
  let Rseq : ℕ → ℂ → ℂ := fun n y => ((quadratic c)^[n] y - α) * (y - β) /
    (((quadratic c)^[n] y - β) * (y - α))
  have hU : closedBall z₀ ρ ⊆ ball z₀ Rball := closedBall_subset_ball hρR
  have hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rball) := by
    intro n z hz
    rfl
  have hdiff : ∀ n z, z ∈ ball z₀ Rball → DifferentiableAt ℂ (Rseq n) z := by
    intro n z hz
    exact differentiableAt_crossRatio (hβ n z hz) (hα z hz)
  exact not_sphericalDeriv_bounded_crossRatio_on_frontier_ball
    (U := ball z₀ Rball) (Rseq := Rseq) hzfront hρ0 hρR hU hαβ hβ hα hpreα hzβ
    hR hdiff

/-- Pointed concrete derivative blow-up for the raw iterate cross-ratio family. -/
theorem exists_sphericalDeriv_gt_iterate_crossRatio_on_frontier_ball {c α β z₀ : ℂ}
    {Rball ρ M : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rball)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rball, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rball, z ≠ β) :
    ∃ n z, z ∈ ball z₀ Rball ∧
      M < sphericalDeriv
        (fun y => ((quadratic c)^[n] y - α) * (y - β) /
          (((quadratic c)^[n] y - β) * (y - α))) z := by
  by_contra h
  have hle : ∀ n z, z ∈ ball z₀ Rball →
      sphericalDeriv
        (fun y => ((quadratic c)^[n] y - α) * (y - β) /
          (((quadratic c)^[n] y - β) * (y - α))) z ≤ M := by
    intro n z hz
    by_contra hnot
    exact h ⟨n, z, hz, lt_of_not_ge hnot⟩
  exact not_sphericalDeriv_bounded_iterate_crossRatio_on_frontier_ball
    hzfront hρ0 hρR hαβ hβ hα hpreα hzβ hle

end

end Bottcher
