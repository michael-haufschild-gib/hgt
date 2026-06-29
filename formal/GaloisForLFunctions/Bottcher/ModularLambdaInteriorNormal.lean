/-
# Interior branch of the modular-lambda Montel extraction

The global closed-disk extension of `stereo ∘ λ ∘ cayleyInv` is not the right object: the
modular universal cover has cusp/limit-set behaviour at the boundary.  This file isolates the
valid interior branch needed by the omitted-values normality proof.  If the bounded disk lifts have
a locally-uniform limit whose image stays in a strictly smaller closed disk, then composing with the
modular target preserves uniform convergence in the spherical model.
-/
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingMarty

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- The sphere-valued modular disk target is continuous on every strict closed subdisk. -/
theorem continuousOn_stereo_modularDiskTarget_closedBall {s : ℝ} (hs : s < 1) :
    ContinuousOn (fun z : ℂ => stereo (modularLambda (cayleyInv z))) (closedBall (0 : ℂ) s) := by
  intro z hz
  have hzlt : ‖z‖ < 1 := by
    have hzle : ‖z‖ ≤ s := by
      simpa [mem_closedBall, dist_zero_right] using hz
    exact lt_of_le_of_lt hzle hs
  exact continuous_stereo.continuousAt.comp_continuousWithinAt
    ((modularDiskTarget_differentiableAt hzlt).continuousAt.continuousWithinAt)

/-- Interior composition branch for the modular-lambda lift.

If `gₙ → g` uniformly on a compact set and the limit values satisfy `‖g z‖ ≤ s < 1`, then
`stereo (λ(cayleyInv (gₙ z)))` converges uniformly to the corresponding composed limit.  This is the
part of three-value Montel where the lift limit stays away from the boundary of the disk; the
remaining branch is the cusp/boundary escape case. -/
theorem tendstoUniformlyOn_stereo_modularDiskTarget_of_lift_limit_strict
    {K : Set ℂ} {gseq : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : ℝ}
    (hs1 : s < 1)
    (hg_strict : ∀ z ∈ K, ‖g z‖ ≤ s)
    (hgconv : TendstoUniformlyOn gseq g atTop K) :
    TendstoUniformlyOn
      (fun n z => stereo (modularLambda (cayleyInv (gseq n z))))
      (fun z => stereo (modularLambda (cayleyInv (g z)))) atTop K := by
  let t : ℝ := (s + 1) / 2
  have hst : s < t := by
    dsimp [t]
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    linarith
  have hlim_mem : ∀ z ∈ K, g z ∈ closedBall (0 : ℂ) t := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    exact (hg_strict z hz).trans (le_of_lt hst)
  have hseq_mem : ∀ᶠ n in atTop, ∀ z ∈ K, gseq n z ∈ closedBall (0 : ℂ) t := by
    rw [Metric.tendstoUniformlyOn_iff] at hgconv
    filter_upwards [hgconv (t - s) (by linarith)] with n hn
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    have hdist : dist (g z) (gseq n z) < t - s := hn z hz
    calc
      ‖gseq n z‖ = dist (0 : ℂ) (gseq n z) := by rw [dist_zero_left]
      _ ≤ dist (0 : ℂ) (g z) + dist (g z) (gseq n z) := dist_triangle _ _ _
      _ = ‖g z‖ + dist (g z) (gseq n z) := by rw [dist_zero_left]
      _ ≤ s + dist (g z) (gseq n z) := by linarith [hg_strict z hz]
      _ ≤ t := by linarith
  have hμUC : UniformContinuousOn
      (fun z : ℂ => stereo (modularLambda (cayleyInv z))) (closedBall (0 : ℂ) t) :=
    (isCompact_closedBall (0 : ℂ) t).uniformContinuousOn_of_continuous
      (continuousOn_stereo_modularDiskTarget_closedBall ht1)
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hseq_mem hlim_mem hμUC hgconv

end

end Bottcher
