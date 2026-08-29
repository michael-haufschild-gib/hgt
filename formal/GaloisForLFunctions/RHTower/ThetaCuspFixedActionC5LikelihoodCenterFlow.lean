import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5ExactFirstAtomTailCore
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodGapCumulantRiccati

/-!
# Fixed-action C5 likelihood centre flow

The exact atom-plus-likelihood factorization leaves three centre derivatives of the likelihood
action in direct-C5 transport.  The source likelihood score is strictly concave: its derivative is
the positive but strictly decreasing likelihood curvature.  This gives a positive symmetric
centre difference.  The same decreasing curvature and negative third source jet orient the two
mixed centre channels.  Thus all three likelihood centre-flow contributions have strict positive
orientation on the physical same-half-line chamber.
-/

open Set

namespace RHTower

noncomputable section

/-- Centre derivative contributed by likelihood-interference action. -/
def c5LikelihoodScaleActionJetOne (u t : ℝ) : ℝ :=
  2 * thetaCuspLikelihoodSourceLogPartitionJetOne u -
    thetaCuspLikelihoodSourceLogPartitionJetOne (u + t) -
    thetaCuspLikelihoodSourceLogPartitionJetOne (u - t)

/-- Centre derivative of likelihood-interference first displacement jet. -/
def c5LikelihoodScaleMixedJetOne (u t : ℝ) : ℝ :=
  thetaCuspLikelihoodSourceLogPartitionJetTwo (u - t) -
    thetaCuspLikelihoodSourceLogPartitionJetTwo (u + t)

/-- Centre derivative of likelihood-interference second displacement jet. -/
def c5LikelihoodScaleMixedJetTwo (u t : ℝ) : ℝ :=
  -thetaCuspLikelihoodSourceLogPartitionJetThree (u + t) -
    thetaCuspLikelihoodSourceLogPartitionJetThree (u - t)

/-- Likelihood curvature is strictly decreasing throughout the nonnegative source half-line. -/
theorem strictAntiOn_thetaCuspLikelihoodSourceLogPartitionJetTwo :
    StrictAntiOn thetaCuspLikelihoodSourceLogPartitionJetTwo (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv]
    exact thetaCuspLikelihoodSourceLogPartitionJetThree_neg hx.le

/-- The source likelihood score is strictly concave on the nonnegative source half-line. -/
theorem strictConcaveOn_thetaCuspLikelihoodSourceLogPartitionJetOne :
    StrictConcaveOn ℝ (Ici 0) thetaCuspLikelihoodSourceLogPartitionJetOne := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
      (thetaCuspLikelihoodCoordinate_pos hx)).continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    rw [interior_Ici] at hx hy
    rw [(hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
        (thetaCuspLikelihoodCoordinate_pos hx.le)).deriv,
      (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne
        (thetaCuspLikelihoodCoordinate_pos hy.le)).deriv]
    exact strictAntiOn_thetaCuspLikelihoodSourceLogPartitionJetTwo
      (show x ∈ Ici 0 by
        simpa only [mem_Ici] using
          (le_of_lt (show 0 < x by simpa only [mem_Ioi] using hx)))
      (show y ∈ Ici 0 by
        simpa only [mem_Ici] using
          (le_of_lt (show 0 < y by simpa only [mem_Ioi] using hy))) hxy

/-- Strict midpoint concavity orients the likelihood centre action channel. -/
theorem c5LikelihoodScaleActionJetOne_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < c5LikelihoodScaleActionJetOne u t := by
  have hminus : u - t ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hplus : u + t ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hne : u + t ≠ u - t := by linarith
  have hconc := strictConcaveOn_thetaCuspLikelihoodSourceLogPartitionJetOne
  have hmid := hconc.2 hplus hminus hne
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  unfold c5LikelihoodScaleActionJetOne
  norm_num [smul_eq_mul] at hmid
  have harg : (1 / 2 : ℝ) * (u + t) + 1 / 2 * (u - t) = u := by ring
  rw [harg] at hmid
  linarith

/-- Decreasing likelihood curvature orients the first mixed centre channel. -/
theorem c5LikelihoodScaleMixedJetOne_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < c5LikelihoodScaleMixedJetOne u t := by
  have hminus : u - t ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hplus : u + t ∈ Ici (0 : ℝ) := by simp only [mem_Ici]; linarith
  have hlt : u - t < u + t := by linarith
  have hanti := strictAntiOn_thetaCuspLikelihoodSourceLogPartitionJetTwo
    hminus hplus hlt
  unfold c5LikelihoodScaleMixedJetOne
  linarith

/-- Negative likelihood third source jet orients the second mixed centre channel. -/
theorem c5LikelihoodScaleMixedJetTwo_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < c5LikelihoodScaleMixedJetTwo u t := by
  have hminus := thetaCuspLikelihoodSourceLogPartitionJetThree_neg
    (show 0 ≤ u - t by linarith)
  have hplus := thetaCuspLikelihoodSourceLogPartitionJetThree_neg
    (show 0 ≤ u + t by linarith)
  unfold c5LikelihoodScaleMixedJetTwo
  linarith

/-- The three likelihood centre-flow channels have simultaneous strict orientation. -/
theorem c5LikelihoodCenterFlowJets_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < c5LikelihoodScaleActionJetOne u t ∧
      0 < c5LikelihoodScaleMixedJetOne u t ∧
      0 < c5LikelihoodScaleMixedJetTwo u t := by
  exact ⟨c5LikelihoodScaleActionJetOne_pos ht htu,
    c5LikelihoodScaleMixedJetOne_pos ht htu,
    c5LikelihoodScaleMixedJetTwo_pos ht htu⟩

/-- The first named likelihood channel is the literal centre derivative of its reflected action. -/
theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantAction_center
    {u t : ℝ}
    (hcenter : 0 < thetaCuspLikelihoodCoordinate u)
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (fun x => thetaCuspReflectedLikelihoodCumulantAction x t)
      (c5LikelihoodScaleActionJetOne u t) u := by
  have hc := (hasDerivAt_thetaCuspLikelihoodSourceLogPartition hcenter).const_mul 2
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartition hplus).comp u
    ((hasDerivAt_id u).add_const t)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartition hminus).comp u
    ((hasDerivAt_id u).sub_const t)
  exact ((hc.sub hp).sub hm).congr_deriv (by
    unfold c5LikelihoodScaleActionJetOne
    ring)

/-- The second named likelihood channel is the centre derivative of its first displacement jet. -/
theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne_center
    {u t : ℝ}
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (fun x => thetaCuspReflectedLikelihoodCumulantJetOne x t)
      (c5LikelihoodScaleMixedJetOne u t) u := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne hplus).comp u
    ((hasDerivAt_id u).add_const t)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetOne hminus).comp u
    ((hasDerivAt_id u).sub_const t)
  exact (hm.sub hp).congr_deriv (by
    unfold c5LikelihoodScaleMixedJetOne
    ring)

/-- The third named likelihood channel is the centre derivative of its second displacement jet. -/
theorem hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetTwo_center
    {u t : ℝ}
    (hplus : 0 < thetaCuspLikelihoodCoordinate (u + t))
    (hminus : 0 < thetaCuspLikelihoodCoordinate (u - t)) :
    HasDerivAt (fun x => thetaCuspReflectedLikelihoodCumulantJetTwo x t)
      (c5LikelihoodScaleMixedJetTwo u t) u := by
  have hp := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hplus).comp u
    ((hasDerivAt_id u).add_const t)
  have hm := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hminus).comp u
    ((hasDerivAt_id u).sub_const t)
  exact (hp.neg.sub hm).congr_deriv (by
    unfold c5LikelihoodScaleMixedJetTwo
    ring)

end

end RHTower
