import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5TangentSaturatedSecondChannel
import GaloisForLFunctions.RHTower.ThetaCuspReflectedLikelihoodSixJetOrientation

/-!
# Mixed likelihood trapezoid coupling for fixed-action C5

The first mixed-centre likelihood channel is the integral of negative third source curvature over
the reflected packet.  Negative third source curvature is convex because the fifth source jet is
strictly negative.  Upper Hermite--Hadamard therefore bounds the first mixed-centre channel by
displacement times the second one.

This exact source coupling repairs one freedom exposed by the C5 tangent cone audit: near the seam,
the adverse mixed-centre channel cannot saturate the master curvature loss independently of the
favorable third-jet channel.
-/

open Set MeasureTheory

namespace RHTower

noncomputable section

/-- Negative fourth likelihood source jet is strictly increasing on the physical half-line. -/
theorem strictMonoOn_neg_thetaCuspLikelihoodSourceLogPartitionJetFour :
    StrictMonoOn (-thetaCuspLikelihoodSourceLogPartitionJetFour) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
      (thetaCuspLikelihoodCoordinate_pos hx)).neg.continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hderiv := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour
      (thetaCuspLikelihoodCoordinate_pos hx.le)).neg
    rw [hderiv.deriv]
    exact neg_pos.mpr (thetaCuspLikelihoodSourceLogPartitionJetFive_neg hx.le)

/-- Negative third likelihood source jet is convex on the physical half-line. -/
theorem convexOn_neg_thetaCuspLikelihoodSourceLogPartitionJetThree :
    ConvexOn ℝ (Ici 0) (-thetaCuspLikelihoodSourceLogPartitionJetThree) := by
  refine (StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) ?_ ?_).convexOn
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos hx)).neg.continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    rw [interior_Ici] at hx hy
    have hxderiv := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos hx.le)).neg
    have hyderiv := (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos hy.le)).neg
    rw [hxderiv.deriv, hyderiv.deriv]
    exact strictMonoOn_neg_thetaCuspLikelihoodSourceLogPartitionJetFour
      (show x ∈ Ici 0 by simpa only [mem_Ici] using hx.le)
      (show y ∈ Ici 0 by simpa only [mem_Ici] using hy.le) hxy

/-- **Upper mixed-jet trapezoid coupling.** The declaration is closed; its implications specify
the same-half-line domain and introduce no route premise or numeric input. -/
theorem c5LikelihoodScaleMixedJetOne_le_mul_mixedJetTwo :
    ∀ u t : ℝ, 0 < t → t ≤ u →
      c5LikelihoodScaleMixedJetOne u t ≤ t * c5LikelihoodScaleMixedJetTwo u t := by
  intro u t ht htu
  let g := -thetaCuspLikelihoodSourceLogPartitionJetTwo
  let k := -thetaCuspLikelihoodSourceLogPartitionJetThree
  have ha : 0 ≤ u - t := by linarith
  have hab : u - t < u + t := by linarith
  have hcont : ContinuousOn k (Icc (u - t) (u + t)) := by
    intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree
      (thetaCuspLikelihoodCoordinate_pos (le_trans ha hx.1))).neg.continuousAt.continuousWithinAt
  have hint : IntervalIntegrable k volume (u - t) (u + t) :=
    hcont.intervalIntegrable_of_Icc hab.le
  have hconv : ConvexOn ℝ (Icc (u - t) (u + t)) k := by
    refine ⟨convex_Icc (u - t) (u + t), ?_⟩
    intro x hx y hy a b ha' hb' hab'
    exact convexOn_neg_thetaCuspLikelihoodSourceLogPartitionJetThree.2
      (le_trans ha hx.1) (le_trans ha hy.1) ha' hb' hab'
  have htrap := GaloisForLFunctions.ConvexOn.integral_le_trapezoid hab hconv hint
  have hftc : (∫ x in (u - t)..(u + t), k x) = g (u + t) - g (u - t) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      exact (hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
        (thetaCuspLikelihoodCoordinate_pos (by
          rw [uIcc_of_le hab.le] at hx
          exact le_trans ha hx.1))).neg
    · exact hint
  rw [hftc] at htrap
  unfold c5LikelihoodScaleMixedJetOne c5LikelihoodScaleMixedJetTwo
  dsimp only [g, k] at htrap ⊢
  simp only [Pi.neg_apply] at htrap
  nlinarith

end

end RHTower
