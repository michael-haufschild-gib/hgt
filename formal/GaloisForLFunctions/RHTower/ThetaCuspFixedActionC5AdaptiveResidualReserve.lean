import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodMixedTrapezoid

/-!
# Exact residual reserve after adaptive C5 cooling

The adaptive-reserved lower margin is not the literal completed margin.  Their exact difference is
a manifestly positive third-likelihood-channel residual on the structural physical tail.  Thus the
correct surviving endpoint is residual-aware domination, not positivity of the adaptive lower
bound.  No numerical result enters this module.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Exact third-channel compensation omitted by the adaptive reserved lower margin. -/
def c5CompletedAdaptiveResidualReserve (u t : ℝ) : ℝ :=
  5 * t ^ (2 : ℕ) *
    (thetaCuspCompletedReflectedCumulantJetOne u t *
        (c5LikelihoodScaleMixedJetTwo u t -
          c5LikelihoodAdaptiveMasterCurvature u t) -
      thetaCuspReflectedLikelihoodCumulantJetThree u t *
        c5CompletedScaleActionJetOne u t)

/-- Literal completed compensation splits exactly into the false adaptive endpoint and the omitted
third-channel residual. -/
theorem c5CompletedCompensationMargin_eq_adaptive_add_residual
    (u t : ℝ) :
    c5CompletedCompensationMargin u t =
      c5CompletedAdaptiveReservedCompensationMargin u t +
        c5CompletedAdaptiveResidualReserve u t := by
  unfold c5CompletedCompensationMargin
    c5CompletedAdaptiveReservedCompensationMargin
    c5CompletedAdaptiveResidualReserve
    c5CompletedLowerJetCompensationMargin
    c5CompletedVelocitySlopeCenterNumerator
    c5CompletedVelocitySlopeLowerJetNumerator
    thetaCuspCompletedReflectedCumulantJetThree
    c5CompletedScaleMixedJetTwo
  ring

/-- Exact residual is strictly positive throughout the structural physical tail. -/
theorem c5CompletedAdaptiveResidualReserve_pos
    {u t : ℝ} (ht : 0 < t) (htu : t < u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u) :
    0 < c5CompletedAdaptiveResidualReserve u t := by
  let a := thetaCuspCompletedReflectedCumulantJetOne u t
  let n := c5LikelihoodScaleMixedJetTwo u t
  let z := c5LikelihoodAdaptiveMasterCurvature u t
  let c := thetaCuspReflectedLikelihoodCumulantJetThree u t
  let s := c5CompletedScaleActionJetOne u t
  have ha : 0 < a := by
    simpa only [a] using c5CompletedActionJetOne_pos ht htu
  have hnz : 0 < n - z := by
    have h := adaptiveMasterCurvature_lt_c5LikelihoodScaleMixedJetTwo ht.le htu.le
    simpa only [n, z] using sub_pos.mpr h
  have hc : c < 0 := by
    simpa only [c] using thetaCuspReflectedLikelihoodCumulantJetThree_neg ht htu.le
  have hs : 0 < s := by
    simpa only [s] using c5CompletedScaleActionJetOne_pos ht htu hscale
  have han : 0 < a * (n - z) := mul_pos ha hnz
  have hcs : c * s < 0 := mul_neg_of_neg_of_pos hc hs
  have hinner : 0 < a * (n - z) - c * s := by
    linarith
  unfold c5CompletedAdaptiveResidualReserve
  dsimp only [a, n, z, c, s] at hinner ⊢
  positivity

/-- Exact replacement endpoint: completed positivity is equivalent to the adaptive margin paying
only the negative of the strictly positive residual. -/
theorem c5CompletedCompensationMargin_pos_iff_adaptive_gt_neg_residual
    (u t : ℝ) :
    0 < c5CompletedCompensationMargin u t ↔
      -c5CompletedAdaptiveResidualReserve u t <
        c5CompletedAdaptiveReservedCompensationMargin u t := by
  rw [c5CompletedCompensationMargin_eq_adaptive_add_residual]
  constructor <;> intro h <;> linarith

end

end RHTower
