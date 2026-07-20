import GaloisForLFunctions.HTGeometry.LinearDifferentialCone
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureHeightLocalizedContraction

/-!
# Finite-section maximum principle for the completed theta Gaussian curvature flow

The exact Gaussian-aperture ratio-curvature equation is triangular and cooperative in the degree
direction.  The source-independent integrating-factor theorem therefore converts its local
boundary derivative into a genuine maximum principle for every finite degree section.  A finite
section can lose positivity only through its single outgoing curvature coordinate.
-/

open Set

namespace RHTower

noncomputable section

/-- **Completed-theta finite-section curvature maximum principle.**  On a negative aperture
interval, nonnegative initial curvature through degree `J` and a nonnegative outgoing curvature
channel at degree `J+1` force the entire finite section to remain nonnegative. -/
theorem thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0) (J : ℕ)
    (hinit : ∀ j, j ≤ J →
      0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    (hboundary : ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1)) :
    ∀ j, j ≤ J → ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j := by
  apply HTGeometry.finiteTriangularCone_nonnegative hab J
    (S := fun j lambda => thetaCuspGaussianApertureRatioCurvature lambda j)
    (A := fun j lambda =>
      4 * (thetaCuspGaussianApertureGammaRatio lambda j -
        thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2)
    (B := fun j lambda =>
      thetaCuspGaussianApertureGammaShape (j + 3) *
        thetaCuspGaussianApertureGammaRatio lambda (j + 2))
    (R := fun j lambda =>
      thetaCuspGaussianApertureRatioCurvatureReaction lambda j)
  · intro j _hj lambda hlambda
    have hlambdaNeg : lambda < 0 := lt_of_le_of_lt hlambda.2 hb
    exact (hasDerivAt_thetaCuspGaussianApertureRatioCurvature
      hlambdaNeg j).continuousAt.continuousWithinAt
  · intro j _hj lambda hlambda
    have hlambdaNeg : lambda < 0 := lt_of_le_of_lt hlambda.2 hb
    have hq0 : ContinuousAt
        (fun eta => thetaCuspGaussianApertureGammaRatio eta j) lambda :=
      (hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambdaNeg j).continuousAt
    have hq1 : ContinuousAt
        (fun eta => thetaCuspGaussianApertureGammaRatio eta (j + 1)) lambda :=
      (hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambdaNeg (j + 1)).continuousAt
    have hq2 : ContinuousAt
        (fun eta => thetaCuspGaussianApertureGammaRatio eta (j + 2)) lambda :=
      (hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambdaNeg (j + 2)).continuousAt
    unfold thetaCuspGaussianApertureRatioCurvatureReaction
    fun_prop
  · intro j _hj lambda hlambda
    have hlambdaNeg : lambda < 0 := hlambda.2.trans hb
    exact (hasDerivAt_thetaCuspGaussianApertureRatioCurvature
      hlambdaNeg j).differentiableAt
  · intro j _hj lambda hlambda
    have hlambdaNeg : lambda < 0 := hlambda.2.trans hb
    rw [deriv_thetaCuspGaussianApertureRatioCurvature_eq hlambdaNeg j]
    ring
  · intro j _hj lambda _hlambda
    positivity
  · intro j _hj lambda hlambda
    have hlambdaNeg : lambda < 0 := hlambda.2.trans hb
    exact mul_nonneg
      (thetaCuspGaussianApertureGammaShape_pos (j + 3)).le
      (thetaCuspGaussianApertureGammaRatio_pos hlambdaNeg.le (j + 2)).le
  · exact hinit
  · exact hboundary

/-- The physical GABTC coordinate is protected on a finite interval by nonnegative initial
curvature through degree `J` and one nonnegative boundary channel at degree `J+1`. -/
theorem thetaCuspGaussianApertureBalance_nonnegative_of_finiteSection
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0) (J : ℕ)
    (hinit : ∀ j, j ≤ J →
      0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    (hboundary : ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1))
    (lambda : ℝ) (hlambda : lambda ∈ Icc a b) :
    0 ≤ thetaCuspGaussianApertureBalance lambda := by
  rw [thetaCuspGaussianApertureBalance_eq_ratioCurvature]
  exact mul_nonneg (by norm_num)
    (thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
      hab hb J hinit hboundary 0 (Nat.zero_le J) lambda hlambda)

/-- **Curvature-transport and dominant-channel localization capstone.**  The completed theta
Gaussian flow simultaneously has finite-section cone preservation, exact response-centered
leading-channel concentration, and a resolution-safe contraction of the entire higher-atom tail
against the literal first atom. -/
theorem thetaCuspGaussianAperture_curvatureTransportLocalizationCapstone
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0) (J : ℕ)
    (hinit : ∀ j, j ≤ J →
      0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    (hboundary : ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1)) :
    (∀ j, j ≤ J → ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j) ∧
    (∀ (lambda : ℝ) (hlambda : lambda ≤ 0), ∀ j : ℕ,
      (3 * Real.pi) *
          (∫ x : ℝ in Ioi 0,
            (x ^ 2 -
                thetaCuspGaussianApertureResponseCenteredSaddleHeight
                  lambda hlambda j ^ 2) ^ 2 *
              x ^ (2 * j) *
                thetaCuspGaussianApertureLeadingChannelWeight lambda x) ≤
        thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)) ∧
    (∀ (lambda : ℝ) (hlambda : lambda ≤ 0), ∀ j : ℕ,
      let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight
        lambda hlambda j
      (3 * Real.pi) * s ^ 4 *
          thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
        (16 / 2997 : ℝ) * (3 * Real.pi) * s ^ 4 *
            thetaCuspHigherAtomExactHeightDamping (s / 2) *
              thetaCuspGaussianApertureFirstAtomHalfMoment lambda j +
          (32 / 2997 : ℝ) *
            thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1)) := by
  refine ⟨thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
    hab hb J hinit hboundary, ?_, ?_⟩
  · intro lambda hlambda j
    exact thetaCuspGaussianApertureLeadingChannel_canonicalSaddleError_le hlambda j
  · intro lambda hlambda j
    exact thetaCuspGaussianApertureHigherAtomHalfMoment_canonical_scaled_le_firstAtom
      hlambda j

end

end RHTower
