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
        thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ (2 : ℕ))
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

/-- If a finite section loses nonnegativity while its initial data are nonnegative, its outgoing
curvature channel must be negative somewhere on the same aperture interval. -/
theorem exists_thetaCuspGaussianApertureRatioCurvature_boundary_neg_of_finiteSection_failure
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0) (J : ℕ)
    (hinit : ∀ j, j ≤ J →
      0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    {j : ℕ} (hj : j ≤ J) {lambda : ℝ} (hlambda : lambda ∈ Icc a b)
    (hneg : thetaCuspGaussianApertureRatioCurvature lambda j < 0) :
    ∃ eta ∈ Icc a b,
      thetaCuspGaussianApertureRatioCurvature eta (J + 1) < 0 := by
  by_contra hboundaryNeg
  have hboundary : ∀ eta ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature eta (J + 1) := by
    intro eta heta
    by_contra hnot
    exact hboundaryNeg ⟨eta, heta, lt_of_not_ge hnot⟩
  have hsection :=
    thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
      hab hb J hinit hboundary j hj lambda hlambda
  exact (not_lt_of_ge hsection) hneg

/-- **Failure escapes to arbitrarily high degree.**  Starting from globally nonnegative initial
curvature, one negative value at any finite degree forces a negative outgoing channel beyond every
larger finite cutoff. -/
theorem forall_exists_thetaCuspGaussianApertureRatioCurvature_highDegree_neg_of_failure
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0)
    (hinit : ∀ j, 0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    {j : ℕ} {lambda : ℝ} (hlambda : lambda ∈ Icc a b)
    (hneg : thetaCuspGaussianApertureRatioCurvature lambda j < 0) :
    ∀ J, j ≤ J → ∃ eta ∈ Icc a b,
      thetaCuspGaussianApertureRatioCurvature eta (J + 1) < 0 := by
  intro J hj
  exact
    exists_thetaCuspGaussianApertureRatioCurvature_boundary_neg_of_finiteSection_failure
      hab hb J (fun k _hk => hinit k) hj hlambda hneg

/-- A cofinal family of nonnegative outgoing channels discharges every finite boundary hypothesis
in the curvature maximum principle. -/
theorem thetaCuspGaussianApertureRatioCurvature_nonnegative_of_cofinalBoundary
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0)
    (hinit : ∀ j, 0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    (hboundary : ∀ j, ∃ J, j ≤ J ∧
      ∀ lambda ∈ Icc a b,
        0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1)) :
    ∀ j, ∀ lambda ∈ Icc a b,
      0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j := by
  intro j lambda hlambda
  obtain ⟨J, hj, hJ⟩ := hboundary j
  exact
    thetaCuspGaussianApertureRatioCurvature_finiteSection_nonnegative
      hab hb J (fun k _hk => hinit k) hJ j hj lambda hlambda

/-- Under globally nonnegative initial curvature, the cofinal outgoing-boundary condition is
exactly equivalent to global curvature preservation on the aperture interval. -/
theorem thetaCuspGaussianApertureRatioCurvature_nonnegative_iff_cofinalBoundary
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0)
    (hinit : ∀ j, 0 ≤ thetaCuspGaussianApertureRatioCurvature a j) :
    (∀ j, ∀ lambda ∈ Icc a b,
        0 ≤ thetaCuspGaussianApertureRatioCurvature lambda j) ↔
      ∀ j, ∃ J, j ≤ J ∧
        ∀ lambda ∈ Icc a b,
          0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1) := by
  constructor
  · intro hglobal j
    exact ⟨j, le_rfl, hglobal (j + 1)⟩
  · exact
      thetaCuspGaussianApertureRatioCurvature_nonnegative_of_cofinalBoundary
        hab hb hinit

/-- The physical Gaussian-aperture balance inherits the cofinal-boundary discharge. -/
theorem thetaCuspGaussianApertureBalance_nonnegative_of_cofinalBoundary
    {a b : ℝ} (hab : a ≤ b) (hb : b < 0)
    (hinit : ∀ j, 0 ≤ thetaCuspGaussianApertureRatioCurvature a j)
    (hboundary : ∀ j, ∃ J, j ≤ J ∧
      ∀ lambda ∈ Icc a b,
        0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (J + 1))
    {lambda : ℝ} (hlambda : lambda ∈ Icc a b) :
    0 ≤ thetaCuspGaussianApertureBalance lambda := by
  rw [thetaCuspGaussianApertureBalance_eq_ratioCurvature]
  exact mul_nonneg (by norm_num)
    (thetaCuspGaussianApertureRatioCurvature_nonnegative_of_cofinalBoundary
      hab hb hinit hboundary 0 lambda hlambda)

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
            (x ^ (2 : ℕ) -
                thetaCuspGaussianApertureResponseCenteredSaddleHeight
                  lambda hlambda j ^ (2 : ℕ)) ^ (2 : ℕ) *
              x ^ (2 * j) *
                thetaCuspGaussianApertureLeadingChannelWeight lambda x) ≤
        thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1)) ∧
    (∀ (lambda : ℝ) (hlambda : lambda ≤ 0), ∀ j : ℕ,
      let s := thetaCuspGaussianApertureResponseCenteredSaddleHeight
        lambda hlambda j
      (3 * Real.pi) * s ^ (4 : ℕ) *
          thetaCuspGaussianApertureHigherAtomHalfMoment lambda j ≤
        (16 / 2997 : ℝ) * (3 * Real.pi) * s ^ (4 : ℕ) *
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
