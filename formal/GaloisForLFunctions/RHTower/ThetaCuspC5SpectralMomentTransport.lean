import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction

/-!
# Spectral moment transport in the complete C5 compensation

Positive mass and a fixed first moment permit unbounded second moments. The exact two-atom
family below proves this unconditionally. Its effect on the C5 source is clarified by an exact
left-curvature perturbation identity: the full compensation is affine in that curvature when
lower jets are retained, and its curvature response contains a separate center-slope contrast.

These are exact algebraic results, with no computational evidence used in their proofs.
The numerical counterfactual theta-tail signs motivating the investigation are not theorems
of this module. Neither the actual theta compensation inequality nor RH is asserted here.
-/

namespace RHTower
noncomputable section

/-- A formal left-endpoint second-derivative increment, holding lower jets fixed. This is a jet-space operation; finite spectral contamination also changes other endpoint jets. -/
def c5LeftCurvaturePerturbation (d : C5LikelihoodAffineData) (z : ℝ) :
    C5LikelihoodAffineData := { d with db := d.db-z, dm := d.dm+z }

/-- Exact lower transport response to the second-derivative increment. -/
theorem c5LeftCurvaturePerturbation_velocityCenter (d : C5LikelihoodAffineData) (z l : ℝ) :
    (c5LeftCurvaturePerturbation d z).velocityCenter l = d.velocityCenter l +
      l*d.t*z*(d.jetOne l+d.scaleAction l) := by
  simp only [c5LeftCurvaturePerturbation, C5LikelihoodAffineData.velocityCenter,
    C5LikelihoodAffineData.jetOne, C5LikelihoodAffineData.jetTwo,
    C5LikelihoodAffineData.scaleAction, C5LikelihoodAffineData.scaleMixedOne,
    C5LikelihoodAffineData.affine]
  ring

/-- Exact first homotopy-derivative response, including its mixed source term. -/
theorem c5LeftCurvaturePerturbation_velocityCenterOne (d : C5LikelihoodAffineData) (z l : ℝ) :
    (c5LeftCurvaturePerturbation d z).velocityCenterOne l = d.velocityCenterOne l +
      d.t*z*(d.jetOne l+d.scaleAction l+l*(d.da+d.ds)) := by
  simp only [c5LeftCurvaturePerturbation, C5LikelihoodAffineData.velocityCenterOne,
    C5LikelihoodAffineData.jetOne, C5LikelihoodAffineData.jetTwo,
    C5LikelihoodAffineData.scaleAction, C5LikelihoodAffineData.scaleMixedOne,
    C5LikelihoodAffineData.affine]
  ring

/-- Curvature response depends on the center-to-right slope contrast, not only left curvature. -/
theorem c5LeftCurvaturePerturbation_velocityCenterTwo (d : C5LikelihoodAffineData) (z : ℝ) :
    (c5LeftCurvaturePerturbation d z).velocityCenterTwo = d.velocityCenterTwo +
      2*d.t*z*(d.da+d.ds) := by
  simp only [c5LeftCurvaturePerturbation, C5LikelihoodAffineData.velocityCenterTwo]
  ring

/-- Exact all-homotopy affine sensitivity of the complete signed compensation. No channel is discarded. -/
theorem c5LeftCurvaturePerturbation_compensationThree (d : C5LikelihoodAffineData) (z l : ℝ) :
    (c5LeftCurvaturePerturbation d z).compensationThree l = d.compensationThree l -
      d.t*z*((l*d.boseCoefficientThree l+3*d.boseCoefficientTwo l)*
        (d.jetOne l+d.scaleAction l)+
        (3*l*d.boseCoefficientTwo l+6*d.boseCoefficientOne l)*(d.da+d.ds)) := by
  change -(d.boseCoefficientThree l*(c5LeftCurvaturePerturbation d z).velocityCenter l+
    3*d.boseCoefficientTwo l*(c5LeftCurvaturePerturbation d z).velocityCenterOne l+
    3*d.boseCoefficientOne l*(c5LeftCurvaturePerturbation d z).velocityCenterTwo) = _
  rw [c5LeftCurvaturePerturbation_velocityCenter,
    c5LeftCurvaturePerturbation_velocityCenterOne,
    c5LeftCurvaturePerturbation_velocityCenterTwo]
  unfold C5LikelihoodAffineData.compensationThree
  ring

/-- Exact positive quadratic term and retained contrast debit. For endpoint data, D=-da, C=-(da+ds)/2, S=-db, and E=(-db-dm)/2 give H2=2D^2+4tDE-4C(D+tS). -/
theorem c5VelocityCenterTwo_contrast_decomposition (d : C5LikelihoodAffineData) :
    d.velocityCenterTwo = 2*(-d.da)^2+
      4*d.t*(-d.da)*((-d.db-d.dm)/2)-
      4*(-(d.da+d.ds)/2)*((-d.da)+d.t*(-d.db)) := by
  unfold C5LikelihoodAffineData.velocityCenterTwo
  ring

/-- Positive two-atom probability weight; the remote node is 4+z^2. -/
def c5MomentEscapeWeight (c z : ℝ) : ℝ := (c^2/(1+c^2))/(1+z^2)

/-- Both atom weights are nonnegative and sum to one for every real parameter. -/
theorem c5MomentEscapeWeight_bounds (c z : ℝ) :
    0 ≤ c5MomentEscapeWeight c z ∧ c5MomentEscapeWeight c z ≤ 1 := by
  unfold c5MomentEscapeWeight
  constructor
  · positivity
  · apply (div_le_one (by positivity : 0 < 1+z^2)).2
    have h : c^2/(1+c^2) ≤ 1 :=
      (div_le_one (by positivity : 0 < 1+c^2)).2 (by linarith)
    nlinarith [sq_nonneg z]

/-- The first moment is independent of the remote node position. -/
theorem c5MomentEscape_firstMoment (c z : ℝ) :
    (1-c5MomentEscapeWeight c z)*3+c5MomentEscapeWeight c z*(4+z^2) =
      3+c^2/(1+c^2) := by
  have hc : 1+c^2 ≠ 0 := by positivity
  have hz : 1+z^2 ≠ 0 := by positivity
  unfold c5MomentEscapeWeight
  field_simp
  ring

/-- Exact growth of the second moment at fixed mass and first moment. -/
theorem c5MomentEscape_secondMoment (c z : ℝ) :
    (1-c5MomentEscapeWeight c z)*3^2+c5MomentEscapeWeight c z*(4+z^2)^2 =
      9+c^2/(1+c^2)*(7+z^2) := by
  have hc : 1+c^2 ≠ 0 := by positivity
  have hz : 1+z^2 ≠ 0 := by positivity
  unfold c5MomentEscapeWeight
  field_simp
  ring

/-- No second-moment ceiling follows from unit positive mass, support at least three, and fixed first moment 16/5. -/
theorem c5MomentEscape_secondMoment_unbounded (R : ℝ) :
    ∃ z : ℝ, R <
      (1-c5MomentEscapeWeight (1/2) z)*3^2+
        c5MomentEscapeWeight (1/2) z*(4+z^2)^2 := by
  refine ⟨5*R, ?_⟩
  rw [c5MomentEscape_secondMoment]
  norm_num
  nlinarith [sq_nonneg (R-1/10)]

/-- A complete positive two-atom witness: fixed mass and mean, fixed support gap,
and second moment above any prescribed real ceiling. -/
theorem c5MomentEscape_exists_fixedMean_unboundedSecond (R : ℝ) :
    ∃ w g : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ 3 ≤ g ∧
      (1-w)*3+w*g = 16/5 ∧ R < (1-w)*3^2+w*g^2 := by
  obtain ⟨z, hz⟩ := c5MomentEscape_secondMoment_unbounded R
  have hw := c5MomentEscapeWeight_bounds (1/2) z
  refine ⟨c5MomentEscapeWeight (1/2) z, 4+z^2, hw.1, hw.2, ?_, ?_, hz⟩
  · nlinarith [sq_nonneg z]
  · rw [c5MomentEscape_firstMoment]
    norm_num

end
end RHTower
