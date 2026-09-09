import GaloisForLFunctions.HTGeometry.FokasLenellsContourFundamental
import GaloisForLFunctions.HTGeometry.FokasLenellsContourScattering

/-!
# The uniformizing gauge at both endpoints of every contour ray

The spatial gauge is carried through actual oscillating evolutions and
their limits. Both the initial gauge and the limiting diagonal gauge are
retained, so the signed-z scattering comparison has no assumed endpoint
or decay identity.
-/

open Complex Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def contourInteractionMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  contourConjugator vertical negative * interactionFundamentalMatrix (contourSource q vertical) κ x *
    contourConjugator vertical negative

def contourAsymptoticMatrix (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) (left : Bool) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  contourConjugator vertical negative * originalAsymptoticMatrix (contourSource q vertical) κ left *
    contourConjugator vertical negative

def contourOscillatingGauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  diagonalFrame (contourSquaredParameter vertical κ) x *
    uniformizationGauge (deriv q x) (contourParameter vertical negative κ) *
      diagonalFrame (-(contourSquaredParameter vertical κ)) x

theorem contourInteractionMatrix_eq_diagonal_mul (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    contourInteractionMatrix q vertical negative κ x =
      diagonalFrame (contourSquaredParameter vertical κ) x * contourFundamentalMatrix q vertical negative κ x := by
  rw [diagonalFrame_contour_conjugation, contourInteractionMatrix,
    interactionFundamentalMatrix_eq_diagonal_mul, contourFundamentalMatrix]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

/-- Pauli transport preserves the existing proved endpoint limits of the interaction evolution. -/
theorem contourInteractionMatrix_oriented_tendsto (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) :
    Tendsto (fun x => contourInteractionMatrix q vertical negative κ (if left then -x else x)) atTop
      (𝓝 (contourAsymptoticMatrix q vertical negative κ left)) :=
  ((interactionFundamentalMatrix_oriented_tendsto (contourSource q vertical) κ left).const_mul
    (contourConjugator vertical negative)).mul_const (contourConjugator vertical negative)

/-- The exact orbit gauge holds before passing to either spatial infinity. -/
theorem uniformizedOrbitMatrix_contour_gauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) (x : ℝ) :
    uniformizedOrbitMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (contourSquaredParameter vertical κ) left x *
      uniformizationGauge (deriv q 0) (contourParameter vertical negative κ) =
    contourOscillatingGauge q vertical negative κ (if left then -x else x) *
      contourInteractionMatrix q vertical negative κ (if left then -x else x) := by
  rw [uniformizedOrbitMatrix_eq_diagonal_mul, Matrix.mul_assoc,
    uniformizedFundamentalMatrix_contour_gauge, ← Matrix.mul_assoc,
    contourInteractionMatrix_eq_diagonal_mul]
  unfold contourOscillatingGauge
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (diagonalFrame (-(contourSquaredParameter vertical κ)) _),
    diagonalFrame_neg_inverse, one_mul]

/-- The gauge error on each ray is exactly the decaying spatial derivative norm. -/
theorem contourOscillatingGauge_difference_norm (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    ‖contourOscillatingGauge q vertical negative κ x - uniformizationGauge 0 (contourParameter vertical negative κ)‖ =
      ‖deriv q x‖ := by
  have he : contourOscillatingGauge q vertical negative κ x - uniformizationGauge 0 (contourParameter vertical negative κ) =
      diagonalFrame (contourSquaredParameter vertical κ) x *
        (uniformizationGauge (deriv q x) (contourParameter vertical negative κ) -
          uniformizationGauge 0 (contourParameter vertical negative κ)) *
            diagonalFrame (-(contourSquaredParameter vertical κ)) x := by
    rw [mul_sub, sub_mul, diagonalFrame_gauge_zero_conjugation]
    rfl
  rw [he]
  have hn := diagonalFrame_conjugation_norm (-(contourSquaredParameter vertical κ)) x
    (uniformizationGauge (deriv q x) (contourParameter vertical negative κ) -
      uniformizationGauge 0 (contourParameter vertical negative κ))
  simp only [neg_neg] at hn
  rw [hn, uniformizationGauge_difference_norm]

/-- Both endpoint gauges converge on both real and imaginary rays. -/
theorem contourOscillatingGauge_tendsto (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) :
    Tendsto (fun x => contourOscillatingGauge q vertical negative κ (if left then -x else x)) atTop
      (𝓝 (uniformizationGauge 0 (contourParameter vertical negative κ))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [contourOscillatingGauge_difference_norm]
  have hd : Tendsto (fun x => deriv q x) atTop (𝓝 0) := by
    have hh := (SchwartzMap.derivCLM ℂ ℂ q).tendsto_cocompact.mono_left atTop_le_cocompact
    change Tendsto (fun x => SchwartzMap.derivCLM ℂ ℂ q x) atTop _ at hh
    simpa only [SchwartzMap.derivCLM_apply] using hh
  have hdneg : Tendsto (fun x => deriv q (-x)) atTop (𝓝 0) := by
    have hl := (SchwartzMap.derivCLM ℂ ℂ q).tendsto_cocompact.mono_left atBot_le_cocompact
    simpa only [Function.comp_def, SchwartzMap.derivCLM_apply] using hl.comp tendsto_neg_atTop_atBot
  cases left
  · simpa using hd.norm
  · simpa using hdneg.norm

/-- The full signed-z endpoint identity follows from the two actual limits. -/
theorem uniformizedAsymptoticMatrix_contour_gauge_endpoint (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) :
    uniformizedAsymptoticMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (contourSquaredParameter vertical κ) left *
      uniformizationGauge (deriv q 0) (contourParameter vertical negative κ) =
    uniformizationGauge 0 (contourParameter vertical negative κ) *
      contourAsymptoticMatrix q vertical negative κ left := by
  have hu := (uniformizedOrbitMatrix_tendsto (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (contourSquaredParameter vertical κ) left).mul_const
      (uniformizationGauge (deriv q 0) (contourParameter vertical negative κ))
  have ho := (contourOscillatingGauge_tendsto q vertical negative κ left).mul
    (contourInteractionMatrix_oriented_tendsto q vertical negative κ left)
  simp only [uniformizedOrbitMatrix_contour_gauge] at hu
  exact tendsto_nhds_unique hu ho

theorem uniformizationGauge_contour_isUnit_det (u : ℂ) (vertical negative : Bool) (κ : ℝ) :
    IsUnit (uniformizationGauge u (contourParameter vertical negative κ)).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [det_uniformizationGauge]
  exact mul_ne_zero (by norm_num) (contourParameter_ne_zero vertical negative κ)

/-- Solving the endpoint identity preserves its initial gauge factor. -/
theorem uniformizedAsymptoticMatrix_contour_gauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ : ℝ) (left : Bool) :
    uniformizedAsymptoticMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (contourSquaredParameter vertical κ) left =
    uniformizationGauge 0 (contourParameter vertical negative κ) *
      contourAsymptoticMatrix q vertical negative κ left *
        (uniformizationGauge (deriv q 0) (contourParameter vertical negative κ))⁻¹ := by
  have he := congrArg (fun M => M*(uniformizationGauge (deriv q 0) (contourParameter vertical negative κ))⁻¹)
    (uniformizedAsymptoticMatrix_contour_gauge_endpoint q vertical negative κ left)
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (uniformizationGauge_contour_isUnit_det _ _ _ _), mul_one] at he
  exact he

end
end GaloisForLFunctions.HTGeometry.FokasLenells
