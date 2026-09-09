import GaloisForLFunctions.HTGeometry.FokasLenellsContourGaugeEndpoints
import GaloisForLFunctions.HTGeometry.FokasLenellsRegularOrigin

/-!
# The exact scattering gauge on the entire squared spectral line

The two independently constructed scattering matrices are compared on
all contour rays by their actual endpoint limits. In particular this
identifies the negative-z uniformized data with the imaginary-ray data,
including the exchange of the transmission entries.
-/

open Complex Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem contour_conjugator_inverse (vertical negative : Bool) :
    (contourConjugator vertical negative)⁻¹ = contourConjugator vertical negative :=
  Matrix.inv_eq_left_inv (contourConjugator_square vertical negative)

/-- The transported actual endpoint connection is exactly the previously constructed contour scattering matrix. -/
theorem contourAsymptoticMatrix_connection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    contourAsymptoticMatrix q vertical negative κ false *
      (contourAsymptoticMatrix q vertical negative κ true)⁻¹ = contourScatteringMatrix q vertical negative κ := by
  simp only [contourAsymptoticMatrix, originalAsymptoticMatrix, Bool.false_eq_true, ↓reduceIte,
    Matrix.mul_inv_rev, contour_conjugator_inverse, contourScatteringMatrix, scatteringMatrix,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (contourConjugator vertical negative) (contourConjugator vertical negative),
    contourConjugator_square, one_mul]

/-- The exact scattering gauge is valid on all four nonzero contour rays. -/
theorem uniformizedScatteringMatrix_contour_gauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    uniformizedScatteringMatrix (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (contourSquaredParameter vertical κ) =
    uniformizationGauge 0 (contourParameter vertical negative κ) *
      contourScatteringMatrix q vertical negative κ *
        (uniformizationGauge 0 (contourParameter vertical negative κ))⁻¹ := by
  have hi := Matrix.nonsing_inv_mul _ (uniformizationGauge_contour_isUnit_det (deriv q 0) vertical negative κ)
  have hdouble := Matrix.nonsing_inv_nonsing_inv _
    (uniformizationGauge_contour_isUnit_det (deriv q 0) vertical negative κ)
  simp only [uniformizedScatteringMatrix,
    uniformizedAsymptoticMatrix_contour_gauge q vertical negative κ false,
    uniformizedAsymptoticMatrix_contour_gauge q vertical negative κ true,
    Matrix.mul_inv_rev, hdouble, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((uniformizationGauge (deriv q 0) (contourParameter vertical negative κ))⁻¹),
    hi, one_mul]
  rw [← Matrix.mul_assoc (contourAsymptoticMatrix q vertical negative κ false),
    contourAsymptoticMatrix_connection]

/-- All four regularized matrix entries have the paper's exact reciprocal gauge factors on every ray. -/
theorem regularScatteringMatrix_contour_amplitudes (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    regularScatteringMatrix q (contourSquaredParameter vertical κ) =
      !![contourTransmission q vertical negative κ,
          -contourReverseReflectionAmplitude q vertical negative κ / (2*contourParameter vertical negative κ);
        -2*contourParameter vertical negative κ*contourReflectionAmplitude q vertical negative κ,
          contourReverseTransmission q vertical negative κ] := by
  rw [regularScatteringMatrix, uniformizedScatteringMatrix_contour_gauge]
  have hk := contourParameter_ne_zero vertical negative κ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uniformizationGauge, contourTransmission, contourReverseTransmission, contourReflectionAmplitude,
      contourReverseReflectionAmplitude, Matrix.inv_def, Matrix.det_fin_two, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> field_simp

/-- Normalization by transmission preserves the exact contour gauge formulas without any nonvanishing premise. -/
theorem regularReflectionCoefficients_contour_gauge (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    regularReflectionCoefficient q (contourSquaredParameter vertical κ) =
      -(2*contourParameter vertical negative κ)*
        (contourReflectionAmplitude q vertical negative κ / contourTransmission q vertical negative κ) ∧
    regularReverseReflectionCoefficient q (contourSquaredParameter vertical κ) =
      -contourReverseReflectionAmplitude q vertical negative κ /
        (2*contourParameter vertical negative κ*contourReverseTransmission q vertical negative κ) := by
  have hS := regularScatteringMatrix_contour_amplitudes q vertical negative κ
  constructor
  · rw [regularReflectionCoefficient, hS]
    change (-2*contourParameter vertical negative κ*contourReflectionAmplitude q vertical negative κ) /
      contourTransmission q vertical negative κ = _
    ring
  · rw [regularReverseReflectionCoefficient, hS]
    change (-contourReverseReflectionAmplitude q vertical negative κ /
      (2*contourParameter vertical negative κ)) / contourReverseTransmission q vertical negative κ = _
    rw [div_div]

/-- On negative z the imaginary-ray transform exchanges the transmissions and inserts the exact imaginary reflection factors. -/
theorem regularScatteringMatrix_negative_exp (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    regularScatteringMatrix q (-((Real.exp κ)^2)) =
      !![reverseTransmission (twistedPotential q) κ,
        I*reflectionAmplitude (twistedPotential q) κ/(2*(Real.exp κ : ℂ));
        2*I*(Real.exp κ : ℂ)*reflectionAmplitude (twistedPotential q) κ,
        transmission (twistedPotential q) κ] := by
  have hS := regularScatteringMatrix_contour_amplitudes q true false κ
  simp only [contourSquaredParameter, ↓reduceIte] at hS
  rw [hS, contourTransmission_eq, contourReverseTransmission_eq,
    contourReverseReflectionAmplitude_eq_neg, contourReflectionAmplitude_eq]
  simp only [contourSource, contourParameter, Bool.false_eq_true, ↓reduceIte,
    one_mul, neg_neg]
  have he : (Real.exp κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero κ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring_nf <;> simp

end
end GaloisForLFunctions.HTGeometry.FokasLenells
