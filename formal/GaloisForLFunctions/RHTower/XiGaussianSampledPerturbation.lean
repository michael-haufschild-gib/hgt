import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorEnergy
import GaloisForLFunctions.HTGeometry.ComplexSquareEnergyPerturbation
import GaloisForLFunctions.HTGeometry.QuadraticHeatPhaseDefect

/-!
# Degree-free perturbation bounds in actual Xi sampled energy

The reference norm is the complete positive energy on actual divisor copies.
Both the complex signed trace and the positive energy obey the same bound.
In particular, a nearly null sampled direction cannot create a large mixed
term against any test in the actual energy unit ball, irrespective of degree.
-/

open Complex Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

/-- Native half-heat amplitude on every actual divisor copy. -/
def xiGaussianNativeAmplitude (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) : ℂ :=
  heatPhaseAmplitude (evalRealPolynomial P (xiSpectralPoint q ^ 2)) t
    (xiSpectralPoint q ^ 2)

/-- Full positive sampled energy in the native polynomial coordinate. -/
def xiGaussianNativeEnergy (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm P t q‖

theorem xiGaussianNativeEnergy_nonneg (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    0 ≤ xiGaussianNativeEnergy P t := tsum_nonneg fun _ => norm_nonneg _

theorem xiGaussianNativeAmplitude_sq (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    xiGaussianNativeAmplitude P t q ^ 2 = xiPolynomialGaussianHeatTerm P t q :=
  heatPhaseAmplitude_sq _ _ _

theorem xiGaussianNativeAmplitude_norm_sq (P : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    ‖xiGaussianNativeAmplitude P t q‖ ^ 2 = ‖xiPolynomialGaussianHeatTerm P t q‖ := by
  rw [← norm_pow, xiGaussianNativeAmplitude_sq]

theorem xiGaussianNativeAmplitude_add (P Q : Polynomial ℝ) (t : ℝ) (q : XiZeroCopy) :
    xiGaussianNativeAmplitude (P + Q) t q =
      xiGaussianNativeAmplitude P t q + xiGaussianNativeAmplitude Q t q := by
  simp only [xiGaussianNativeAmplitude, heatPhaseAmplitude, evalRealPolynomial,
    Polynomial.map_add, Polynomial.eval_add, add_mul]

/-- Pointwise perturbation before any sum or coefficient expansion. -/
theorem norm_xiGaussianHeatTerm_add_sub_le (P Q : Polynomial ℝ) (t : ℝ)
    (η : {η : ℝ // 0 < η}) (q : XiZeroCopy) :
    ‖xiPolynomialGaussianHeatTerm (P + Q) t q - xiPolynomialGaussianHeatTerm P t q‖ ≤
      (η : ℝ) * ‖xiPolynomialGaussianHeatTerm P t q‖ +
        (1 + 1 / (η : ℝ)) * ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
  have h := norm_complex_square_add_sub_le
    (xiGaussianNativeAmplitude P t q) (xiGaussianNativeAmplitude Q t q) η
  rwa [← xiGaussianNativeAmplitude_add, xiGaussianNativeAmplitude_sq,
    xiGaussianNativeAmplitude_sq, xiGaussianNativeAmplitude_norm_sq,
    xiGaussianNativeAmplitude_norm_sq] at h

/-- Complete complex trace perturbation, uniformly over all polynomial degrees. -/
theorem norm_xiGaussianHeatTrace_add_sub_le (P Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    ‖xiPolynomialGaussianHeatTrace (P + Q) t - xiPolynomialGaussianHeatTrace P t‖ ≤
      (η : ℝ) * xiGaussianNativeEnergy P t +
        (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t := by
  have hP := summable_xiPolynomialGaussianHeatTerm t.property P
  have hQ := summable_xiPolynomialGaussianHeatTerm t.property Q
  have hPQ := summable_xiPolynomialGaussianHeatTerm t.property (P + Q)
  rw [xiPolynomialGaussianHeatTrace, xiPolynomialGaussianHeatTrace, ← hPQ.tsum_sub hP]
  refine (norm_tsum_le_tsum_norm (hPQ.sub hP).norm).trans ?_
  have h := (hPQ.sub hP).norm.tsum_le_tsum
    (norm_xiGaussianHeatTerm_add_sub_le P Q t η)
    ((hP.norm.mul_left (η : ℝ)).add (hQ.norm.mul_left (1 + 1 / (η : ℝ))))
  simpa only [Summable.tsum_add (hP.norm.mul_left (η : ℝ))
    (hQ.norm.mul_left (1 + 1 / (η : ℝ))), tsum_mul_left, xiGaussianNativeEnergy] using h

/-- The signed real Hankel trace retains the same full perturbation control. -/
theorem abs_xiGaussianHeatTraceReal_add_sub_le (P Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    |xiPolynomialGaussianHeatTraceReal (P + Q) t - xiPolynomialGaussianHeatTraceReal P t| ≤
      (η : ℝ) * xiGaussianNativeEnergy P t +
        (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t := by
  exact (Complex.abs_re_le_norm
    (xiPolynomialGaussianHeatTrace (P + Q) t - xiPolynomialGaussianHeatTrace P t)).trans
    (norm_xiGaussianHeatTrace_add_sub_le P Q t η)

/-- The positive sampled energy changes by the same degree-free bound. -/
theorem abs_xiGaussianNativeEnergy_add_sub_le (P Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    |xiGaussianNativeEnergy (P + Q) t - xiGaussianNativeEnergy P t| ≤
      (η : ℝ) * xiGaussianNativeEnergy P t +
        (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t := by
  have hP := (summable_xiPolynomialGaussianHeatTerm t.property P).norm
  have hQ := (summable_xiPolynomialGaussianHeatTerm t.property Q).norm
  have hPQ := (summable_xiPolynomialGaussianHeatTerm t.property (P + Q)).norm
  have hpoint (q : XiZeroCopy) :
      ‖‖xiPolynomialGaussianHeatTerm (P + Q) t q‖ - ‖xiPolynomialGaussianHeatTerm P t q‖‖ ≤
        (η : ℝ) * ‖xiPolynomialGaussianHeatTerm P t q‖ +
          (1 + 1 / (η : ℝ)) * ‖xiPolynomialGaussianHeatTerm Q t q‖ := by
    have h := abs_complex_norm_square_add_sub_le
      (xiGaussianNativeAmplitude P t q) (xiGaussianNativeAmplitude Q t q) η
    rwa [← xiGaussianNativeAmplitude_add, xiGaussianNativeAmplitude_norm_sq,
      xiGaussianNativeAmplitude_norm_sq, xiGaussianNativeAmplitude_norm_sq,
      ← Real.norm_eq_abs] at h
  unfold xiGaussianNativeEnergy
  rw [← hPQ.tsum_sub hP, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (hPQ.sub hP).norm).trans ?_
  have h := (hPQ.sub hP).norm.tsum_le_tsum hpoint
    ((hP.mul_left (η : ℝ)).add (hQ.mul_left (1 + 1 / (η : ℝ))))
  simpa only [Summable.tsum_add (hP.mul_left (η : ℝ))
    (hQ.mul_left (1 + 1 / (η : ℝ))), tsum_mul_left] using h

/-- Signed trace is bounded by actual sampled energy without a positivity premise. -/
theorem abs_xiGaussianHeatTraceReal_le_nativeEnergy (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    |xiPolynomialGaussianHeatTraceReal P t| ≤ xiGaussianNativeEnergy P t :=
  (Complex.abs_re_le_norm _).trans
    (norm_tsum_le_tsum_norm (summable_xiPolynomialGaussianHeatTerm t.property P).norm)

end RHTower
