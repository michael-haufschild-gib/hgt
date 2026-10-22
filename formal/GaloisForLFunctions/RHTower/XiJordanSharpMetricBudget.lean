import GaloisForLFunctions.HTGeometry.TaylorJordanNormalization
import GaloisForLFunctions.RHTower.XiHedenmalmJordanMatrix
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticJetDeterminant

/-!
# Exact metric-conditioning frontier of the actual Xi arithmetic jet chains

Every literal local Xi chain has an attained least trace-energy defect under
each Taylor-frame conditioning budget. Spectral displacement and chain depth
contribute separately. The normalization is an explicit factorial and reversal
frame on the source derivative jets; neither RH nor simplicity is assumed.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace RHTower

noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry Matrix

/-- The reference Euclidean norm is the reversed Taylor-coefficient norm. -/
def xiArithmeticTaylorFrame (rho : XiDivisorSupport) :
    (Matrix (DeningerArithmeticJetIndex rho) (DeningerArithmeticJetIndex rho) ℂ)ˣ :=
  reversedTaylorFrame (xiSupportMultiplicity rho)

theorem xiArithmeticTaylorFrame_conjugate (rho : XiDivisorSupport) :
    (xiArithmeticTaylorFrame rho).val *
        deningerArithmeticJetCenteredMatrix rho *
        (xiArithmeticTaylorFrame rho).inv =
      xiLocalJordanMatrix rho :=
  reversedTaylorFrame_conjugate (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)

theorem xiLocalJordanMatrix_budget_isLeast (rho : XiDivisorSupport)
    {q : ℝ} (hq : 1 ≤ q) :
    IsLeast
      {x : ℝ | ∃ P : (Matrix (Fin (xiSupportMultiplicity rho))
          (Fin (xiSupportMultiplicity rho)) ℂ)ˣ,
        HilbertMetric.similarityConditionNumber P ≤ q ^ (xiSupportMultiplicity rho - 1) ∧
        finiteMatrixQuadraticTraceEnergyDefect
          ((P : Matrix (Fin (xiSupportMultiplicity rho)) (Fin (xiSupportMultiplicity rho)) ℂ) *
            xiLocalJordanMatrix rho * P.inv) = x}
      (2 * (xiSupportMultiplicity rho : ℝ) * (xiSpectralPointSupport rho).im ^ 2 +
        ((xiSupportMultiplicity rho - 1 : ℕ) : ℝ) / q ^ 2) :=
  metricJordanBlock_budget_isLeast (xiSupportMultiplicity rho) (xiSupportMultiplicity_pos rho)
    (xiSpectralPointSupport rho) hq

theorem xiArithmeticMetric_conjugate (rho : XiDivisorSupport)
    (P : (Matrix (DeningerArithmeticJetIndex rho) (DeningerArithmeticJetIndex rho) ℂ)ˣ) :
    (P * xiArithmeticTaylorFrame rho).val *
      deningerArithmeticJetCenteredMatrix rho *
      (P * xiArithmeticTaylorFrame rho).inv =
    P.val * xiLocalJordanMatrix rho * P.inv := by
  change (P.val * (xiArithmeticTaylorFrame rho).val) *
      deningerArithmeticJetCenteredMatrix rho * ((xiArithmeticTaylorFrame rho).inv * P.inv) = _
  rw [← xiArithmeticTaylorFrame_conjugate rho]
  simp only [Matrix.mul_assoc]

/-- Exact attained frontier on the native centered Frobenius, in its specified Taylor norm. -/
theorem xiArithmeticJet_metricBudget_isLeast (rho : XiDivisorSupport)
    {q : ℝ} (hq : 1 ≤ q) :
    IsLeast
      {x : ℝ | ∃ P : (Matrix (DeningerArithmeticJetIndex rho)
          (DeningerArithmeticJetIndex rho) ℂ)ˣ,
        HilbertMetric.similarityConditionNumber P ≤ q ^ (xiSupportMultiplicity rho - 1) ∧
        finiteMatrixQuadraticTraceEnergyDefect
          ((P * xiArithmeticTaylorFrame rho).val *
            deningerArithmeticJetCenteredMatrix rho *
            (P * xiArithmeticTaylorFrame rho).inv) = x}
      (2 * (xiSupportMultiplicity rho : ℝ) * ((rho : ℂ).re - 1 / 2) ^ 2 +
        ((xiSupportMultiplicity rho - 1 : ℕ) : ℝ) / q ^ 2) := by
  simp only [xiArithmeticMetric_conjugate]
  have him : (xiSpectralPointSupport rho).im = -((rho : ℂ).re - 1 / 2) := by
    simp [xiSpectralPointSupport]
  simpa only [him, neg_sq] using xiLocalJordanMatrix_budget_isLeast rho hq

/-- All admitted native frames give literal positive definite jet forms. -/
theorem xiArithmeticMetric_gram_posDef (rho : XiDivisorSupport)
    (P : (Matrix (DeningerArithmeticJetIndex rho) (DeningerArithmeticJetIndex rho) ℂ)ˣ) :
    let Q : Matrix (DeningerArithmeticJetIndex rho) (DeningerArithmeticJetIndex rho) ℂ :=
      (P * xiArithmeticTaylorFrame rho).val
    (Qᴴ * Q).PosDef :=
  matrixMetricFrame_gram_posDef (P * xiArithmeticTaylorFrame rho)

end
end RHTower
