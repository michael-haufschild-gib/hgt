import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFlowTraceClass
import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticLefschetz

/-! # Distributional Lefschetz trace of the original full-Jordan Meyer flow

The middle trace here is the ordinary basis-independent operator trace of a
Bochner average of the actual source flow on its faithful Hilbert completion.
Its trace-class proof factors through the full original generator inverse;
no replacement by a diagonal operator, spectral simplicity, or RH is used.
-/

noncomputable section
open Complex MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem deningerHasseShiftEvolution_basis_diagonal (t : ℝ)
    (q : DeningerArithmeticJetCoordinate) :
    deningerHasseShiftEvolution t (xiDivisorHilbertBasis q) q = 1 := by
  classical
  rw [deningerHasseShiftEvolution_apply, xiDivisorHilbertBasis_apply]
  rw [Finset.sum_eq_single 0]
  · simp [deningerHasseLower]
  · intro k hk hk0
    have hl : deningerHasseLower q k ≠ q := by
      intro he
      have hj := congrArg (fun r : DeningerArithmeticJetCoordinate => r.2.val) he
      change q.2.val-k = q.2.val at hj
      have hk' := Finset.mem_range.mp hk
      omega
    have hz : (lp.single 2 q (1 : ℂ) : DeningerArithmeticJetHilbert)
        (deningerHasseLower q k) = 0 := by
      simpa only using! (lp.single_apply_ne (E := fun _ : DeningerArithmeticJetCoordinate => ℂ)
        2 q (1 : ℂ) hl)
    exact mul_eq_zero_of_right _ hz
  · simp

/-- Nilpotent terms are retained by the flow but vanish on its basis diagonal. -/
theorem deningerMeyerHilbertFlow_basis_diagonal (t : ℝ)
    (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerHilbertFlow t (xiDivisorHilbertBasis q) q =
      Complex.exp ((t : ℂ)*(q.1 : ℂ)) := by
  change Complex.exp ((t : ℂ)*(q.1 : ℂ))*
    deningerHasseShiftEvolution t (xiDivisorHilbertBasis q) q = _
  rw [deningerHasseShiftEvolution_basis_diagonal, mul_one]

theorem deningerMeyerFlowSmoothing_basis_diagonal (φ : DeningerTimeTestFunction)
    (q : DeningerArithmeticJetCoordinate) :
    ⟪xiDivisorHilbertBasis q, deningerMeyerFlowSmoothing φ (xiDivisorHilbertBasis q)⟫_ℂ =
      deningerTimeTestLaplace φ (q.1 : ℂ) := by
  classical
  rw [xiDivisorHilbertBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [← xiDivisorHilbertBasis_apply, deningerMeyerFlowSmoothing_coordinate]
  simp only [deningerMeyerHilbertFlow_basis_diagonal, deningerTimeTestLaplace]

/-- The operator trace of the actual full source average equals its multiplicity-exact divisor sum. -/
theorem deningerMeyerFlowSmoothing_opTrace (φ : DeningerTimeTestFunction) :
    opTrace (deningerMeyerFlowSmoothing φ) =
      ∑' q : XiZeroCopy, deningerTimeTestLaplace φ (deningerRawThetaEigen q) := by
  rw [opTrace_eq_tsum_basis_of_mem (deningerMeyerFlowSmoothing_mem_hsTraceIdeal φ)
    xiDivisorHilbertBasis]
  exact tsum_congr (fun q => deningerMeyerFlowSmoothing_basis_diagonal φ q)

theorem deningerMeyerFlowSmoothing_opTrace_eq_H1 (φ : DeningerTimeTestFunction) :
    opTrace (deningerMeyerFlowSmoothing φ) = deningerArithmeticH1TraceDistribution φ := by
  rw [deningerMeyerFlowSmoothing_opTrace,
    deningerArithmeticH1TraceDistribution_apply_eq_spectralSum]

/-- The genuine operator trace is continuous in the full test-function topology. -/
theorem continuous_deningerMeyerFlowSmoothing_opTrace :
    Continuous (fun φ : DeningerTimeTestFunction => opTrace (deningerMeyerFlowSmoothing φ)) := by
  simpa only [deningerMeyerFlowSmoothing_opTrace_eq_H1] using!
    deningerArithmeticH1TraceDistribution.continuous

/-- Full prime, Gamma, and endpoint Lefschetz law for the actual source-flow average. -/
theorem deningerMeyerSourceFlowLefschetz (φ : DeningerTimeTestFunction) :
    deningerTimeTestLaplace φ 0 - opTrace (deningerMeyerFlowSmoothing φ) +
      deningerTimeTestLaplace φ 1 =
        (∑' n : DeningerPrimePowerIndex,
          (deningerPrimePowerWeight n : ℂ)*(φ (deningerPrimePowerTime n) : ℂ)) +
        ∫ t : ℝ, (φ t : ℂ)*deningerArchimedeanLefschetzDensity t := by
  rw [deningerMeyerFlowSmoothing_opTrace]
  exact deningerArithmeticScalarExplicitFormula_proved φ

end RHTower
