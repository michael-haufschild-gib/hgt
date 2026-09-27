import GaloisForLFunctions.RHTower.XiGaussianUniformAnnihilatorControl
import GaloisForLFunctions.RHTower.XiPolynomialGaussianExplicitFormula

/-!
# Actual prime--Gamma cancellation along the fixed-time null family

The complete arithmetic source, including its polar term and all mixed
polynomial terms, has a degree-free perturbation bound in actual sampled
energy. It vanishes along the normalized finite-divisor annihilators. Its
mixed interaction with the entire sampled unit ball vanishes uniformly.
-/

open Complex MeasureTheory Filter Topology
open scoped Real
noncomputable section

namespace RHTower

/-- Exact Gamma plus polar minus complete prime source; no absolute prime
majorant replaces the signed arithmetic cancellation. -/
def xiGaussianCompletedSourceResidual (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  (∫ x : ℝ, ‖routeUPolynomialGaussianDensity P t x‖ * gammaHardyPhaseRate x) +
    2 * π * (P.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp ((t : ℝ) / 4) -
      (routeUPolynomialGaussianPrimeSource P t).re

theorem xiGaussianCompletedSourceResidual_eq_trace (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianCompletedSourceResidual P t = π * xiPolynomialGaussianHeatTraceReal P t :=
  (pi_mul_xiPolynomialGaussianHeatTraceReal_eq_primeGamma P t).symm

/-- The actual residual is controlled in the actual sampled energy. -/
theorem abs_xiGaussianCompletedSourceResidual_le_energy (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    |xiGaussianCompletedSourceResidual P t| ≤ π * xiGaussianNativeEnergy P t := by
  rw [xiGaussianCompletedSourceResidual_eq_trace, abs_mul, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (abs_xiGaussianHeatTraceReal_le_nativeEnergy P t)
    Real.pi_pos.le

/-- All coefficient cross terms obey a degree-independent source perturbation bound. -/
theorem abs_xiGaussianCompletedSourceResidual_add_sub_le (P Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    |xiGaussianCompletedSourceResidual (P + Q) t - xiGaussianCompletedSourceResidual P t| ≤
      π * ((η : ℝ) * xiGaussianNativeEnergy P t +
        (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t) := by
  rw [xiGaussianCompletedSourceResidual_eq_trace, xiGaussianCompletedSourceResidual_eq_trace,
    ← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (abs_xiGaussianHeatTraceReal_add_sub_le P Q t η)
    Real.pi_pos.le

/-- A nontrivial family with nonvanishing continuous mass has vanishing
complete arithmetic residual at every fixed positive heat time. -/
theorem tendsto_xiGaussianCompletedSourceResidual_annihilator_zero
    (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiGaussianCompletedSourceResidual (xiGaussianAnnihilator F) t) atTop (𝓝 0) := by
  simpa only [xiGaussianCompletedSourceResidual_eq_trace, mul_zero] using
    (tendsto_xiGaussianHeatTraceReal_annihilator_zero t).const_mul π

/-- The complete raw prime term cancels the literal polar and Gamma terms.
This is a fixed-time limit of actual sources, not an absolute-tail estimate. -/
theorem tendsto_xiGaussianAnnihilator_prime_sub_polarGamma_zero
    (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      (routeUPolynomialGaussianPrimeSource (xiGaussianAnnihilator F) t).re -
        2 * π * ((xiGaussianAnnihilator F).eval (-(1 / 4 : ℝ))) ^ 2 *
          Real.exp ((t : ℝ) / 4) -
        (∫ x : ℝ, ‖routeUPolynomialGaussianDensity (xiGaussianAnnihilator F) t x‖ *
          gammaHardyPhaseRate x)) atTop (𝓝 0) := by
  have h := (tendsto_xiGaussianCompletedSourceResidual_annihilator_zero t).neg
  simp only [neg_zero] at h
  convert h using 1
  funext F
  unfold xiGaussianCompletedSourceResidual
  ring

/-- One divisor cutoff controls arithmetic perturbation simultaneously for
all polynomial orders in the actual energy unit ball. -/
theorem eventually_forall_xiGaussianAnnihilator_source_perturbation_small
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t ≤ 1},
        |xiGaussianCompletedSourceResidual (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianCompletedSourceResidual P.1 t| < (ε : ℝ) := by
  let e : {e : ℝ // 0 < e} := ⟨(ε : ℝ) / π, div_pos ε.property Real.pi_pos⟩
  filter_upwards [eventually_forall_xiGaussianAnnihilator_perturbation_small t e] with F hF P
  rw [xiGaussianCompletedSourceResidual_eq_trace, xiGaussianCompletedSourceResidual_eq_trace,
    ← mul_sub, abs_mul, abs_of_pos Real.pi_pos]
  have h := mul_lt_mul_of_pos_left (hF P).1 Real.pi_pos
  dsimp only [e] at h
  simpa only [mul_div_cancel₀ _ Real.pi_ne_zero] using h

/-- Every complete mixed prime--Gamma term with an energy-unit polynomial
vanishes uniformly, with no bound on the degree of either test. -/
theorem eventually_forall_xiGaussianAnnihilator_mixed_source_small
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t ≤ 1},
        |xiGaussianCompletedSourceResidual (P.1 + xiGaussianAnnihilator F) t -
          xiGaussianCompletedSourceResidual P.1 t -
          xiGaussianCompletedSourceResidual (xiGaussianAnnihilator F) t| < (ε : ℝ) := by
  let e : {e : ℝ // 0 < e} := ⟨(ε : ℝ) / π, div_pos ε.property Real.pi_pos⟩
  filter_upwards [eventually_forall_xiGaussianAnnihilator_mixed_trace_small t e] with F hF P
  rw [xiGaussianCompletedSourceResidual_eq_trace, xiGaussianCompletedSourceResidual_eq_trace,
    xiGaussianCompletedSourceResidual_eq_trace, ← mul_sub, ← mul_sub,
    abs_mul, abs_of_pos Real.pi_pos]
  have h := mul_lt_mul_of_pos_left (hF P) Real.pi_pos
  dsimp only [e] at h
  simpa only [mul_div_cancel₀ _ Real.pi_ne_zero] using h

end RHTower
