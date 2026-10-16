import GaloisForLFunctions.RHTower.DeningerMeyerHilbertFlowDerivative
import GaloisForLFunctions.RHTower.DeningerArithmeticTimeDistribution

/-! # Genuine compact-time averages of the full Meyer flow

Each average is constructed as a Bochner integral of actual vector orbits.
The operator includes the original Hasse action, rather than its diagonal
trace alone. No spectral sign or simplicity premise is used.
-/

noncomputable section
open Complex MeasureTheory Filter Set Topology

namespace RHTower

private theorem integrable_test_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (φ : DeningerTimeTestFunction) (f : ℝ → E) (hf : Continuous f) :
    Integrable (fun t : ℝ => (φ t : ℂ) • f t) := by
  have hc : Continuous (fun t : ℝ => (φ t : ℂ)) := Complex.continuous_ofReal.comp φ.continuous
  have hs : HasCompactSupport (fun t : ℝ => (φ t : ℂ)) := by
    simpa only [Function.comp_apply] using!
      φ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  exact (hc.smul hf).integrable_of_hasCompactSupport hs.smul_right

theorem integrable_deningerMeyerFlowAverage (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) :
    Integrable (fun t : ℝ => (φ t : ℂ) • deningerMeyerHilbertFlow t x) := by
  exact integrable_test_smul φ _ (continuous_deningerMeyerHilbertFlow_orbit x)

def deningerMeyerFlowAverage (φ : DeningerTimeTestFunction) (x : DeningerArithmeticJetHilbert) :
    DeningerArithmeticJetHilbert := ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t x

theorem integrable_deningerMeyerFlowWeight (φ : DeningerTimeTestFunction) :
    Integrable (fun t => ‖φ t‖*deningerMeyerHilbertFlowBound t) :=
  (φ.continuous.norm.mul continuous_deningerMeyerHilbertFlowBound).integrable_of_hasCompactSupport
    φ.hasCompactSupport.norm.mul_right

theorem norm_deningerMeyerFlowAverage (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) :
    ‖deningerMeyerFlowAverage φ x‖ ≤ (∫ t, ‖φ t‖*deningerMeyerHilbertFlowBound t)*‖x‖ := by
  have hb (t : ℝ) : ‖(φ t : ℂ) • deningerMeyerHilbertFlow t x‖ ≤
      (‖φ t‖*deningerMeyerHilbertFlowBound t)*‖x‖ := by
    rw [norm_smul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (norm_deningerMeyerHilbertFlow_apply t x)
      (norm_nonneg (φ t))).trans_eq (mul_assoc _ _ _).symm
  have h := norm_integral_le_of_norm_le
    ((integrable_deningerMeyerFlowWeight φ).mul_const ‖x‖) (Eventually.of_forall hb)
  simpa only [deningerMeyerFlowAverage, integral_mul_const] using h

def deningerMeyerFlowSmoothingLM (φ : DeningerTimeTestFunction) :
    DeningerArithmeticJetHilbert →ₗ[ℂ] DeningerArithmeticJetHilbert where
  toFun := deningerMeyerFlowAverage φ
  map_add' x y := by
    simp only [deningerMeyerFlowAverage, map_add, smul_add]
    exact integral_add (integrable_deningerMeyerFlowAverage φ x) (integrable_deningerMeyerFlowAverage φ y)
  map_smul' c x := by
    change (∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t (c • x)) =
      c • ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t x
    calc
      _ = ∫ t : ℝ, c • ((φ t : ℂ) • deningerMeyerHilbertFlow t x) :=
        integral_congr_ae (Eventually.of_forall fun t => by rw [map_smul, smul_comm])
      _ = _ := integral_smul c _

/-- Compact-time averaging of the actual full source flow as a bounded operator. -/
def deningerMeyerFlowSmoothing (φ : DeningerTimeTestFunction) :
    DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert :=
  (deningerMeyerFlowSmoothingLM φ).mkContinuous
    (∫ t, ‖φ t‖*deningerMeyerHilbertFlowBound t) (norm_deningerMeyerFlowAverage φ)

theorem deningerMeyerFlowSmoothing_apply (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) :
    deningerMeyerFlowSmoothing φ x = ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t x := rfl

theorem deningerMeyerFlowSmoothing_coordinate (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    deningerMeyerFlowSmoothing φ x q =
      ∫ t : ℝ, (φ t : ℂ)*deningerMeyerHilbertFlow t x q := by
  have h := (lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q).integral_comp_comm
    (integrable_deningerMeyerFlowAverage φ x)
  exact h.symm

/-- The average agrees with the literal dilation of every original Meyer class. -/
theorem deningerMeyerFlowSmoothing_source (φ : DeningerTimeTestFunction)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerFlowSmoothing φ (deningerMeyerHasseHilbertLM u) =
      ∫ t : ℝ, (φ t : ℂ) •
        deningerMeyerHasseHilbertLM (deningerMeyerStrongLogCohomologyFlow t u) := by
  rw [deningerMeyerFlowSmoothing_apply]
  apply integral_congr_ae
  filter_upwards with t
  exact congrArg (fun v : DeningerArithmeticJetHilbert => (φ t : ℂ) • v)
    (deningerMeyerHilbertFlow_source t u)

theorem deningerMeyerFlowSmoothing_add (φ ψ : DeningerTimeTestFunction) :
    deningerMeyerFlowSmoothing (φ+ψ) = deningerMeyerFlowSmoothing φ+deningerMeyerFlowSmoothing ψ := by
  apply ContinuousLinearMap.ext
  intro x
  change (∫ t : ℝ, ((φ t+ψ t : ℝ) : ℂ) • deningerMeyerHilbertFlow t x) =
    (∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t x) +
    (∫ t : ℝ, (ψ t : ℂ) • deningerMeyerHilbertFlow t x)
  simp only [Complex.ofReal_add, add_smul]
  exact integral_add (integrable_deningerMeyerFlowAverage φ x) (integrable_deningerMeyerFlowAverage ψ x)

theorem deningerMeyerFlowSmoothing_real_smul (a : ℝ) (φ : DeningerTimeTestFunction) :
    deningerMeyerFlowSmoothing (a • φ) = (a : ℂ) • deningerMeyerFlowSmoothing φ := by
  apply ContinuousLinearMap.ext
  intro x
  change (∫ t : ℝ, ((a*φ t : ℝ) : ℂ) • deningerMeyerHilbertFlow t x) =
    (a : ℂ) • ∫ t : ℝ, (φ t : ℂ) • deningerMeyerHilbertFlow t x
  simp only [Complex.ofReal_mul, mul_smul]
  exact integral_smul (a : ℂ) _

end RHTower
