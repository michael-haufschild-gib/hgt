import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFlowSmoothing
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerClosedHasseGenerator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal

/-! # Source-flow smoothing factors through the actual Hasse inverse

Coordinate integration by parts puts every compact smooth time average in
the square of the original generator's resolvent ideal. This proves actual
trace class, including the full nilpotent action at every repeated zero.
-/

noncomputable section
open Complex MeasureTheory Filter Set Topology ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem timeTest_integral_byParts (φ : DeningerTimeTestFunction)
    (f f' : ℝ → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ t, HasDerivAt f (f' t) t) :
    (∫ t : ℝ, (φ t : ℂ)*f' t) =
      -(∫ t : ℝ, (deningerTimeTestDerivative φ t : ℂ)*f t) := by
  let u : ℝ → ℂ := fun t => (φ t : ℂ)
  let u' : ℝ → ℂ := fun t => (deningerTimeTestDerivative φ t : ℂ)
  have hu : ∀ t, HasDerivAt u (u' t) t := by
    intro t
    have hφ := (φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt (x := t)
    simpa only [u, u', deningerTimeTestDerivative_apply_eq_deriv] using hφ.ofReal_comp
  have hc : Continuous u := Complex.continuous_ofReal.comp φ.continuous
  have hc' : Continuous u' := Complex.continuous_ofReal.comp (deningerTimeTestDerivative φ).continuous
  have hs : HasCompactSupport u := by
    simpa only [u, Function.comp_apply] using!
      φ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hs' : HasCompactSupport u' := by
    simpa only [u', Function.comp_apply] using!
      (deningerTimeTestDerivative φ).hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t _ => hu t) (fun t _ => hd t)
    ((hc.mul hf').integrable_of_hasCompactSupport hs.mul_right)
    ((hc'.mul hf).integrable_of_hasCompactSupport hs'.mul_right)
    ((hc.mul hf).integrable_of_hasCompactSupport hs.mul_right)

/-- Integration by parts for the full generator, including its predecessor term. -/
theorem deningerMeyerFlowSmoothing_generator_row (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    (q.1 : ℂ)*deningerMeyerFlowSmoothing φ x q +
      deningerHasseHilbertShift (deningerMeyerFlowSmoothing φ x) q =
        -deningerMeyerFlowSmoothing (deningerTimeTestDerivative φ) x q := by
  let ev := lp.evalCLM ℂ (fun _ : DeningerArithmeticJetCoordinate => ℂ) 2 q
  let A := (q.1 : ℂ) • ev + ev.comp deningerHasseHilbertShift
  have hcomm := (A.integral_comp_comm (integrable_deningerMeyerFlowAverage φ x)).symm
  change A (deningerMeyerFlowSmoothing φ x) = _ at hcomm
  change A (deningerMeyerFlowSmoothing φ x) = _
  rw [hcomm, deningerMeyerFlowSmoothing_coordinate]
  simp only [map_smul, smul_eq_mul]
  exact timeTest_integral_byParts φ
    (fun t => deningerMeyerHilbertFlow t x q)
    (fun t => (q.1 : ℂ)*deningerMeyerHilbertFlow t x q +
      deningerHasseHilbertShift (deningerMeyerHilbertFlow t x) q)
    (ev.continuous.comp (continuous_deningerMeyerHilbertFlow_orbit x))
    (continuous_deningerMeyerHilbertFlow_coordinate_deriv x q)
    (hasDerivAt_deningerMeyerHilbertFlow_coordinate x q)

/-- The transpose time derivative for the generator centered at one half. -/
def deningerMeyerCenteredTimeDerivative (φ : DeningerTimeTestFunction) :
    DeningerTimeTestFunction := deningerTimeTestDerivative φ + (1/2 : ℝ) • φ

theorem deningerMeyerFlowSmoothing_centered_row (φ : DeningerTimeTestFunction)
    (x : DeningerArithmeticJetHilbert) (q : DeningerArithmeticJetCoordinate) :
    xiSpectralPoint q * deningerMeyerFlowSmoothing φ x q -
      I * deningerHasseHilbertShift (deningerMeyerFlowSmoothing φ x) q =
        I * deningerMeyerFlowSmoothing (deningerMeyerCenteredTimeDerivative φ) x q := by
  have h := deningerMeyerFlowSmoothing_generator_row φ x q
  rw [deningerMeyerCenteredTimeDerivative, deningerMeyerFlowSmoothing_add,
    deningerMeyerFlowSmoothing_real_smul]
  simp only [add_apply, smul_apply,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    xiSpectralPoint_eq_support, xiSpectralPointSupport]
  linear_combination -I * h

/-- The actual inverse, not a diagonal surrogate, solves the averaged source equation. -/
theorem deningerMeyerFlowSmoothing_resolvent (φ : DeningerTimeTestFunction) :
    deningerMeyerFlowSmoothing φ = I • deningerMeyerHasseResolvent.comp
      (deningerMeyerFlowSmoothing (deningerMeyerCenteredTimeDerivative φ)) := by
  apply ContinuousLinearMap.ext
  intro x
  have h := deningerMeyerHasseResolvent_of_equation (deningerMeyerFlowSmoothing φ x)
    (I • deningerMeyerFlowSmoothing (deningerMeyerCenteredTimeDerivative φ) x)
    (deningerMeyerFlowSmoothing_centered_row φ x)
  simpa only [map_smul, smul_apply, ContinuousLinearMap.comp_apply] using h.symm

/-- Two genuine Hilbert--Schmidt factors for every compact smooth time average. -/
theorem deningerMeyerFlowSmoothing_factorization (φ : DeningerTimeTestFunction) :
    deningerMeyerFlowSmoothing φ = (-deningerMeyerHasseResolvent).comp
      (deningerMeyerHasseResolvent.comp (deningerMeyerFlowSmoothing
        (deningerMeyerCenteredTimeDerivative (deningerMeyerCenteredTimeDerivative φ)))) := by
  have h₁ := deningerMeyerFlowSmoothing_resolvent φ
  have h₂ := deningerMeyerFlowSmoothing_resolvent (deningerMeyerCenteredTimeDerivative φ)
  rw [h₂] at h₁
  rw [h₁]
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    neg_apply, map_smul, smul_smul, Complex.I_mul_I, neg_one_smul]

theorem deningerMeyerFlowSmoothing_mem_hsTraceIdeal (φ : DeningerTimeTestFunction) :
    deningerMeyerFlowSmoothing φ ∈ hsTraceIdeal DeningerArithmeticJetHilbert := by
  rw [deningerMeyerFlowSmoothing_factorization]
  exact comp_mem_hsTraceIdeal deningerMeyerHasseResolvent_isHilbertSchmidt.neg
    (deningerMeyerHasseResolvent_isHilbertSchmidt.comp_right _)

/-- Genuine summability of singular values, with no arithmetic admission premise. -/
theorem deningerMeyerFlowSmoothing_memSchattenClass_one (φ : DeningerTimeTestFunction) :
    MemSchattenClass 1 (deningerMeyerFlowSmoothing φ) := by
  rw [deningerMeyerFlowSmoothing_factorization]
  exact memSchattenClass_one_comp deningerMeyerHasseResolvent_isHilbertSchmidt.neg
    (deningerMeyerHasseResolvent_isHilbertSchmidt.comp_right _)

end RHTower
