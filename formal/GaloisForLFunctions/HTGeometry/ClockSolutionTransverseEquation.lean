import GaloisForLFunctions.HTGeometry.ClockSolutionTransverseDeriv

/-!
# Differentiating the integral equation in the transverse variable

The two null derivatives of the solution are read off the integral equation by the fundamental
theorem of calculus and the Leibniz rule. The transverse derivative is read off it in a third way:
the integrand is holomorphic in the transverse variable, uniformly on a strip, so the derivative
passes through both integrations.

The result is the transverse analogue of the two null formulas: the transverse derivative of the
solution is the double integral of the transverse derivative of the step operator. Differentiating
*that* along a null coordinate is again the fundamental theorem of calculus, so the mixed
null–transverse derivatives cost nothing beyond this identity.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The step operator applied to the solution is holomorphic in the transverse variable. -/
theorem differentiableOn_clampedStep {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1) (s t : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => clampedStep V T w s t) (imStrip ρ) :=
  differentiableOn_clockStripStep ((hV.holo (boxClamp T s) (boxClamp T t)).mono
      (imStrip_mono hρ.le))
    (differentiableOn_clockSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      (abs_boxClamp_le hT s) (abs_boxClamp_le hT t))

/-- The step operator applied to the solution is jointly continuous on the strip. -/
theorem continuousOn_clampedStep_joint {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) :
    ContinuousOn (fun r : (ℝ × ℝ) × ℂ => clampedStep V T r.2 r.1.1 r.1.2)
      (univ ×ˢ imStrip ρ₁) := fun _ hq =>
  (continuousAt_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hq.2).continuousWithinAt

/-- The inner integral of the step operator is holomorphic in the transverse variable. -/
theorem differentiableOn_clampedInner {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (s η : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in (0 : ℝ)..η, clampedStep V T w s t)
      (imStrip ρ₁) := by
  refine differentiableOn_intervalIntegral_of_holomorphic_on
    (F := fun t w => clampedStep V T w s t) ?_ ?_
  · intro q hq
    have hbase := continuousAt_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      (q := (((s, q.1) : ℝ × ℝ), q.2)) hq.2
    have hcomp := hbase.comp (x := q)
      (f := fun q' : ℝ × ℂ => (((s, q'.1) : ℝ × ℝ), q'.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt
    exact hcomp.continuousWithinAt
  · exact fun t => (differentiableOn_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t).mono
      (imStrip_mono hρ₁.le)

/-- **The transverse derivative passes through the inner integration.** -/
theorem hasDerivAt_clampedInner_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (s η : ℝ)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (fun w : ℂ => ∫ t in (0 : ℝ)..η, clampedStep V T w s t)
      (∫ t in (0 : ℝ)..η, deriv (fun w : ℂ => clampedStep V T w s t) z) z := by
  refine hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun t w => clampedStep V T w s t) hρ₂ ?_ ?_ hz
  · intro q hq
    have hbase := continuousAt_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      (q := (((s, q.1) : ℝ × ℝ), q.2)) hq.2
    have hcomp := hbase.comp (x := q)
      (f := fun q' : ℝ × ℂ => (((s, q'.1) : ℝ × ℝ), q'.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt
    exact hcomp.continuousWithinAt
  · exact fun t => (differentiableOn_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t).mono
      (imStrip_mono hρ₁.le)

/-- **The transverse derivative passes through both integrations.** -/
theorem hasDerivAt_clampedBox_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (ξ η : ℝ)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (fun w : ℂ => ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, clampedStep V T w s t)
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => clampedStep V T w s t) z) z := by
  have hbase := hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun s w => ∫ t in (0 : ℝ)..η, clampedStep V T w s t) (a := 0) (b := ξ) hρ₂ ?_ ?_ hz
  · have hval : (∫ s in (0 : ℝ)..ξ,
        deriv (fun w : ℂ => ∫ t in (0 : ℝ)..η, clampedStep V T w s t) z)
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
          deriv (fun w : ℂ => clampedStep V T w s t) z := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (hasDerivAt_clampedInner_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
        hρ₂ s η hz).deriv
    rwa [hval] at hbase
  · intro q hq
    exact (continuousAt_innerIntegral_of_strip (ρ := ρ₁) (η := η)
      (H := fun s t w => clampedStep V T w s t)
      (continuousOn_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁)
      hq.2).continuousWithinAt
  · exact fun s => differentiableOn_clampedInner hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ s η

/-- **The transverse derivative of the solution.** -/
theorem deriv_clockSolution_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T) {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (clockSolution V ξ η)
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => clampedStep V T w s t) z) z := by
  have hbox := hasDerivAt_clampedBox_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    ξ η hz
  have hshift := hbox.const_add (1 : ℂ)
  refine hshift.congr_of_eventuallyEq ?_
  have hz' : z ∈ imStrip ρ := imStrip_mono hρ₁.le (imStrip_mono hρ₂.le hz)
  refine Filter.eventuallyEq_of_mem ((isOpen_imStrip ρ).mem_nhds hz') fun w hw => ?_
  exact clockSolution_eq_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT
    (le_of_lt (mem_imStrip.mp hw))

end GaloisForLFunctions.HTGeometry
