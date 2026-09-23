import GaloisForLFunctions.HTGeometry.ClockSolutionMixedTransverse

/-!
# The second transverse derivative of the integral equation

The transverse derivative of the solution is the double integral of the transverse derivative of the
step operator. That identity has exactly the shape of the integral equation itself, so the argument
that produced it produces its own derivative in turn: the second transverse derivative of the
solution is the double integral of the second transverse derivative of the step operator.

This is what makes the pure second derivative along a null coordinate accessible. Differentiating
`u_zz` along a null coordinate is then the fundamental theorem of calculus applied to that double
integral — no differentiation of a Cauchy representation in a parameter is needed anywhere.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- The transverse derivative of the step operator applied to the solution. -/
noncomputable def dClampedStep (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (w : ℂ) (s t : ℝ) : ℂ :=
  deriv (fun v : ℂ => clampedStep V T v s t) w

/-- The transverse derivative of the step operator is holomorphic in the transverse variable. -/
theorem differentiableOn_dClampedStep {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁ : ρ₁ < ρ) (s t : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => dClampedStep V T w s t) (imStrip ρ₁) :=
  differentiableOn_deriv_of_holomorphic hρ₁
    (differentiableOn_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t)

/-- The transverse derivative of the step operator is jointly continuous on the strip. -/
theorem continuousOn_dClampedStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) :
    ContinuousOn (fun r : (ℝ × ℝ) × ℂ => dClampedStep V T r.2 r.1.1 r.1.2)
      (univ ×ˢ imStrip ρ₂) := fun _ hq =>
  (continuousAt_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂
    hq.2).continuousWithinAt

/-- The inner integral of the transverse derivative of the step operator is holomorphic. -/
theorem differentiableOn_dClampedInner {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (s η : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in (0 : ℝ)..η, dClampedStep V T w s t)
      (imStrip ρ₂) := by
  refine differentiableOn_intervalIntegral_of_holomorphic_on
    (F := fun t w => dClampedStep V T w s t) ?_ ?_
  · intro q hq
    have hbase := continuousAt_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      hρ₂0 hρ₂ (q := (((s, q.1) : ℝ × ℝ), q.2)) hq.2
    have hcomp := hbase.comp (x := q)
      (f := fun q' : ℝ × ℂ => (((s, q'.1) : ℝ × ℝ), q'.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt
    exact hcomp.continuousWithinAt
  · exact fun t => (differentiableOn_dClampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁ s t).mono
      (imStrip_mono hρ₂.le)

/-- **The second transverse derivative passes through the inner integration.** -/
theorem hasDerivAt_dClampedInner_transverse {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (s η : ℝ) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun w : ℂ => ∫ t in (0 : ℝ)..η, dClampedStep V T w s t)
      (∫ t in (0 : ℝ)..η, deriv (fun w : ℂ => dClampedStep V T w s t) z) z := by
  refine hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₂) (ρ := ρ₃)
    (F := fun t w => dClampedStep V T w s t) hρ₃ ?_ ?_ hz
  · intro q hq
    have hbase := continuousAt_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      hρ₂0 hρ₂ (q := (((s, q.1) : ℝ × ℝ), q.2)) hq.2
    have hcomp := hbase.comp (x := q)
      (f := fun q' : ℝ × ℂ => (((s, q'.1) : ℝ × ℝ), q'.2))
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd).continuousAt
    exact hcomp.continuousWithinAt
  · exact fun t => (differentiableOn_dClampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁ s t).mono
      (imStrip_mono hρ₂.le)

/-- **The second transverse derivative passes through both integrations.** -/
theorem hasDerivAt_dClampedBox_transverse {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (ξ η : ℝ) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun w : ℂ => ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, dClampedStep V T w s t)
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => dClampedStep V T w s t) z) z := by
  have hbase := hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₂) (ρ := ρ₃)
    (F := fun s w => ∫ t in (0 : ℝ)..η, dClampedStep V T w s t) (a := 0) (b := ξ) hρ₃ ?_ ?_ hz
  · have hval : (∫ s in (0 : ℝ)..ξ,
        deriv (fun w : ℂ => ∫ t in (0 : ℝ)..η, dClampedStep V T w s t) z)
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
          deriv (fun w : ℂ => dClampedStep V T w s t) z := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (hasDerivAt_dClampedInner_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
        hρ₂0 hρ₂ hρ₃ s η hz).deriv
    rwa [hval] at hbase
  · intro q hq
    exact (continuousAt_innerIntegral_of_strip (ρ := ρ₂) (η := η)
      (H := fun s t w => dClampedStep V T w s t)
      (continuousOn_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂)
      hq.2).continuousWithinAt
  · exact fun s => differentiableOn_dClampedInner hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      hρ₂0 hρ₂ s η

/-- **The second transverse derivative of the solution.** -/
theorem hasDerivAt_deriv_clockSolution_box {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (deriv (clockSolution V ξ η))
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => dClampedStep V T w s t) z) z := by
  have hbox := hasDerivAt_dClampedBox_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃ ξ η hz
  refine hbox.congr_of_eventuallyEq ?_
  have hz' : z ∈ imStrip ρ₂ := imStrip_mono hρ₃.le hz
  refine Filter.eventuallyEq_of_mem ((isOpen_imStrip ρ₂).mem_nhds hz') fun w hw => ?_
  exact (deriv_clockSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    hξT hηT hw).deriv

/-- The second transverse derivative of the solution, as a double integral. -/
theorem deriv_deriv_clockSolution_eq {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    deriv (deriv (clockSolution V ξ η)) z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => dClampedStep V T w s t) z :=
  (hasDerivAt_deriv_clockSolution_box hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃
    hξT hηT hz).deriv

end GaloisForLFunctions.HTGeometry
