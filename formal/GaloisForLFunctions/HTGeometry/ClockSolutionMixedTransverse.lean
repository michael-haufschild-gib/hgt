import GaloisForLFunctions.HTGeometry.ClockSolutionTransverseEquation

/-!
# The mixed null–transverse derivatives

The transverse derivative of the solution is the double integral of the transverse derivative of the
step operator. That identity has the same shape as the integral equation itself, so differentiating
it along a null coordinate repeats the two arguments already used there: the fundamental theorem of
calculus for the outer integration, the Leibniz rule for the inner one.

What has to be checked first is that the transverse derivative of the step operator is jointly
continuous, and that is again the Cauchy representation applied to a family holomorphic on a strip.

The transverse derivative of each null derivative is the same double integral read in the other
order, so all four mixed second derivatives are the two functions

`∫₀^η ∂_z S(ξ,t,z) dt`  and  `∫₀^ξ ∂_z S(s,η,z) ds`,

as the symmetry of mixed partials requires. The second pure transverse derivative is free: the
solution is holomorphic in that variable, hence so is its derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- **The transverse derivative of the step operator is jointly continuous.** -/
theorem continuousAt_dClampedStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ₂) :
    ContinuousAt
      (fun q' : (ℝ × ℝ) × ℂ => deriv (fun w : ℂ => clampedStep V T w q'.1.1 q'.1.2) q'.2) q :=
  continuousAt_deriv_of_strip (ρ' := ρ₁) (P := ℝ × ℝ)
    (W := fun p : ℝ × ℝ => fun w : ℂ => clampedStep V T w p.1 p.2) hρ₂ hρ₂0
    (continuousOn_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁)
    (fun p => (differentiableOn_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall p.1 p.2).mono
      (imStrip_mono hρ₁.le)) hq

/-- The transverse derivative of the step operator, at a fixed transverse point, is continuous in
the two null coordinates. -/
theorem continuous_dClampedStep_slice {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    Continuous fun p : ℝ × ℝ => deriv (fun w : ℂ => clampedStep V T w p.1 p.2) z := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hbase := continuousAt_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ (q := ((p, z) : (ℝ × ℝ) × ℂ)) hz
  have hcomp := hbase.comp (x := p)
    (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
    (continuous_id.prodMk continuous_const).continuousAt
  exact hcomp

/-- **The transverse derivative passes through the outer integration.** -/
theorem hasDerivAt_clampedOuter_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (ξ η : ℝ)
    {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (fun w : ℂ => ∫ s in (0 : ℝ)..ξ, clampedStep V T w s η)
      (∫ s in (0 : ℝ)..ξ, deriv (fun w : ℂ => clampedStep V T w s η) z) z := by
  refine hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun s w => clampedStep V T w s η) hρ₂ ?_ ?_ hz
  · intro q hq
    have hbase := continuousAt_clampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
      (q := (((q.1, η) : ℝ × ℝ), q.2)) hq.2
    have hcomp := hbase.comp (x := q)
      (f := fun q' : ℝ × ℂ => (((q'.1, η) : ℝ × ℝ), q'.2))
      ((continuous_fst.prodMk continuous_const).prodMk continuous_snd).continuousAt
    exact hcomp.continuousWithinAt
  · exact fun s => (differentiableOn_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s η).mono
      (imStrip_mono hρ₁.le)

/-- **The first null derivative of the transverse derivative.** -/
theorem hasDerivAt_deriv_clockSolution_transverse_fst {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T) {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (fun x : ℝ => deriv (clockSolution V x η) z)
      (∫ t in (0 : ℝ)..η, deriv (fun w : ℂ => clampedStep V T w ξ t) z) ξ := by
  have hslice := continuous_dClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hz
  have hinner : Continuous fun x : ℝ =>
      ∫ t in (0 : ℝ)..η, deriv (fun w : ℂ => clampedStep V T w x t) z :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (x : ℝ) (t : ℝ) => deriv (fun w : ℂ => clampedStep V T w x t) z)
      hslice continuous_const
  have hbase : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..η,
        deriv (fun w : ℂ => clampedStep V T w s t) z)
      (∫ t in (0 : ℝ)..η, deriv (fun w : ℂ => clampedStep V T w ξ t) z) ξ :=
    (hinner.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact (deriv_clockSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    (le_of_lt hx) hηT hz).deriv

/-- **The second null derivative of the transverse derivative.** -/
theorem hasDerivAt_deriv_clockSolution_transverse_snd {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hη : |η| < T) {z : ℂ} (hz : z ∈ imStrip ρ₂) :
    HasDerivAt (fun y : ℝ => deriv (clockSolution V ξ y) z)
      (∫ s in (0 : ℝ)..ξ, deriv (fun w : ℂ => clampedStep V T w s η) z) η := by
  have hslice := continuous_dClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hz
  have hswap : Continuous fun p : ℝ × ℝ =>
      deriv (fun w : ℂ => clampedStep V T w p.2 p.1) z :=
    hslice.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hjoint : Continuous fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..p.1, deriv (fun w : ℂ => clampedStep V T w p.2 t) z := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ =>
        deriv (fun w : ℂ => clampedStep V T w q.1.2 q.2) z :=
      hslice.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2) : ℝ × ℝ))
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (t : ℝ) => deriv (fun w : ℂ => clampedStep V T w p.2 t) z)
      huncurry continuous_fst
  have hderiv : ∀ y s : ℝ,
      HasDerivAt (fun v : ℝ => ∫ t in (0 : ℝ)..v, deriv (fun w : ℂ => clampedStep V T w s t) z)
        (deriv (fun w : ℂ => clampedStep V T w s y) z) y := by
    intro y s
    have hsl : Continuous fun t : ℝ => deriv (fun w : ℂ => clampedStep V T w s t) z :=
      hslice.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
    exact (hsl.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hpar := hasDerivAt_parametric_intervalIntegral
    (f := fun (y : ℝ) (s : ℝ) => ∫ t in (0 : ℝ)..y, deriv (fun w : ℂ => clampedStep V T w s t) z)
    (f' := fun (y : ℝ) (s : ℝ) => deriv (fun w : ℂ => clampedStep V T w s y) z)
    hjoint hswap hderiv 0 ξ η
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact (deriv_clockSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    hξT (le_of_lt hy) hz).deriv

/-- **The second transverse derivative of the solution**, which is free from its holomorphy. -/
theorem hasDerivAt_deriv_clockSolution_transverse {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁ : ρ₁ < ρ) {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : ℂ} (hz : z ∈ imStrip ρ₁) :
    HasDerivAt (deriv (clockSolution V ξ η))
      (deriv (deriv (clockSolution V ξ η)) z) z := by
  have hd : DifferentiableOn ℂ (deriv (clockSolution V ξ η)) (imStrip ρ₁) :=
    differentiableOn_deriv_of_holomorphic hρ₁
      (differentiableOn_clockSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT)
  exact (hd.differentiableAt ((isOpen_imStrip ρ₁).mem_nhds hz)).hasDerivAt

end GaloisForLFunctions.HTGeometry
