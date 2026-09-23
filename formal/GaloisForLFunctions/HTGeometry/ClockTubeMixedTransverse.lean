import GaloisForLFunctions.HTGeometry.ClockTubeTransverseEquation

/-!
# The mixed null–transverse derivatives on a tube

The transverse partial derivative of the solution is the double integral of that partial derivative
of the step operator. That identity has the same shape as the integral equation itself, so
differentiating it along a null coordinate repeats the two arguments already used there: the
fundamental theorem of calculus for the outer integration, the Leibniz rule for the inner one.

What has to be checked first is that the transverse partial derivative of the step operator is
jointly continuous, and that is the Cauchy representation along the coordinate slice.

The second pure transverse derivative is free: along its own coordinate the solution is holomorphic,
hence so is its partial derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- **The transverse partial derivative of the step operator is jointly continuous.** -/
theorem continuousAt_dClampedTubeStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₂) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w q'.1.1 q'.1.2) q'.2) q :=
  continuousAt_cpartial_of_tube (ρ' := ρ₁) (P := ℝ × ℝ)
    (W := fun p : ℝ × ℝ => fun w : Fin k → ℂ => clampedTubeStep V T w p.1 p.2) hρ₂ hρ₂0
    (continuousOn_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁)
    (fun p => sliceHolo_mono
      (sliceHolo_clampedTubeStepFun hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall p.1 p.2) hρ₁.le) i hq

/-- The transverse partial derivative of the step operator, at a fixed transverse point, is
continuous in the two null coordinates. -/
theorem continuous_dClampedTubeStep_slice {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) :
    Continuous fun p : ℝ × ℝ =>
      cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w p.1 p.2) z := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hbase := continuousAt_dClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ i (q := ((p, z) : (ℝ × ℝ) × (Fin k → ℂ))) hz
  exact hbase.comp (x := p)
    (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ)))
    (continuous_id.prodMk continuous_const).continuousAt

/-- **The first null derivative of the transverse partial derivative.** -/
theorem hasDerivAt_cpartial_tubeSolution_fst {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) :
    HasDerivAt (fun x : ℝ => cpartial i (tubeSolution V x η) z)
      (∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w ξ t) z) ξ := by
  have hslice := continuous_dClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0.le hρ₁
    hρ₂0 hρ₂ i hz
  have hinner : Continuous fun x : ℝ =>
      ∫ t in (0 : ℝ)..η, cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w x t) z :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (x : ℝ) (t : ℝ) =>
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w x t) z)
      hslice continuous_const
  have hbase : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z)
      (∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w ξ t) z) ξ :=
    (hinner.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact (hasDerivAt_tubeSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    (le_of_lt hx) hηT hz i).deriv

/-- **The second null derivative of the transverse partial derivative.** -/
theorem hasDerivAt_cpartial_tubeSolution_snd {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hη : |η| < T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) :
    HasDerivAt (fun y : ℝ => cpartial i (tubeSolution V ξ y) z)
      (∫ s in (0 : ℝ)..ξ,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s η) z) η := by
  have hslice := continuous_dClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0.le hρ₁
    hρ₂0 hρ₂ i hz
  have hswap : Continuous fun p : ℝ × ℝ =>
      cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w p.2 p.1) z :=
    hslice.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hjoint : Continuous fun p : ℝ × ℝ =>
      ∫ t in (0 : ℝ)..p.1, cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w p.2 t) z := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ =>
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w q.1.2 q.2) z :=
      hslice.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2) : ℝ × ℝ))
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (t : ℝ) =>
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w p.2 t) z)
      huncurry continuous_fst
  have hderiv : ∀ y s : ℝ,
      HasDerivAt
        (fun v : ℝ => ∫ t in (0 : ℝ)..v,
          cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z)
        (cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s y) z) y := by
    intro y s
    have hsl : Continuous fun t : ℝ =>
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z :=
      hslice.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
    exact (hsl.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hpar := hasDerivAt_parametric_intervalIntegral
    (f := fun (y : ℝ) (s : ℝ) => ∫ t in (0 : ℝ)..y,
      cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z)
    (f' := fun (y : ℝ) (s : ℝ) =>
      cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s y) z)
    hjoint hswap hderiv 0 ξ η
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact (hasDerivAt_tubeSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂
    hξT (le_of_lt hy) hz i).deriv

/-- **The second transverse derivative along a coordinate**, which is free from the holomorphy of the
solution along that coordinate. -/
theorem hasDerivAt_cpartial_tubeSolution_transverse {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁ : ρ₁ < ρ) {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₁) (i : Fin k) :
    HasDerivAt (fun ζ : ℂ => cpartial i (tubeSolution V ξ η) (Function.update z i ζ))
      (cpartial i (cpartial i (tubeSolution V ξ η)) z) (z i) := by
  have hslice : DifferentiableOn ℂ
      (fun ζ : ℂ => tubeSolution V ξ η (Function.update z i ζ)) (imStrip ρ) :=
    sliceHolo_tubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT z (tube_mono hρ₁.le hz) i
  have hd : DifferentiableOn ℂ
      (deriv fun ζ : ℂ => tubeSolution V ξ η (Function.update z i ζ)) (imStrip ρ₁) :=
    differentiableOn_deriv_of_holomorphic hρ₁ hslice
  have hbase := (hd.differentiableAt ((isOpen_imStrip ρ₁).mem_nhds
    (mem_imStrip.mpr (hz i)))).hasDerivAt
  rw [cpartial_cpartial_eq, cpartial_update_eq_deriv_slice]
  exact hbase

end GaloisForLFunctions.HTGeometry
