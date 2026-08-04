import GaloisForLFunctions.HTGeometry.ClockTubeSumIntegral

/-!
# From the integral equation to the characteristic clock equation on a tube

The sum of the iterates satisfies

`u(ξ,η,z) = 1 + ∫₀^ξ ∫₀^η (∑ᵢ ∂ᵢ²u(s,t,·) + V·u(s,t,·))(z)/4 ds dt`,

on the rectangle `|ξ|, |η| ≤ T`. Differentiating once in each null coordinate returns the
characteristic form of the clock equation with several coupled transverse coordinates,

`∂η ∂ξ u = (∑ᵢ ∂ᵢ²u + V·u)/4`,

at every interior point. Both differentiations are the fundamental theorem of calculus for a
continuous integrand, transported from the clamped identity along an eventual equality on the open
rectangle.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

variable {k : ℕ}

/-- **The solution is the clamped double integral of the step operator.** -/
theorem tubeSolution_eq_clamped {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    tubeSolution V ξ η z
      = 1 + ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η, clampedTubeStep V T z s t := by
  rw [tubeSolution_integral_equation hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT hz]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hsb : |s| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero hs) hξT
  refine intervalIntegral.integral_congr fun t ht => ?_
  have htb : |t| ≤ T := le_trans (abs_le_abs_of_mem_uIcc_zero ht) hηT
  exact (clampedTubeStep_eq hsb htb).symm

/-- The inner integral of the clamped step is continuous in the outer null coordinate. -/
theorem continuous_clampedTubeInner {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) (η : ℝ) :
    Continuous fun s : ℝ => ∫ t in (0 : ℝ)..η, clampedTubeStep V T z s t :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s t : ℝ => clampedTubeStep V T z s t)
    (continuous_clampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz) 0 η

/-- **The solution is differentiable in the first null coordinate**, with the inner integral of the
step operator as derivative. -/
theorem hasDerivAt_tubeSolution_fst {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    HasDerivAt (fun x : ℝ => tubeSolution V x η z)
      (∫ t in (0 : ℝ)..η, clampedTubeStep V T z ξ t) ξ := by
  have hinner := continuous_clampedTubeInner hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz η
  have hbase : HasDerivAt
      (fun x : ℝ => 1 + ∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..η, clampedTubeStep V T z s t)
      (∫ t in (0 : ℝ)..η, clampedTubeStep V T z ξ t) ξ :=
    (hinner.integral_hasStrictDerivAt 0 ξ).hasDerivAt.const_add 1
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact tubeSolution_eq_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall (le_of_lt hx) hηT hz

/-- The derivative of the solution in the first null coordinate. -/
theorem deriv_tubeSolution_fst {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    deriv (fun x : ℝ => tubeSolution V x η z) ξ
      = ∫ t in (0 : ℝ)..η, clampedTubeStep V T z ξ t :=
  (hasDerivAt_tubeSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξ hηT hz).deriv

/-- **The characteristic clock equation on a tube.** The mixed derivative of the solution in the two
null coordinates is the step operator applied to the solution. -/
theorem hasDerivAt_deriv_tubeSolution {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {ξ η : ℝ} (hξ : |ξ| < T) (hη : |η| < T)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => tubeSolution V x y z) ξ)
      (tubeStep (V ξ η) (tubeSolution V ξ η) z) η := by
  have hslice : Continuous fun t : ℝ => clampedTubeStep V T z ξ t :=
    (continuous_clampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hz).comp
      (f := fun t : ℝ => ((ξ, t) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
  have hbase : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, clampedTubeStep V T z ξ t)
      (clampedTubeStep V T z ξ η) η := (hslice.integral_hasStrictDerivAt 0 η).hasDerivAt
  rw [← clampedTubeStep_eq (le_of_lt hξ) (le_of_lt hη)]
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact deriv_tubeSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξ (le_of_lt hy) hz

/-- The solution is normalised at the origin of the null coordinates. -/
theorem tubeSolution_zero_zero {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    {z : Fin k → ℂ} (hz : ∀ i, |(z i).im| ≤ ρ) :
    tubeSolution V 0 0 z = 1 := by
  have habs : |(0 : ℝ)| ≤ T := by simpa using hT
  rw [tubeSolution_eq_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall habs habs hz]
  simp

end GaloisForLFunctions.HTGeometry
