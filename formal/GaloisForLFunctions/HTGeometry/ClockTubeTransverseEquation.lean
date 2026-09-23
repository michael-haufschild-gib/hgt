import GaloisForLFunctions.HTGeometry.ClockTubeSolutionTransverseDeriv

/-!
# Differentiating the integral equation along a transverse coordinate

The two null derivatives of the solution are read off the integral equation by the fundamental
theorem of calculus and the Leibniz rule. A transverse partial derivative is read off it in a third
way: along the coordinate slice the integrand is holomorphic on a strip, uniformly, so the derivative
passes through both integrations.

The result is the transverse analogue of the two null formulas: the partial derivative of the
solution along a coordinate is the double integral of that partial derivative of the step operator.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The step operator applied to the solution is slice holomorphic in the transverse point. -/
theorem sliceHolo_clampedTubeStepFun {ρ₀ Mv ρ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1) (s t : ℝ) :
    SliceHolo (fun w : Fin k → ℂ => clampedTubeStep V T w s t) ρ := by
  have hcont : ContinuousOn
      (tubeSolution V (boxClamp T s) (boxClamp T t)) (tube k ρ) := by
    have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
      isOpen_univ.prod (isOpen_tube k ρ)
    have hjoint := continuousOn_tubeSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    intro y hy
    have hbase := hjoint.continuousAt
      (x := (((s, t) : ℝ × ℝ), y)) (hopen.mem_nhds ⟨mem_univ _, hy⟩)
    exact (hbase.comp (x := y)
      (f := fun y' : (Fin k → ℂ) => (((s, t) : ℝ × ℝ), y'))
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  exact sliceHolo_tubeStep
    (sliceHolo_mono (hV.holo (boxClamp T s) (boxClamp T t)) hρ.le) hcont
    (sliceHolo_tubeSolution hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      (abs_boxClamp_le hT s) (abs_boxClamp_le hT t))

/-- The step operator applied to the solution is jointly continuous on the tube. -/
theorem continuousOn_clampedTubeStep_joint {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) :
    ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) => clampedTubeStep V T r.2 r.1.1 r.1.2)
      (univ ×ˢ tube k ρ₁) := fun _ hq =>
  (continuousAt_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hq.2).continuousWithinAt

/-- The slice of the step operator through a point of the tube is continuous jointly with the null
coordinate. -/
theorem continuousOn_clampedTubeStep_slice {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (s : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₁) (i : Fin k) :
    ContinuousOn (fun q : ℝ × ℂ => clampedTubeStep V T (Function.update z i q.2) s q.1)
      (univ ×ˢ imStrip ρ₁) := by
  intro q hq
  have hmem : Function.update z i q.2 ∈ tube k ρ₁ := update_mem_tube hz i hq.2
  have hbase := continuousAt_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    (q := (((s, q.1) : ℝ × ℝ), Function.update z i q.2)) hmem
  have hmap : ContinuousAt (fun q' : ℝ × ℂ =>
      ((((s, q'.1) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ))) q :=
    ((continuous_const.prodMk continuous_fst).prodMk
      ((differentiable_updateSlice z i).continuous.comp continuous_snd)).continuousAt
  exact (hbase.comp (x := q)
    (f := fun q' : ℝ × ℂ =>
      ((((s, q'.1) : ℝ × ℝ), Function.update z i q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    hmap).continuousWithinAt

/-- **The transverse partial derivative passes through the inner integration.** -/
theorem hasDerivAt_clampedTubeInner_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (s η : ℝ)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (i : Fin k) :
    HasDerivAt (fun ζ : ℂ => ∫ t in (0 : ℝ)..η, clampedTubeStep V T (Function.update z i ζ) s t)
      (∫ t in (0 : ℝ)..η, cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z)
      (z i) := by
  have hz₁ : z ∈ tube k ρ₁ := tube_mono hρ₂.le hz
  exact hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun t ζ => clampedTubeStep V T (Function.update z i ζ) s t) hρ₂
    (continuousOn_clampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ s hz₁ i)
    (fun t => sliceHolo_mono
      (sliceHolo_clampedTubeStepFun hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t) hρ₁.le z hz₁ i)
    (mem_imStrip.mpr (hz i))

/-- The inner integral is slice holomorphic in the transverse point. -/
theorem differentiableOn_clampedTubeInner {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (s η : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₁) (i : Fin k) :
    DifferentiableOn ℂ
      (fun ζ : ℂ => ∫ t in (0 : ℝ)..η, clampedTubeStep V T (Function.update z i ζ) s t)
      (imStrip ρ₁) :=
  differentiableOn_intervalIntegral_of_holomorphic_on
    (F := fun t ζ => clampedTubeStep V T (Function.update z i ζ) s t)
    (continuousOn_clampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ s hz i)
    fun t => sliceHolo_mono
      (sliceHolo_clampedTubeStepFun hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t) hρ₁.le z hz i

/-- **The transverse partial derivative passes through both integrations.** -/
theorem hasDerivAt_clampedTubeBox_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁) (ξ η : ℝ)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (i : Fin k) :
    HasDerivAt
      (fun ζ : ℂ => ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        clampedTubeStep V T (Function.update z i ζ) s t)
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z) (z i) := by
  have hz₁ : z ∈ tube k ρ₁ := tube_mono hρ₂.le hz
  have hjoint := continuousOn_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0.le hρ₁
  have hbase := hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₁) (ρ := ρ₂)
    (F := fun s ζ => ∫ t in (0 : ℝ)..η, clampedTubeStep V T (Function.update z i ζ) s t)
    (a := 0) (b := ξ) hρ₂ ?_ ?_ (mem_imStrip.mpr (hz i))
  · have hval : (∫ s in (0 : ℝ)..ξ,
        deriv (fun ζ : ℂ => ∫ t in (0 : ℝ)..η,
          clampedTubeStep V T (Function.update z i ζ) s t) (z i))
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
          cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (hasDerivAt_clampedTubeInner_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
        hρ₁0.le hρ₁ hρ₂ s η hz i).deriv
    rwa [hval] at hbase
  · intro q hq
    have hmem : Function.update z i q.2 ∈ tube k ρ₁ := update_mem_tube hz₁ i hq.2
    obtain ⟨ρ', hρ'0, hρ'lt, hmem'⟩ := exists_inner_radius hρ₁0 hmem
    have hinner := continuousAt_innerIntegral_of_tube (ρ := ρ₁) (η := η)
      (H := fun s t w => clampedTubeStep V T w s t) hρ'lt hρ'0 hjoint
      (q := ((q.1, Function.update z i q.2) : ℝ × (Fin k → ℂ))) hmem'
    have hmap : ContinuousAt
        (fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ))) q :=
      (continuous_fst.prodMk
        ((differentiable_updateSlice z i).continuous.comp continuous_snd)).continuousAt
    exact (hinner.comp (x := q)
      (f := fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ)))
      hmap).continuousWithinAt
  · exact fun s => differentiableOn_clampedTubeInner hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0.le hρ₁ s η hz₁ i

/-- **The transverse partial derivative of the solution.** -/
theorem hasDerivAt_tubeSolution_transverse {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂ : ρ₂ < ρ₁)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (i : Fin k) :
    HasDerivAt (fun ζ : ℂ => tubeSolution V ξ η (Function.update z i ζ))
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => clampedTubeStep V T w s t) z) (z i) := by
  have hbox := hasDerivAt_clampedTubeBox_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂ ξ η hz i
  have hshift := hbox.const_add (1 : ℂ)
  refine hshift.congr_of_eventuallyEq ?_
  have hzρ : z ∈ tube k ρ := tube_mono hρ₁.le (tube_mono hρ₂.le hz)
  refine Filter.eventuallyEq_of_mem ((isOpen_imStrip ρ).mem_nhds
    (mem_imStrip.mpr (hzρ i))) fun ζ hζ => ?_
  have hmem : Function.update z i ζ ∈ tube k ρ := update_mem_tube hzρ i hζ
  exact tubeSolution_eq_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hξT hηT
    fun j => (hmem j).le

end GaloisForLFunctions.HTGeometry
