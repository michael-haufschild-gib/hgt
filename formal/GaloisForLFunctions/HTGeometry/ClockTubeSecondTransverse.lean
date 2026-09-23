import GaloisForLFunctions.HTGeometry.ClockTubeMixedTransverse
import GaloisForLFunctions.HTGeometry.ClockTubeSliceHoloFirst

/-!
# The second transverse derivative of the integral equation on a tube

The transverse partial derivative of the solution is the double integral of that partial derivative
of the step operator. That identity has exactly the shape of the integral equation itself, so the
argument that produced it produces its own derivative in turn: the second partial derivative along a
coordinate is the double integral of the second partial derivative of the step operator.

This is what makes the pure second derivative along a null coordinate accessible: differentiating
`∂ᵢ²u` along a null coordinate is the fundamental theorem of calculus applied to that double
integral.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

variable {k : ℕ}

/-- The transverse partial derivative of the step operator applied to the solution. -/
noncomputable def dClampedTubeStep (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i : Fin k)
    (w : Fin k → ℂ) (s t : ℝ) : ℂ :=
  cpartial i (fun v : Fin k → ℂ => clampedTubeStep V T v s t) w

/-- The step operator applied to the solution is continuous in the transverse point alone. -/
theorem continuousOn_clampedTubeStep_fixed {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (s t : ℝ) :
    ContinuousOn (fun w : Fin k → ℂ => clampedTubeStep V T w s t) (tube k ρ₁) := by
  intro y hy
  have hbase := continuousAt_clampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    (q := (((s, t) : ℝ × ℝ), y)) hy
  exact (hbase.comp (x := y)
    (f := fun y' : (Fin k → ℂ) => (((s, t) : ℝ × ℝ), y'))
    (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt

/-- **The transverse partial derivative of the step operator is slice holomorphic.** -/
theorem sliceHolo_dClampedTubeStep {ρ₀ Mv ρ ρ₁ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (i : Fin k) (s t : ℝ) :
    SliceHolo (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) ρ₁ :=
  sliceHolo_cpartial
    (continuousOn_clampedTubeStep_fixed hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ s t)
    (sliceHolo_mono (sliceHolo_clampedTubeStepFun hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall s t)
      hρ₁.le) i

/-- The transverse partial derivative of the step operator is jointly continuous on the tube. -/
theorem continuousOn_dClampedTubeStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k) :
    ContinuousOn (fun r : (ℝ × ℝ) × (Fin k → ℂ) => dClampedTubeStep V T i r.2 r.1.1 r.1.2)
      (univ ×ˢ tube k ρ₂) := fun _ hq =>
  (continuousAt_dClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ i
    hq.2).continuousWithinAt

/-- The slice of the transverse partial derivative of the step operator, jointly with the null
coordinate. -/
theorem continuousOn_dClampedTubeStep_slice {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k) (s : ℝ)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (j : Fin k) :
    ContinuousOn (fun q : ℝ × ℂ => dClampedTubeStep V T i (Function.update z j q.2) s q.1)
      (univ ×ˢ imStrip ρ₂) := by
  intro q hq
  have hmem : Function.update z j q.2 ∈ tube k ρ₂ := update_mem_tube hz j hq.2
  have hbase := continuousAt_dClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ i (q := (((s, q.1) : ℝ × ℝ), Function.update z j q.2)) hmem
  have hmap : ContinuousAt (fun q' : ℝ × ℂ =>
      ((((s, q'.1) : ℝ × ℝ), Function.update z j q'.2) : (ℝ × ℝ) × (Fin k → ℂ))) q :=
    ((continuous_const.prodMk continuous_fst).prodMk
      ((differentiable_updateSlice z j).continuous.comp continuous_snd)).continuousAt
  exact (hbase.comp (x := q)
    (f := fun q' : ℝ × ℂ =>
      ((((s, q'.1) : ℝ × ℝ), Function.update z j q'.2) : (ℝ × ℝ) × (Fin k → ℂ)))
    hmap).continuousWithinAt

/-- **The second transverse derivative passes through the inner integration.** -/
theorem hasDerivAt_dClampedTubeInner_transverse {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (i : Fin k) (s η : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt
      (fun ζ : ℂ => ∫ t in (0 : ℝ)..η, dClampedTubeStep V T i (Function.update z i ζ) s t)
      (∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) z) (z i) := by
  have hz₂ : z ∈ tube k ρ₂ := tube_mono hρ₃.le hz
  exact hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₂) (ρ := ρ₃)
    (F := fun t ζ => dClampedTubeStep V T i (Function.update z i ζ) s t) hρ₃
    (continuousOn_dClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂
      i s hz₂ i)
    (fun t => sliceHolo_mono
      (sliceHolo_dClampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ i s t) hρ₂.le
      z hz₂ i)
    (mem_imStrip.mpr (hz i))

/-- The inner integral of the transverse partial derivative of the step operator is slice
holomorphic. -/
theorem differentiableOn_dClampedTubeInner {ρ₀ Mv ρ ρ₁ ρ₂ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁) (i : Fin k) (s η : ℝ)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₂) (j : Fin k) :
    DifferentiableOn ℂ
      (fun ζ : ℂ => ∫ t in (0 : ℝ)..η, dClampedTubeStep V T i (Function.update z j ζ) s t)
      (imStrip ρ₂) :=
  differentiableOn_intervalIntegral_of_holomorphic_on
    (F := fun t ζ => dClampedTubeStep V T i (Function.update z j ζ) s t)
    (continuousOn_dClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂
      i s hz j)
    fun t => sliceHolo_mono
      (sliceHolo_dClampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ i s t) hρ₂.le z hz j

/-- **The second transverse derivative passes through both integrations.** -/
theorem hasDerivAt_dClampedTubeBox_transverse {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (i : Fin k) (ξ η : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt
      (fun ζ : ℂ => ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        dClampedTubeStep V T i (Function.update z i ζ) s t)
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) z) (z i) := by
  have hz₂ : z ∈ tube k ρ₂ := tube_mono hρ₃.le hz
  have hjoint := continuousOn_dClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0 hρ₁ hρ₂0.le hρ₂ i
  have hbase := hasDerivAt_intervalIntegral_of_holomorphic_on (ρ' := ρ₂) (ρ := ρ₃)
    (F := fun s ζ => ∫ t in (0 : ℝ)..η, dClampedTubeStep V T i (Function.update z i ζ) s t)
    (a := 0) (b := ξ) hρ₃ ?_ ?_ (mem_imStrip.mpr (hz i))
  · have hval : (∫ s in (0 : ℝ)..ξ,
        deriv (fun ζ : ℂ => ∫ t in (0 : ℝ)..η,
          dClampedTubeStep V T i (Function.update z i ζ) s t) (z i))
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
          cpartial i (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) z := by
      refine intervalIntegral.integral_congr fun s _ => ?_
      exact (hasDerivAt_dClampedTubeInner_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
        hρ₁0 hρ₁ hρ₂0.le hρ₂ hρ₃ i s η hz).deriv
    rwa [hval] at hbase
  · intro q hq
    have hmem : Function.update z i q.2 ∈ tube k ρ₂ := update_mem_tube hz₂ i hq.2
    obtain ⟨ρ', hρ'0, hρ'lt, hmem'⟩ := exists_inner_radius hρ₂0 hmem
    have hinner := continuousAt_innerIntegral_of_tube (ρ := ρ₂) (η := η)
      (H := fun s t w => dClampedTubeStep V T i w s t) hρ'lt hρ'0 hjoint
      (q := ((q.1, Function.update z i q.2) : ℝ × (Fin k → ℂ))) hmem'
    have hmap : ContinuousAt
        (fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ))) q :=
      (continuous_fst.prodMk
        ((differentiable_updateSlice z i).continuous.comp continuous_snd)).continuousAt
    exact (hinner.comp (x := q)
      (f := fun q' : ℝ × ℂ => ((q'.1, Function.update z i q'.2) : ℝ × (Fin k → ℂ)))
      hmap).continuousWithinAt
  · exact fun s => differentiableOn_dClampedTubeInner hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ hρ₂0.le hρ₂ i s η hz₂ i

/-- **The second transverse derivative of the solution along a coordinate.** -/
theorem hasDerivAt_cpartial_tubeSolution_box {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (i : Fin k) {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt (fun ζ : ℂ => cpartial i (tubeSolution V ξ η) (Function.update z i ζ))
      (∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) z) (z i) := by
  have hbox := hasDerivAt_dClampedTubeBox_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0.le hρ₁ hρ₂0 hρ₂ hρ₃ i ξ η hz
  refine hbox.congr_of_eventuallyEq ?_
  have hz₂ : z ∈ tube k ρ₂ := tube_mono hρ₃.le hz
  refine Filter.eventuallyEq_of_mem ((isOpen_imStrip ρ₂).mem_nhds
    (mem_imStrip.mpr (hz₂ i))) fun ζ hζ => ?_
  have hmem : Function.update z i ζ ∈ tube k ρ₂ := update_mem_tube hz₂ i hζ
  have hbase := (hasDerivAt_tubeSolution_transverse hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0 hρ₁ hρ₂ hξT hηT hmem i).deriv
  have hupd : ((Function.update z i ζ) i) = ζ := Function.update_self i ζ z
  rw [hupd] at hbase
  have hidem : (fun ζ' : ℂ =>
      tubeSolution V ξ η (Function.update (Function.update z i ζ) i ζ'))
      = fun ζ' : ℂ => tubeSolution V ξ η (Function.update z i ζ') := by
    funext ζ'
    rw [Function.update_idem]
  rw [hidem] at hbase
  rw [cpartial_update_same i (tubeSolution V ξ η) z ζ]
  exact hbase

/-- The second transverse derivative of the solution along a coordinate, as a double integral. -/
theorem cpartial_cpartial_tubeSolution_eq {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁) (hρ₃ : ρ₃ < ρ₂)
    (i : Fin k) {ξ η : ℝ} (hξT : |ξ| ≤ T) (hηT : |η| ≤ T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    cpartial i (cpartial i (tubeSolution V ξ η)) z
      = ∫ s in (0 : ℝ)..ξ, ∫ t in (0 : ℝ)..η,
        cpartial i (fun w : Fin k → ℂ => dClampedTubeStep V T i w s t) z :=
  (hasDerivAt_cpartial_tubeSolution_box hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃
    i hξT hηT hz).deriv

end GaloisForLFunctions.HTGeometry
