import GaloisForLFunctions.HTGeometry.ClockSolutionSecondTransverse

/-!
# The pure second derivative along the first null coordinate

The chart d'Alembertian reads second derivatives one direction at a time, so the pure derivatives
`∂ξ²u` and `∂η²u` are needed even though they cancel in the null combination. They are the one place
where the potential's own regularity in the null coordinates enters: differentiating

`S = (u'' + V u)/4`

along a null coordinate differentiates `V` there too.

Everything else is already available. The derivative of `u''` along the first null coordinate is the
fundamental theorem of calculus applied to `u'' = ∫∫ S''`, and the derivative of `u` along it is the
first null derivative. So the step operator is differentiable along the first null coordinate on the
open rectangle, with a derivative continuous on the whole plane, and the Leibniz rule then gives
`∂ξ²u`.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

/-- The second transverse derivative of the step operator applied to the solution. -/
noncomputable def d2ClampedStep (V : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (w : ℂ) (s t : ℝ) : ℂ :=
  deriv (fun v : ℂ => dClampedStep V T v s t) w

/-- **The second transverse derivative of the step operator is jointly continuous.** -/
theorem continuousAt_d2ClampedStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ₃) :
    ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => d2ClampedStep V T q'.2 q'.1.1 q'.1.2) q :=
  continuousAt_deriv_of_strip (ρ' := ρ₂) (P := ℝ × ℝ)
    (W := fun p : ℝ × ℝ => fun w : ℂ => dClampedStep V T w p.1 p.2) hρ₃ hρ₃0
    (continuousOn_dClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂)
    (fun p => (differentiableOn_dClampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁ p.1 p.2).mono
      (imStrip_mono hρ₂.le)) hq

theorem continuous_d2ClampedStep_slice {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    Continuous fun p : ℝ × ℝ => d2ClampedStep V T z p.1 p.2 := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hbase := continuousAt_d2ClampedStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ (q := ((p, z) : (ℝ × ℝ) × ℂ)) hz
  exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
    (continuous_id.prodMk continuous_const).continuousAt

/-- **The first null derivative of the second transverse derivative of the solution.** -/
theorem hasDerivAt_deriv_deriv_clockSolution_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun x : ℝ => deriv (deriv (clockSolution V x η)) z)
      (∫ t in (0 : ℝ)..η, d2ClampedStep V T z ξ t) ξ := by
  have hslice := continuous_d2ClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hinner : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..η, d2ClampedStep V T z x t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (x : ℝ) (t : ℝ) => d2ClampedStep V T z x t) hslice continuous_const
  have hbase : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..η, d2ClampedStep V T z s t)
      (∫ t in (0 : ℝ)..η, d2ClampedStep V T z ξ t) ξ :=
    (hinner.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact deriv_deriv_clockSolution_eq hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃
    (le_of_lt hx) hηT hz

/-! ## Potentials differentiable in the null coordinates -/

/-- A potential of the clock equation which is moreover continuously differentiable in the two null
coordinates. This is the regularity the pure second derivatives of the solution ask for. -/
structure StripPotentialC1 (V Vs Vt : ℝ → ℝ → ℂ → ℂ) (ρ : ℝ) : Prop where
  base : StripPotential V ρ
  hasDerivFst : ∀ (s t : ℝ), ∀ z ∈ imStrip ρ, HasDerivAt (fun x : ℝ => V x t z) (Vs s t z) s
  hasDerivSnd : ∀ (s t : ℝ), ∀ z ∈ imStrip ρ, HasDerivAt (fun x : ℝ => V s x z) (Vt s t z) t
  contFst : ContinuousOn (fun q : (ℝ × ℝ) × ℂ => Vs q.1.1 q.1.2 q.2) (univ ×ˢ imStrip ρ)
  contSnd : ContinuousOn (fun q : (ℝ × ℝ) × ℂ => Vt q.1.1 q.1.2 q.2) (univ ×ˢ imStrip ρ)

/-- The derivative of the step operator along the first null coordinate. -/
noncomputable def clampedStepFst (V Vs : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (z : ℂ) (s t : ℝ) : ℂ :=
  ((∫ r in (0 : ℝ)..t, d2ClampedStep V T z s r)
    + (Vs s t z * clockSolution V (boxClamp T s) (boxClamp T t) z
      + V s t z * ∫ r in (0 : ℝ)..t, clampedStep V T z s r)) / 4

/-- **The derivative of the step operator along the first null coordinate is continuous on the whole
plane of null coordinates.** -/
theorem continuous_clampedStepFst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    Continuous fun p : ℝ × ℝ => clampedStepFst V Vs T z p.1 p.2 := by
  have hV := hVC1.base
  have hz₀ : z ∈ imStrip ρ₀ :=
    imStrip_mono hρ.le (imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz)))
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ₀) :=
    isOpen_univ.prod (isOpen_imStrip ρ₀)
  -- the second transverse derivative, integrated
  have hslice2 := continuous_d2ClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hterm1 : Continuous fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..p.2, d2ClampedStep V T z p.1 r := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => d2ClampedStep V T z q.1.1 q.2 :=
      hslice2.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ))
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => d2ClampedStep V T z p.1 r) huncurry continuous_snd
  -- the step operator, integrated
  have hslice1 := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hterm3 : Continuous fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..p.2, clampedStep V T z p.1 r := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => clampedStep V T z q.1.1 q.2 :=
      hslice1.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ))
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => clampedStep V T z p.1 r) huncurry continuous_snd
  -- the potential and its derivative, at a fixed transverse point
  have hVcont : Continuous fun p : ℝ × ℝ => V p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ => V q.1.1 q.1.2 q.2) ((p, z) : (ℝ × ℝ) × ℂ) :=
      hV.cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  have hVscont : Continuous fun p : ℝ × ℝ => Vs p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ => Vs q.1.1 q.1.2 q.2)
        ((p, z) : (ℝ × ℝ) × ℂ) :=
      hVC1.contFst.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  -- the solution at clamped null coordinates
  have hUcont : Continuous fun p : ℝ × ℝ =>
      clockSolution V (boxClamp T p.1) (boxClamp T p.2) z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ =>
        clockSolution V (boxClamp T q.1.1) (boxClamp T q.1.2) q.2) ((p, z) : (ℝ × ℝ) × ℂ) :=
      (continuousOn_clockSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall).continuousAt
        ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hzmem⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  exact ((hterm1.add ((hVscont.mul hUcont).add (hVcont.mul hterm3))).div_const 4)

/-- **The step operator is differentiable along the first null coordinate**, inside the rectangle. -/
theorem hasDerivAt_clampedStep_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {s t : ℝ} (hs : |s| < T) (ht : |t| < T)
    {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun x : ℝ => clampedStep V T z x t) (clampedStepFst V Vs T z s t) s := by
  have hV := hVC1.base
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hz₀ : z ∈ imStrip ρ₀ := imStrip_mono hρ.le hzmem
  have h1 := hasDerivAt_deriv_deriv_clockSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ hs (le_of_lt ht) hz
  have h2 : HasDerivAt (fun x : ℝ => V x t z) (Vs s t z) s := hVC1.hasDerivFst s t z hz₀
  have h3 := hasDerivAt_clockSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hs (le_of_lt ht) hzρ
  have hmain := (h1.add (h2.mul h3)).div_const 4
  have hval : clampedStepFst V Vs T z s t
      = ((∫ r in (0 : ℝ)..t, d2ClampedStep V T z s r)
        + (Vs s t z * clockSolution V s t z
          + V s t z * ∫ r in (0 : ℝ)..t, clampedStep V T z s r)) / 4 := by
    rw [clampedStepFst, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  rw [hval]
  refine hmain.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hs) fun x hx => ?_
  exact clampedStep_eq (le_of_lt hx) (le_of_lt ht)

/-- **The pure second derivative of the solution along the first null coordinate.** -/
theorem hasDerivAt_deriv_clockSolution_fst_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {ξ η : ℝ} (hξ : |ξ| < T) (hη : |η| < T)
    {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => clockSolution V y η z) x)
      (∫ t in (0 : ℝ)..η, clampedStepFst V Vs T z ξ t) ξ := by
  have hV := hVC1.base
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hcont := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hcont' := continuous_clampedStepFst hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hpar := hasDerivAt_parametric_intervalIntegral_on
    (f := fun (x : ℝ) (t : ℝ) => clampedStep V T z x t)
    (f' := fun (x : ℝ) (t : ℝ) => clampedStepFst V Vs T z x t)
    (isOpen_absLt T) hξ hcont hcont' 0 η
    (fun x hx t htmem => hasDerivAt_clampedStep_fst hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ hx
      (lt_of_le_of_lt (abs_le_abs_of_mem_uIoc_zero htmem) hη) hz)
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact deriv_clockSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hx (le_of_lt hη) hzρ

end GaloisForLFunctions.HTGeometry
