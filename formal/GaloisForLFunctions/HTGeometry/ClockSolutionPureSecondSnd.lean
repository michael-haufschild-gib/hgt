import GaloisForLFunctions.HTGeometry.ClockSolutionPureSecondFst

/-!
# The pure second derivative along the second null coordinate

The mirror of the previous file. The second null coordinate sits inside the outer integration, so
each step is the Leibniz rule where the first coordinate used the fundamental theorem of calculus;
nothing else changes.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

/-- **The second null derivative of the second transverse derivative of the solution.** -/
theorem hasDerivAt_deriv_deriv_clockSolution_snd {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → ℂ → ℂ} (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂)
    {ξ η : ℝ} (hξT : |ξ| ≤ T) (hη : |η| < T) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun y : ℝ => deriv (deriv (clockSolution V ξ y)) z)
      (∫ s in (0 : ℝ)..ξ, d2ClampedStep V T z s η) η := by
  have hslice := continuous_d2ClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hswap : Continuous fun p : ℝ × ℝ => d2ClampedStep V T z p.2 p.1 :=
    hslice.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hjoint : Continuous fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..p.1, d2ClampedStep V T z p.2 t := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => d2ClampedStep V T z q.1.2 q.2 :=
      hslice.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.2, q.2) : ℝ × ℝ))
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (t : ℝ) => d2ClampedStep V T z p.2 t) huncurry continuous_fst
  have hderiv : ∀ y s : ℝ,
      HasDerivAt (fun v : ℝ => ∫ t in (0 : ℝ)..v, d2ClampedStep V T z s t)
        (d2ClampedStep V T z s y) y := by
    intro y s
    have hsl : Continuous fun t : ℝ => d2ClampedStep V T z s t :=
      hslice.comp (f := fun t : ℝ => ((s, t) : ℝ × ℝ)) (continuous_const.prodMk continuous_id)
    exact (hsl.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hpar := hasDerivAt_parametric_intervalIntegral
    (f := fun (y : ℝ) (s : ℝ) => ∫ t in (0 : ℝ)..y, d2ClampedStep V T z s t)
    (f' := fun (y : ℝ) (s : ℝ) => d2ClampedStep V T z s y) hjoint hswap hderiv 0 ξ η
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact deriv_deriv_clockSolution_eq hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃
    hξT (le_of_lt hy) hz

/-- The derivative of the step operator along the second null coordinate. -/
noncomputable def clampedStepSnd (V Vt : ℝ → ℝ → ℂ → ℂ) (T : ℝ) (z : ℂ) (s t : ℝ) : ℂ :=
  ((∫ r in (0 : ℝ)..s, d2ClampedStep V T z r t)
    + (Vt s t z * clockSolution V (boxClamp T s) (boxClamp T t) z
      + V s t z * ∫ r in (0 : ℝ)..s, clampedStep V T z r t)) / 4

/-- **The derivative of the step operator along the second null coordinate is continuous on the
whole plane of null coordinates.** -/
theorem continuous_clampedStepSnd {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    Continuous fun p : ℝ × ℝ => clampedStepSnd V Vt T z p.1 p.2 := by
  have hV := hVC1.base
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hz₀ : z ∈ imStrip ρ₀ := imStrip_mono hρ.le hzmem
  have hopen : IsOpen ((univ : Set (ℝ × ℝ)) ×ˢ imStrip ρ₀) :=
    isOpen_univ.prod (isOpen_imStrip ρ₀)
  have hslice2 := continuous_d2ClampedStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hterm1 : Continuous fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..p.1, d2ClampedStep V T z r p.2 := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => d2ClampedStep V T z q.2 q.1.2 :=
      hslice2.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.2, q.1.2) : ℝ × ℝ))
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => d2ClampedStep V T z r p.2) huncurry continuous_fst
  have hslice1 := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hterm3 : Continuous fun p : ℝ × ℝ => ∫ r in (0 : ℝ)..p.1, clampedStep V T z r p.2 := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => clampedStep V T z q.2 q.1.2 :=
      hslice1.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.2, q.1.2) : ℝ × ℝ))
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => clampedStep V T z r p.2) huncurry continuous_fst
  have hVcont : Continuous fun p : ℝ × ℝ => V p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ => V q.1.1 q.1.2 q.2) ((p, z) : (ℝ × ℝ) × ℂ) :=
      hV.cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  have hVtcont : Continuous fun p : ℝ × ℝ => Vt p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ => Vt q.1.1 q.1.2 q.2)
        ((p, z) : (ℝ × ℝ) × ℂ) :=
      hVC1.contSnd.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  have hUcont : Continuous fun p : ℝ × ℝ =>
      clockSolution V (boxClamp T p.1) (boxClamp T p.2) z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × ℂ =>
        clockSolution V (boxClamp T q.1.1) (boxClamp T q.1.2) q.2) ((p, z) : (ℝ × ℝ) × ℂ) :=
      (continuousOn_clockSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall).continuousAt
        ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hzmem⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ))
      (continuous_id.prodMk continuous_const).continuousAt
  exact ((hterm1.add ((hVtcont.mul hUcont).add (hVcont.mul hterm3))).div_const 4)

/-- **The step operator is differentiable along the second null coordinate**, inside the
rectangle. -/
theorem hasDerivAt_clampedStep_snd {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {s t : ℝ} (hs : |s| < T) (ht : |t| < T)
    {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun y : ℝ => clampedStep V T z s y) (clampedStepSnd V Vt T z s t) t := by
  have hV := hVC1.base
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hz₀ : z ∈ imStrip ρ₀ := imStrip_mono hρ.le hzmem
  have h1 := hasDerivAt_deriv_deriv_clockSolution_snd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ (le_of_lt hs) ht hz
  have h2 : HasDerivAt (fun y : ℝ => V s y z) (Vt s t z) t := hVC1.hasDerivSnd s t z hz₀
  have h3 := hasDerivAt_clockSolution_snd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall (le_of_lt hs) ht hzρ
  have hmain := (h1.add (h2.mul h3)).div_const 4
  have hval : clampedStepSnd V Vt T z s t
      = ((∫ r in (0 : ℝ)..s, d2ClampedStep V T z r t)
        + (Vt s t z * clockSolution V s t z
          + V s t z * ∫ r in (0 : ℝ)..s, clampedStep V T z r t)) / 4 := by
    rw [clampedStepSnd, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  rw [hval]
  refine hmain.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds ht) fun y hy => ?_
  exact clampedStep_eq (le_of_lt hs) (le_of_lt hy)

/-- **The pure second derivative of the solution along the second null coordinate.** -/
theorem hasDerivAt_deriv_clockSolution_snd_snd {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → ℂ → ℂ} (hVC1 : StripPotentialC1 V Vs Vt ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {ξ η : ℝ} (hξ : |ξ| < T) (hη : |η| < T)
    {z : ℂ} (hz : z ∈ imStrip ρ₃) :
    HasDerivAt (fun y : ℝ => deriv (fun x : ℝ => clockSolution V ξ x z) y)
      (∫ s in (0 : ℝ)..ξ, clampedStepSnd V Vt T z s η) η := by
  have hV := hVC1.base
  have hzmem : z ∈ imStrip ρ :=
    imStrip_mono hρ₁.le (imStrip_mono hρ₂.le (imStrip_mono hρ₃.le hz))
  have hzρ : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hzmem)
  have hcont0 := continuous_clampedStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hcont0' := continuous_clampedStepSnd hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ hz
  have hcont : Continuous fun p : ℝ × ℝ => clampedStep V T z p.2 p.1 :=
    hcont0.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hcont' : Continuous fun p : ℝ × ℝ => clampedStepSnd V Vt T z p.2 p.1 :=
    hcont0'.comp (f := fun p : ℝ × ℝ => ((p.2, p.1) : ℝ × ℝ))
      (continuous_snd.prodMk continuous_fst)
  have hpar := hasDerivAt_parametric_intervalIntegral_on
    (f := fun (y : ℝ) (s : ℝ) => clampedStep V T z s y)
    (f' := fun (y : ℝ) (s : ℝ) => clampedStepSnd V Vt T z s y)
    (isOpen_absLt T) hη hcont hcont' 0 ξ
    (fun y hy s hsmem => hasDerivAt_clampedStep_snd hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃
      (lt_of_le_of_lt (abs_le_abs_of_mem_uIoc_zero hsmem) hξ) hy hz)
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hη) fun y hy => ?_
  exact deriv_clockSolution_snd hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall (le_of_lt hξ) hy hzρ

end GaloisForLFunctions.HTGeometry
