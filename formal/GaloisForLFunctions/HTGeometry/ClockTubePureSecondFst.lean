import GaloisForLFunctions.HTGeometry.ClockTubeSecondTransverse

/-!
# The pure second derivative along the first null coordinate, on a tube

The chart d'Alembertian reads second derivatives one direction at a time, so the pure derivatives
`∂ξ²u` and `∂η²u` are needed even though they cancel in the null combination. They are the one place
where the potential's own regularity in the null coordinates enters: differentiating

`S = (∑ᵢ ∂ᵢ²u + V u)/4`

along a null coordinate differentiates `V` there too.

Everything else is already available. The derivative of each `∂ᵢ²u` along the first null coordinate
is the fundamental theorem of calculus applied to `∂ᵢ²u = ∫∫ ∂ᵢ²S`, and the derivative of `u` along
it is the first null derivative. The `k` coordinates contribute a finite sum, which differentiates
term by term.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped Interval

variable {k : ℕ}

/-- The second transverse partial derivative of the step operator applied to the solution. -/
noncomputable def d2ClampedTubeStep (V : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (i : Fin k)
    (w : Fin k → ℂ) (s t : ℝ) : ℂ :=
  cpartial i (fun v : Fin k → ℂ => dClampedTubeStep V T i v s t) w

/-- **The second transverse partial derivative of the step operator is jointly continuous.** -/
theorem continuousAt_d2ClampedTubeStep_joint {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) (i : Fin k)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ₃) :
    ContinuousAt (fun q' : (ℝ × ℝ) × (Fin k → ℂ) =>
      d2ClampedTubeStep V T i q'.2 q'.1.1 q'.1.2) q :=
  continuousAt_cpartial_of_tube (ρ' := ρ₂) (P := ℝ × ℝ)
    (W := fun p : ℝ × ℝ => fun w : Fin k → ℂ => dClampedTubeStep V T i w p.1 p.2) hρ₃ hρ₃0
    (continuousOn_dClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂ i)
    (fun p => sliceHolo_mono
      (sliceHolo_dClampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ i p.1 p.2) hρ₂.le)
    i hq

theorem continuous_d2ClampedTubeStep_slice {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) (i : Fin k) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    Continuous fun p : ℝ × ℝ => d2ClampedTubeStep V T i z p.1 p.2 := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hbase := continuousAt_d2ClampedTubeStep_joint hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁
    hρ₂0 hρ₂ hρ₃0 hρ₃ i (q := ((p, z) : (ℝ × ℝ) × (Fin k → ℂ))) hz
  exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ)))
    (continuous_id.prodMk continuous_const).continuousAt

/-- **The first null derivative of the second transverse derivative of the solution.** -/
theorem hasDerivAt_cpartial_cpartial_tubeSolution_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) (i : Fin k)
    {ξ η : ℝ} (hξ : |ξ| < T) (hηT : |η| ≤ T) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt (fun x : ℝ => cpartial i (cpartial i (tubeSolution V x η)) z)
      (∫ t in (0 : ℝ)..η, d2ClampedTubeStep V T i z ξ t) ξ := by
  have hslice := continuous_d2ClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
    hρ₁0.le hρ₁ hρ₂0.le hρ₂ hρ₃0 hρ₃ i hz
  have hinner : Continuous fun x : ℝ => ∫ t in (0 : ℝ)..η, d2ClampedTubeStep V T i z x t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (x : ℝ) (t : ℝ) => d2ClampedTubeStep V T i z x t) hslice continuous_const
  have hbase : HasDerivAt
      (fun x : ℝ => ∫ s in (0 : ℝ)..x, ∫ t in (0 : ℝ)..η, d2ClampedTubeStep V T i z s t)
      (∫ t in (0 : ℝ)..η, d2ClampedTubeStep V T i z ξ t) ξ :=
    (hinner.integral_hasStrictDerivAt 0 ξ).hasDerivAt
  refine hbase.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact cpartial_cpartial_tubeSolution_eq hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hρ₁0 hρ₁ hρ₂0 hρ₂
    hρ₃ i (le_of_lt hx) hηT hz

/-! ## Potentials differentiable in the null coordinates -/

/-- A potential of the clock equation on a tube which is moreover continuously differentiable in the
two null coordinates. -/
structure TubePotentialC1 (V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (ρ : ℝ) : Prop where
  base : TubePotential V ρ
  hasDerivFst : ∀ (s t : ℝ), ∀ z ∈ tube k ρ, HasDerivAt (fun x : ℝ => V x t z) (Vs s t z) s
  hasDerivSnd : ∀ (s t : ℝ), ∀ z ∈ tube k ρ, HasDerivAt (fun x : ℝ => V s x z) (Vt s t z) t
  contFst : ContinuousOn (fun q : (ℝ × ℝ) × (Fin k → ℂ) => Vs q.1.1 q.1.2 q.2) (univ ×ˢ tube k ρ)
  contSnd : ContinuousOn (fun q : (ℝ × ℝ) × (Fin k → ℂ) => Vt q.1.1 q.1.2 q.2) (univ ×ˢ tube k ρ)

/-- The derivative of the step operator along the first null coordinate. -/
noncomputable def clampedTubeStepFst (V Vs : ℝ → ℝ → (Fin k → ℂ) → ℂ) (T : ℝ) (z : Fin k → ℂ)
    (s t : ℝ) : ℂ :=
  ((∑ i, ∫ r in (0 : ℝ)..t, d2ClampedTubeStep V T i z s r)
    + (Vs s t z * tubeSolution V (boxClamp T s) (boxClamp T t) z
      + V s t z * ∫ r in (0 : ℝ)..t, clampedTubeStep V T z s r)) / 4

/-- **The derivative of the step operator along the first null coordinate is continuous on the whole
plane of null coordinates.** -/
theorem continuous_clampedTubeStepFst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hVC1 : TubePotentialC1 V Vs Vt ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    Continuous fun p : ℝ × ℝ => clampedTubeStepFst V Vs T z p.1 p.2 := by
  classical
  have hV := hVC1.base
  have hzmem : z ∈ tube k ρ := tube_mono hρ₁.le (tube_mono hρ₂.le (tube_mono hρ₃.le hz))
  have hz₀ : z ∈ tube k ρ₀ := tube_mono hρ.le hzmem
  have hzρ : ∀ i, |(z i).im| ≤ ρ := fun i => (hzmem i).le
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ₀) :=
    isOpen_univ.prod (isOpen_tube k ρ₀)
  -- the second transverse derivatives, integrated
  have hterm1 : Continuous fun p : ℝ × ℝ =>
      ∑ i, ∫ r in (0 : ℝ)..p.2, d2ClampedTubeStep V T i z p.1 r := by
    refine continuous_finsetSum Finset.univ fun i _ => ?_
    have hslice2 := continuous_d2ClampedTubeStep_slice hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ i hz
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => d2ClampedTubeStep V T i z q.1.1 q.2 :=
      hslice2.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ))
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => d2ClampedTubeStep V T i z p.1 r) huncurry continuous_snd
  -- the step operator, integrated
  have hslice1 := continuous_clampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hterm3 : Continuous fun p : ℝ × ℝ =>
      ∫ r in (0 : ℝ)..p.2, clampedTubeStep V T z p.1 r := by
    have huncurry : Continuous fun q : (ℝ × ℝ) × ℝ => clampedTubeStep V T z q.1.1 q.2 :=
      hslice1.comp (f := fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.2) : ℝ × ℝ))
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (r : ℝ) => clampedTubeStep V T z p.1 r) huncurry continuous_snd
  -- the potential and its derivative, at a fixed transverse point
  have hVcont : Continuous fun p : ℝ × ℝ => V p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × (Fin k → ℂ) => V q.1.1 q.1.2 q.2)
        ((p, z) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      hV.cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ)))
      (continuous_id.prodMk continuous_const).continuousAt
  have hVscont : Continuous fun p : ℝ × ℝ => Vs p.1 p.2 z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × (Fin k → ℂ) => Vs q.1.1 q.1.2 q.2)
        ((p, z) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      hVC1.contFst.continuousAt (hopen.mem_nhds ⟨mem_univ _, hz₀⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ)))
      (continuous_id.prodMk continuous_const).continuousAt
  -- the solution at clamped null coordinates
  have hUcont : Continuous fun p : ℝ × ℝ =>
      tubeSolution V (boxClamp T p.1) (boxClamp T p.2) z := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    have hbase : ContinuousAt (fun q : (ℝ × ℝ) × (Fin k → ℂ) =>
        tubeSolution V (boxClamp T q.1.1) (boxClamp T q.1.2) q.2)
        ((p, z) : (ℝ × ℝ) × (Fin k → ℂ)) :=
      (continuousOn_tubeSolution_clamped hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall).continuousAt
        ((isOpen_univ.prod (isOpen_tube k ρ)).mem_nhds ⟨mem_univ _, hzmem⟩)
    exact hbase.comp (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ)))
      (continuous_id.prodMk continuous_const).continuousAt
  exact ((hterm1.add ((hVscont.mul hUcont).add (hVcont.mul hterm3))).div_const 4)

/-- **The step operator is differentiable along the first null coordinate**, inside the
rectangle. -/
theorem hasDerivAt_clampedTubeStep_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hVC1 : TubePotentialC1 V Vs Vt ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {s t : ℝ} (hs : |s| < T) (ht : |t| < T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt (fun x : ℝ => clampedTubeStep V T z x t) (clampedTubeStepFst V Vs T z s t) s := by
  classical
  have hV := hVC1.base
  have hzmem : z ∈ tube k ρ := tube_mono hρ₁.le (tube_mono hρ₂.le (tube_mono hρ₃.le hz))
  have hzρ : ∀ i, |(z i).im| ≤ ρ := fun i => (hzmem i).le
  have hz₀ : z ∈ tube k ρ₀ := tube_mono hρ.le hzmem
  have h1 : HasDerivAt
      (fun x : ℝ => ∑ i, cpartial i (cpartial i (tubeSolution V x t)) z)
      (∑ i, ∫ r in (0 : ℝ)..t, d2ClampedTubeStep V T i z s r) s := by
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        HasDerivAt (fun x : ℝ => cpartial i (cpartial i (tubeSolution V x t)) z)
          (∫ r in (0 : ℝ)..t, d2ClampedTubeStep V T i z s r) s := fun i _ =>
      hasDerivAt_cpartial_cpartial_tubeSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall
        hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ i hs (le_of_lt ht) hz
    have hbase := HasDerivAt.sum (u := (Finset.univ : Finset (Fin k)))
      (A := fun (i : Fin k) (x : ℝ) => cpartial i (cpartial i (tubeSolution V x t)) z)
      (A' := fun i => ∫ r in (0 : ℝ)..t, d2ClampedTubeStep V T i z s r) hterm
    have heq : (∑ i : Fin k, fun x : ℝ => cpartial i (cpartial i (tubeSolution V x t)) z)
        = fun x : ℝ => ∑ i, cpartial i (cpartial i (tubeSolution V x t)) z := by
      funext x
      simp [Finset.sum_apply]
    rwa [heq] at hbase
  have h2 : HasDerivAt (fun x : ℝ => V x t z) (Vs s t z) s := hVC1.hasDerivFst s t z hz₀
  have h3 := hasDerivAt_tubeSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hs (le_of_lt ht) hzρ
  have hmain := (h1.add (h2.mul h3)).div_const 4
  have hval : clampedTubeStepFst V Vs T z s t
      = ((∑ i, ∫ r in (0 : ℝ)..t, d2ClampedTubeStep V T i z s r)
        + (Vs s t z * tubeSolution V s t z
          + V s t z * ∫ r in (0 : ℝ)..t, clampedTubeStep V T z s r)) / 4 := by
    rw [clampedTubeStepFst, boxClamp_eq_self (le_of_lt hs), boxClamp_eq_self (le_of_lt ht)]
  rw [hval]
  refine hmain.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hs) fun x hx => ?_
  exact clampedTubeStep_eq (le_of_lt hx) (le_of_lt ht)

/-- **The pure second derivative of the solution along the first null coordinate.** -/
theorem hasDerivAt_deriv_tubeSolution_fst_fst {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hVC1 : TubePotentialC1 V Vs Vt ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) * T ^ (2 : ℕ) * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ (2 : ℕ) < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 ≤ ρ₃) (hρ₃ : ρ₃ < ρ₂) {ξ η : ℝ} (hξ : |ξ| < T) (hη : |η| < T)
    {z : Fin k → ℂ} (hz : z ∈ tube k ρ₃) :
    HasDerivAt (fun x : ℝ => deriv (fun y : ℝ => tubeSolution V y η z) x)
      (∫ t in (0 : ℝ)..η, clampedTubeStepFst V Vs T z ξ t) ξ := by
  have hV := hVC1.base
  have hzmem : z ∈ tube k ρ := tube_mono hρ₁.le (tube_mono hρ₂.le (tube_mono hρ₃.le hz))
  have hzρ : ∀ i, |(z i).im| ≤ ρ := fun i => (hzmem i).le
  have hcont := continuous_clampedTubeStep hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hzρ
  have hcont' := continuous_clampedTubeStepFst hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall hρ₁0.le hρ₁
    hρ₂0.le hρ₂ hρ₃0 hρ₃ hz
  have hpar := hasDerivAt_parametric_intervalIntegral_on
    (f := fun (x : ℝ) (t : ℝ) => clampedTubeStep V T z x t)
    (f' := fun (x : ℝ) (t : ℝ) => clampedTubeStepFst V Vs T z x t)
    (isOpen_absLt T) hξ hcont hcont' 0 η
    (fun x hx t htmem => hasDerivAt_clampedTubeStep_fst hρ₀ hVC1 hMv0 hMv hρ0 hρ hT hsmall
      hρ₁0 hρ₁ hρ₂0 hρ₂ hρ₃0 hρ₃ hx
      (lt_of_le_of_lt (abs_le_abs_of_mem_uIoc_zero htmem) hη) hz)
  refine hpar.congr_of_eventuallyEq ?_
  refine Filter.eventuallyEq_of_mem ((isOpen_absLt T).mem_nhds hξ) fun x hx => ?_
  exact deriv_tubeSolution_fst hρ₀ hV hMv0 hMv hρ0 hρ hT hsmall hx (le_of_lt hη) hzρ

end GaloisForLFunctions.HTGeometry
