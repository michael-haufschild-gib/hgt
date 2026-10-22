import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemmaAd2Derivative

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- Continuous representative of literal Suzuki smoothing on an `L¹` input. -/
def suzukiCompressedHankelL1ContinuousOutput
    (omega B : ℝ) (homega : 1 < omega) (f : IntervalL1 0 B) :
    C(ClosedInterval 0 B, ℂ) where
  toFun x := suzukiHankelL1FunctionalContinuous omega B homega x f
  continuous_toFun :=
    ((ContinuousLinearMap.apply ℂ ℂ) f).continuous.comp
      (suzukiHankelL1FunctionalContinuous omega B homega).continuous

theorem suzukiCompressedHankelL1ContinuousOutput_eq_integral
    (omega B : ℝ) (homega : 1 < omega) (f : IntervalL1 0 B)
    (x : ClosedInterval 0 B) :
    suzukiCompressedHankelL1ContinuousOutput omega B homega f x =
      ∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  change (complexMulBilinear.lpPairing volume ∞ 1
    (suzukiHankelKernelRowsLInf omega B homega x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiHankelKernelRowsLInf_ae omega B homega x] with y hy
  rw [hy]
  simp [complexMulBilinear]

theorem suzukiCompressedHankelContinuousOutput_eq_L1ContinuousOutput
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B)
    (f : IntervalL2 0 B) :
    suzukiCompressedHankelContinuousOutput omega B (by linarith) hB f =
      suzukiCompressedHankelL1ContinuousOutput omega B homega
        (suzukiIntervalL2AsL1 B f) := by
  ext x
  rw [suzukiCompressedHankelContinuousOutput_eq_integral,
    suzukiCompressedHankelL1ContinuousOutput_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiIntervalL2AsL1_ae B f] with y hy
  rw [hy]

theorem suzukiCompressedHankelL1ContinuousOutput_cutoff_continuousMap
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (a : ℝ) (ha0 : 0 ≤ a) (haB : a ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) :
    suzukiCompressedHankelL1ContinuousOutput omega B homega
        (suzukiApertureCutoffL1 a B (ContinuousMap.toLp 1 volume ℂ f)) =
      suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a := by
  ext x
  rw [suzukiCompressedHankelL1ContinuousOutput_eq_integral]
  have hcut := suzukiApertureCutoffL1_ae a B
    (ContinuousMap.toLp 1 volume ℂ f)
  have hf := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B))) f
  let F : ℝ → ℂ := fun y =>
    suzukiSourceHFinite omega ((x : ℝ) * y) *
      f (Set.projIcc 0 B hB0 y)
  calc
    (∫ y : ClosedInterval 0 B,
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
        suzukiApertureCutoffL1 a B (ContinuousMap.toLp 1 volume ℂ f) y ∂volume) =
      ∫ y : ClosedInterval 0 B,
        (suzukiApertureSet a B).indicator (fun y => F (y : ℝ)) y ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcut, hf] with y hcuty hfy
      rw [hcuty]
      by_cases hy : y ∈ suzukiApertureSet a B
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hfy]
        dsimp only [F]
        rw [Set.projIcc_of_mem hB0 y.property]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    _ = ∫ y in (0 : ℝ)..a, F y :=
      integral_subtype_apertureSet_eq_intervalIntegral B a ha0 haB F
    _ = suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a x := by
      have hint : IntervalIntegrable
          (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f)
          volume 0 a :=
        (continuous_suzukiSmoothedApertureProfileIntegrand
          omega B homega hB0 f).intervalIntegrable 0 a
      rw [suzukiSmoothedApertureProfilePrimitive]
      calc
        (∫ y in (0 : ℝ)..a, F y) =
            ∫ y in (0 : ℝ)..a, (ContinuousMap.evalCLM ℂ x)
              (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y) := by
          apply intervalIntegral.integral_congr
          intro y hy
          have hyB : y ∈ Icc 0 B := by
            rw [uIcc_of_le ha0] at hy
            exact ⟨hy.1, hy.2.trans haB⟩
          dsimp only [F]
          rw [ContinuousMap.evalCLM_apply, suzukiSmoothedApertureProfileIntegrand,
            ContinuousMap.smul_apply, suzukiHankelKernelContinuousRowOnReal,
            suzukiHankelKernelContinuousRow_apply]
          simp only [smul_eq_mul]
          rw [Set.projIcc_of_mem hB0 hyB]
          exact mul_comm _ _
        _ = (ContinuousMap.evalCLM ℂ x)
            (∫ y in (0 : ℝ)..a,
              suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y) :=
          (ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm hint
        _ = _ := by rw [ContinuousMap.evalCLM_apply]

theorem continuousAt_suzukiApertureCutoffL1_apply₂
    (B a : ℝ) {u : ℝ → IntervalL1 0 B} (hu : ContinuousAt u a) :
    ContinuousAt (fun b : ℝ => suzukiApertureCutoffL1 b B (u b)) a := by
  have hdiff : Tendsto (fun b => u b - u a) (𝓝 a) (𝓝 0) := by
    have h : ContinuousAt (fun b : ℝ => u b - u a) a :=
      hu.sub continuousAt_const
    change Tendsto (fun b => u b - u a) (𝓝 a) (𝓝 (u a - u a)) at h
    simpa using h
  have hfirstNorm : Tendsto (fun b =>
      ‖suzukiApertureCutoffL1 b B (u b - u a)‖) (𝓝 a) (𝓝 0) := by
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · exact fun b => norm_suzukiApertureCutoffL1_apply_le b B (u b - u a)
    · simpa using hdiff.norm
  have hfirst : Tendsto (fun b =>
      suzukiApertureCutoffL1 b B (u b - u a)) (𝓝 a) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hfirstNorm
  have hsecond : Tendsto (fun b => suzukiApertureCutoffL1 b B (u a))
      (𝓝 a) (𝓝 (suzukiApertureCutoffL1 a B (u a))) :=
    (continuous_suzukiApertureCutoffL1_apply B (u a)).continuousAt
  have hsum := hfirst.add hsecond
  change Tendsto (fun b => suzukiApertureCutoffL1 b B (u b))
    (𝓝 a) (𝓝 (suzukiApertureCutoffL1 a B (u a)))
  convert hsum using 1
  · ext b
    rw [← map_add]
    simp
  · simp

theorem hasDerivAt_suzukiApertureCutoffL1_centered
    (B a : ℝ) {u : ℝ → IntervalL1 0 B} {du : IntervalL1 0 B}
    (hu : HasDerivAt u du a) :
    HasDerivAt (fun b : ℝ => suzukiApertureCutoffL1 b B (u b - u a))
      (suzukiApertureCutoffL1 a B du) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  let g := Function.update (slope u a) a du
  have hg : ContinuousAt g a :=
    continuousAt_update_same.mpr hu.tendsto_slope
  have hcut : Tendsto (fun b => suzukiApertureCutoffL1 b B (g b))
      (𝓝[≠] a) (𝓝 (suzukiApertureCutoffL1 a B du)) := by
    have h : Tendsto (fun b => suzukiApertureCutoffL1 b B (g b))
        (𝓝[≠] a) (𝓝 (suzukiApertureCutoffL1 a B (g a))) :=
      (continuousAt_suzukiApertureCutoffL1_apply₂ B a hg).tendsto.mono_left
        nhdsWithin_le_nhds
    simpa [g] using h
  refine hcut.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with b hba
  change suzukiApertureCutoffL1 b B
    (Function.update (slope u a) a du b) = _
  rw [Function.update_of_ne hba]
  change suzukiApertureCutoffL1 b B (slope u a b) =
    slope (fun c : ℝ => suzukiApertureCutoffL1 c B (u c - u a)) a b
  rw [slope_def_module]
  change suzukiApertureCutoffL1 b B ((b - a)⁻¹ • (u b - u a)) =
    (b - a)⁻¹ •
      (suzukiApertureCutoffL1 b B (u b - u a) -
        suzukiApertureCutoffL1 a B (u a - u a))
  rw [sub_self, map_zero, sub_zero]
  exact map_smul ((suzukiApertureCutoffL1 b B).restrictScalars ℝ)
    (b - a)⁻¹ (u b - u a)

def suzukiFixedWindowSmoothedPhiDerivativePoint
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ)
    (ha0 : 0 < a) (haB : a < B) (x : ClosedInterval 0 B) : ℂ :=
  suzukiHankelL1FunctionalContinuous omega B homega x
      (suzukiApertureCutoffL1 a B
        (suzukiFixedWindowPhiDerivativeL1
          epsilon omega B homega hB a ha0 haB)) +
    suzukiSmoothedApertureProfileIntegrand omega B homega (by linarith)
      (suzukiFixedWindowPhiContinuous
        epsilon omega B homega hB a ha0 haB.le) a x

theorem hasDerivAt_suzukiFixedWindowSmoothedPhiPoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) :
    HasDerivAt (fun b : ℝ =>
      suzukiCompressedHankelL1ContinuousOutput omega B homega
        (suzukiApertureCutoffL1 b B
          (suzukiFixedWindowPhiL1 epsilon omega B homega hB b)) x)
      (suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a ha0 haB x) a := by
  let u := suzukiFixedWindowPhiL1 epsilon omega B homega hB
  let du := suzukiFixedWindowPhiDerivativeL1
    epsilon omega B homega hB a ha0 haB
  let f := suzukiFixedWindowPhiContinuous
    epsilon omega B homega hB a ha0 haB.le
  let L := suzukiHankelL1FunctionalContinuous omega B homega x
  have hu : HasDerivAt u du a :=
    hasDerivAt_suzukiFixedWindowPhiL1 epsilon homega hB ha0 haB
  have hcenter := hasDerivAt_suzukiApertureCutoffL1_centered B a hu
  have hfirst := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt a hcenter
  have hprim := hasDerivAt_suzukiSmoothedApertureProfilePrimitive
    omega B homega (by linarith) f a
  have hsecond := ((ContinuousMap.evalCLM ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    a hprim
  have hsum := hfirst.add hsecond
  have huaf : u a = ContinuousMap.toLp 1 volume ℂ f := by
    exact (suzukiFixedWindowPhiContinuous_toLp_one_eq
      epsilon omega B homega hB a ha0 haB.le).symm
  have hev : (fun b : ℝ =>
      suzukiCompressedHankelL1ContinuousOutput omega B homega
        (suzukiApertureCutoffL1 b B (u b)) x) =ᶠ[𝓝 a]
      fun b : ℝ =>
        L (suzukiApertureCutoffL1 b B (u b - u a)) +
          suzukiSmoothedApertureProfilePrimitive
            omega B homega (by linarith) f b x := by
    filter_upwards [Icc_mem_nhds ha0 haB] with b hb
    rw [← suzukiCompressedHankelL1ContinuousOutput_cutoff_continuousMap
      omega B homega (by linarith) b hb.1 hb.2 f]
    change L (suzukiApertureCutoffL1 b B (u b)) =
      L (suzukiApertureCutoffL1 b B (u b - u a)) +
        L (suzukiApertureCutoffL1 b B (ContinuousMap.toLp 1 volume ℂ f))
    rw [← huaf, ← map_add, ← map_add]
    simp
  change HasDerivAt _ (L (suzukiApertureCutoffL1 a B du) +
    suzukiSmoothedApertureProfileIntegrand omega B homega (by linarith) f a x) a
  exact hsum.congr_of_eventuallyEq hev

theorem suzukiFixedWindowPhiPoint_eq_L1_formula
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B)
    (x : ClosedInterval 0 B) :
    suzukiFixedWindowPhiPoint epsilon omega B homega hB a x =
      suzukiSourceHFinite omega (a * (x : ℝ)) - epsilon.coeff *
        suzukiCompressedHankelL1ContinuousOutput omega B homega
          (suzukiApertureCutoffL1 a B
            (suzukiFixedWindowPhiL1 epsilon omega B homega hB a)) x := by
  rw [suzukiFixedWindowPhiPoint, suzukiFixedWindowPhiL1,
    suzukiApertureCutoffL1_asL1,
    ← suzukiCompressedHankelContinuousOutput_eq_L1ContinuousOutput]

def suzukiFixedWindowPhiPointApertureDerivative
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (a : ℝ)
    (ha0 : 0 < a) (haB : a < B) (x : ClosedInterval 0 B) : ℂ :=
  deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a -
    epsilon.coeff *
      suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a ha0 haB x

theorem hasDerivAt_suzukiFixedWindowPhiPoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ))
    (hregular : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ)) :
    HasDerivAt (fun b : ℝ =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b x)
      (suzukiFixedWindowPhiPointApertureDerivative
        epsilon omega B homega hB a ha0 haB x) a := by
  have hsourceCD : ContDiffAt ℝ 1
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a := by
    exact (contDiffAt_one_suzukiSourceHFinite_of_not_nat homega
      (mul_pos ha0 hx) hregular).comp a (contDiffAt_id.mul contDiffAt_const)
  have hsource : HasDerivAt
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ)))
      (deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a) a :=
    (hsourceCD.differentiableAt (by norm_num)).hasDerivAt
  have hout := hasDerivAt_suzukiFixedWindowSmoothedPhiPoint
    epsilon homega hB ha0 haB x
  have hformula : (fun b : ℝ =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b x) =ᶠ[𝓝 a]
      fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ)) - epsilon.coeff *
        suzukiCompressedHankelL1ContinuousOutput omega B homega
          (suzukiApertureCutoffL1 b B
            (suzukiFixedWindowPhiL1 epsilon omega B homega hB b)) x := by
    filter_upwards [Ioo_mem_nhds ha0 haB] with b hb
    exact suzukiFixedWindowPhiPoint_eq_L1_formula
      epsilon homega hB x
  change HasDerivAt _
    (deriv (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a -
      epsilon.coeff * suzukiFixedWindowSmoothedPhiDerivativePoint
        epsilon omega B homega hB a ha0 haB x) a
  exact (hsource.sub (hout.const_mul epsilon.coeff)).congr_of_eventuallyEq hformula

def SuzukiHankelRegularAperture (x : ℝ) : Set ℝ :=
  {a | 1 < a ∧ ∀ n : ℕ, a ≠ (n : ℝ) / x ∧ a ≠ Real.sqrt n}

def suzukiHankelPhiGlobalApertureReal
    (epsilon : SuzukiHankelSign) (omega x : ℝ) (homega : 1 < omega) : ℝ → ℂ :=
  fun a => if ha : 1 < a then
    suzukiHankelPhiGlobal epsilon omega a homega ha x
  else 0

theorem differentiableAt_suzukiHankelPhiGlobalApertureReal
    (epsilon : SuzukiHankelSign) {omega x a : ℝ}
    (homega : 1 < omega) (hx : 0 < x)
    (ha : a ∈ SuzukiHankelRegularAperture x) :
    DifferentiableAt ℝ
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) a := by
  let B : ℝ := max a x + 1
  have haB : a < B := by dsimp only [B]; linarith [le_max_left a x]
  have hxB : x < B := by dsimp only [B]; linarith [le_max_right a x]
  have hB : 1 < B := ha.1.trans haB
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx.le, hxB.le⟩⟩
  have hregular : ∀ n : ℕ, a * (xB : ℝ) ≠ (n : ℝ) := by
    intro n han
    apply (ha.2 n).1
    apply (eq_div_iff hx.ne').2
    simpa only [xB] using han
  have hlocal := hasDerivAt_suzukiFixedWindowPhiPoint
    epsilon homega hB (lt_trans zero_lt_one ha.1) haB xB hx hregular
  have hev : suzukiHankelPhiGlobalApertureReal epsilon omega x homega =ᶠ[𝓝 a]
      fun b : ℝ => suzukiFixedWindowPhiPoint epsilon omega B homega hB b xB := by
    filter_upwards [Ioo_mem_nhds ha.1 haB] with b hb
    rw [suzukiHankelPhiGlobalApertureReal, dif_pos hb.1]
    exact (suzukiFixedWindowPhiPoint_eq_global
      epsilon homega hb.1 hB hb.2.le xB hx).symm
  exact (hlocal.congr_of_eventuallyEq hev).differentiableAt

theorem differentiableOn_suzukiHankelPhiGlobalApertureReal_regular
    (epsilon : SuzukiHankelSign) {omega x : ℝ}
    (homega : 1 < omega) (hx : 0 < x) :
    DifferentiableOn ℝ
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega)
      (SuzukiHankelRegularAperture x) := by
  intro a ha
  exact (differentiableAt_suzukiHankelPhiGlobalApertureReal
    epsilon homega hx ha).differentiableWithinAt

end RHTower
