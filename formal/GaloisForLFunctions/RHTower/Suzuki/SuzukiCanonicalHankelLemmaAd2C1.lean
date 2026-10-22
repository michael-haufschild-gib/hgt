import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemmaAd2Pointwise

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

def suzukiCompressedHankelL1ToContinuous
    (omega B : ℝ) (homega : 1 < omega) :
    IntervalL1 0 B →L[ℂ] C(ClosedInterval 0 B, ℂ) :=
  let L : IntervalL1 0 B →ₗ[ℂ] C(ClosedInterval 0 B, ℂ) :=
    { toFun := suzukiCompressedHankelL1ContinuousOutput omega B homega
      map_add' := by
        intro f g
        ext x
        exact map_add (suzukiHankelL1FunctionalContinuous omega B homega x) f g
      map_smul' := by
        intro c f
        ext x
        exact map_smul (suzukiHankelL1FunctionalContinuous omega B homega x) c f }
  L.mkContinuous
    ‖suzukiHankelL1FunctionalContinuous omega B homega‖
    (fun f => by
      change ‖suzukiCompressedHankelL1ContinuousOutput omega B homega f‖ ≤ _
      rw [ContinuousMap.norm_le
        (suzukiCompressedHankelL1ContinuousOutput omega B homega f)
        (mul_nonneg
          (norm_nonneg (suzukiHankelL1FunctionalContinuous omega B homega))
          (norm_nonneg f))]
      intro x
      exact (suzukiHankelL1FunctionalContinuous omega B homega x).le_opNorm f |>.trans
        (mul_le_mul_of_nonneg_right
          ((suzukiHankelL1FunctionalContinuous omega B homega).norm_coe_le_norm x)
          (norm_nonneg f)))

@[simp] theorem suzukiCompressedHankelL1ToContinuous_apply
    (omega B : ℝ) (homega : 1 < omega) (f : IntervalL1 0 B) :
    suzukiCompressedHankelL1ToContinuous omega B homega f =
      suzukiCompressedHankelL1ContinuousOutput omega B homega f := rfl

def suzukiFixedExtensionBoundarySourceL1
    (omega B R : ℝ) (homega : 1 < omega) (hB : 1 < B) (b : ℝ) : IntervalL1 0 B :=
  suzukiLogPullbackL1 B (by linarith)
    (realL1Translate (Real.log b)
      (integrableToL1 (suzukiSourceHLogSmoothExtension omega R)
        (integrable_suzukiSourceHLogSmoothExtension homega R)))

def suzukiFixedExtensionBoundarySourceDerivativeL1
    (omega B R : ℝ) (homega : 1 < omega) (hB : 1 < B) (b : ℝ) : IntervalL1 0 B :=
  b⁻¹ • suzukiLogPullbackL1 B (by linarith)
    (realL1Translate (Real.log b)
      (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
        (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)))

theorem hasDerivAt_suzukiFixedExtensionBoundarySourceL1
    {omega B R b : ℝ} (homega : 1 < omega) (hB : 1 < B) (hb : 0 < b) :
    HasDerivAt (suzukiFixedExtensionBoundarySourceL1 omega B R homega hB)
      (suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB b) b := by
  have hlog := hasDerivAt_suzukiLogPullbackL1_realL1Translate_of_integral_eq_sub
    B (by linarith) (suzukiSourceHLogSmoothExtension omega R)
      (suzukiSourceHLogSmoothExtensionDerivative omega R)
      (integrable_suzukiSourceHLogSmoothExtension homega R)
      (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)
      (integral_suzukiSourceHLogSmoothExtensionDerivative_eq_sub homega R)
      (Real.log b)
  have hcomp := hlog.hasFDerivAt.comp_hasDerivAt_of_eq b
    (Real.hasDerivAt_log hb.ne') rfl
  change HasDerivAt (fun c : ℝ =>
    suzukiLogPullbackL1 B (by linarith)
      (realL1Translate (Real.log c)
        (integrableToL1 (suzukiSourceHLogSmoothExtension omega R)
          (integrable_suzukiSourceHLogSmoothExtension homega R))))
    (b⁻¹ • suzukiLogPullbackL1 B (by linarith)
      (realL1Translate (Real.log b)
        (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
          (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)))) b
  change HasDerivAt (fun c : ℝ =>
    suzukiLogPullbackL1 B (by linarith)
      (realL1Translate (Real.log c)
        (integrableToL1 (suzukiSourceHLogSmoothExtension omega R)
          (integrable_suzukiSourceHLogSmoothExtension homega R)))) _ b at hcomp
  simpa only [ContinuousLinearMap.toSpanSingleton_apply] using hcomp

theorem continuousOn_suzukiFixedExtensionBoundarySourceDerivativeL1
    (omega B R : ℝ) (homega : 1 < omega) (hB : 1 < B) :
    ContinuousOn
      (suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB) (Ioi 0) := by
  have htrans : Continuous fun t : ℝ =>
      realL1Translate t
        (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
          (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)) :=
    continuous_realL1Translate _
  have hinner : ContinuousOn (fun b : ℝ =>
      suzukiLogPullbackL1 B (by linarith)
        (realL1Translate (Real.log b)
          (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
            (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)))) (Ioi 0) :=
    (suzukiLogPullbackL1 B (by linarith)).continuous.comp_continuousOn
      (htrans.comp_continuousOn
        (Real.continuousOn_log.mono fun b hb => ne_of_gt hb))
  exact (continuousOn_inv₀.mono fun b hb => ne_of_gt hb).smul hinner

theorem contDiffAt_one_suzukiFixedExtensionBoundarySourceL1
    {omega B R b : ℝ} (homega : 1 < omega) (hB : 1 < B) (hb : 0 < b) :
    ContDiffAt ℝ 1 (suzukiFixedExtensionBoundarySourceL1 omega B R homega hB) b := by
  rw [contDiffAt_one_iff]
  let d := suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB
  let d' := fun c : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (d c)
  refine ⟨d', Ioi 0, Ioi_mem_nhds hb, ?_, ?_⟩
  · exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := IntervalL1 0 B)).continuous.comp_continuousOn
        (continuousOn_suzukiFixedExtensionBoundarySourceDerivativeL1
          omega B R homega hB)
  · intro c hc
    exact (hasDerivAt_suzukiFixedExtensionBoundarySourceL1 homega hB hc).hasFDerivAt

theorem contDiffAt_one_suzukiFixedWindowBoundarySourceL1
    {omega B a : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (ha0 : 0 < a) (haB : a < B) :
    ContDiffAt ℝ 1 (suzukiFixedWindowBoundarySourceL1 omega B homega hB) a := by
  let R := suzukiSourceLogExtensionHorizon B (Real.log a)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B (Real.log a)
  have haR : Real.log a + Real.log B < R :=
    lt_suzukiSourceLogExtensionHorizon B (Real.log a)
  have hlocal := contDiffAt_one_suzukiFixedExtensionBoundarySourceL1
    (R := R) homega hB ha0
  have hev : suzukiFixedWindowBoundarySourceL1 omega B homega hB =ᶠ[𝓝 a]
      suzukiFixedExtensionBoundarySourceL1 omega B R homega hB := by
    have hpos : ∀ᶠ b : ℝ in 𝓝 a, 0 < b := Ioi_mem_nhds ha0
    have hbelow : ∀ᶠ b : ℝ in 𝓝 a, b < B := Iio_mem_nhds haB
    have hhor : ∀ᶠ b : ℝ in 𝓝 a, Real.log b + Real.log B < R :=
      (Real.continuousAt_log ha0.ne').add continuousAt_const |>.eventually
        (Iio_mem_nhds haR)
    filter_upwards [hpos, hbelow, hhor] with b hb0 hbB hbR
    rw [suzukiFixedExtensionBoundarySourceL1]
    have heq := suzukiFixedWindowBoundarySourceL1_eq_logPullback_smoothExtension
      (omega := omega) (B := B) (R := R) (t := Real.log b)
      homega hB hR (by rw [Real.exp_log hb0]; exact hbB.le) hbR.le
    rw [Real.exp_log hb0] at heq
    exact heq
  exact hlocal.congr_of_eventuallyEq hev

def suzukiFixedWindowPhiContinuousCurve
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b : ℝ) :
    C(ClosedInterval 0 B, ℂ) :=
  suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) b -
    epsilon.coeff • suzukiCompressedHankelL1ToContinuous omega B homega
      (suzukiApertureCutoffL1 b B
        (suzukiFixedWindowPhiL1 epsilon omega B homega hB b))

theorem suzukiFixedWindowPhiContinuousCurve_eq
    (epsilon : SuzukiHankelSign) {omega B b : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hb0 : 0 < b) (hbB : b ≤ B) :
    suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b =
      suzukiFixedWindowPhiContinuous epsilon omega B homega hB b hb0 hbB := by
  ext x
  rw [suzukiFixedWindowPhiContinuousCurve, suzukiFixedWindowPhiContinuous,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, suzukiHankelKernelContinuousRowOnReal,
    Set.projIcc_of_mem (by linarith) ⟨hb0.le, hbB⟩,
    suzukiHankelKernelContinuousRow_apply]
  simp only [smul_eq_mul, suzukiCompressedHankelL1ToContinuous_apply]
  rw [suzukiFixedWindowPhiL1, suzukiApertureCutoffL1_asL1,
    ← suzukiCompressedHankelContinuousOutput_eq_L1ContinuousOutput]

theorem continuousAt_suzukiFixedWindowPhiContinuousCurve
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContinuousAt
      (suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB) a := by
  have hu : ContinuousAt
      (suzukiFixedWindowPhiL1 epsilon omega B homega hB) a :=
    (hasDerivAt_suzukiFixedWindowPhiL1 epsilon homega hB ha0 haB).continuousAt
  have hcut := continuousAt_suzukiApertureCutoffL1_apply₂ B a hu
  have hout : ContinuousAt (fun b : ℝ =>
      suzukiCompressedHankelL1ToContinuous omega B homega
        (suzukiApertureCutoffL1 b B
          (suzukiFixedWindowPhiL1 epsilon omega B homega hB b))) a :=
    (suzukiCompressedHankelL1ToContinuous omega B homega).continuous.continuousAt.comp hcut
  exact (continuous_suzukiHankelKernelContinuousRowOnReal
    omega B homega (by linarith)).continuousAt.sub
      (hout.const_smul epsilon.coeff)

def suzukiFixedWindowSignedSectionDerivativeCurveL1
    (epsilon : SuzukiHankelSign) (omega B : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b : ℝ) : IntervalL1 0 B :=
  suzukiFixedWindowL1Lift epsilon B
    (ContinuousMap.toLp 2 volume ℂ
      ((suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b)
        (Set.projIcc 0 B (by linarith) b) •
          suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) b))

theorem continuousAt_suzukiFixedWindowSignedSectionDerivativeCurveL1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContinuousAt
      (suzukiFixedWindowSignedSectionDerivativeCurveL1 epsilon omega B homega hB) a := by
  have hcurve := continuousAt_suzukiFixedWindowPhiContinuousCurve
    epsilon homega hB ha0 haB
  let hB0 : 0 ≤ B := by linarith
  have hproj : ContinuousAt (fun b : ℝ => Set.projIcc 0 B hB0 b) a :=
    continuous_projIcc.continuousAt
  have heval : ContinuousAt (fun b : ℝ =>
      suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
        (Set.projIcc 0 B hB0 b)) a := by
    exact continuous_eval.continuousAt.comp
      (hcurve.prodMk hproj)
  have hrow : ContinuousAt
      (suzukiHankelKernelContinuousRowOnReal omega B homega hB0) a :=
    (continuous_suzukiHankelKernelContinuousRowOnReal
      omega B homega hB0).continuousAt
  change ContinuousAt (fun b : ℝ =>
    suzukiFixedWindowL1Lift epsilon B
      (ContinuousMap.toLp 2 volume ℂ
        (suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
          (Set.projIcc 0 B hB0 b) •
            suzukiHankelKernelContinuousRowOnReal omega B homega hB0 b))) a
  have h := (suzukiFixedWindowL1Lift epsilon B).continuous.continuousAt.comp
    ((ContinuousMap.toLp 2 volume ℂ).continuous.continuousAt.comp (heval.smul hrow))
  change ContinuousAt (fun b : ℝ =>
    suzukiFixedWindowL1Lift epsilon B
      (ContinuousMap.toLp 2 volume ℂ
        (suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
          (Set.projIcc 0 B hB0 b) •
            suzukiHankelKernelContinuousRowOnReal omega B homega hB0 b))) a at h
  exact h

theorem suzukiFixedWindowSignedSectionDerivativeCurveL1_eq
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    suzukiFixedWindowSignedSectionDerivativeCurveL1 epsilon omega B homega hB a =
      suzukiFixedWindowSignedSectionDerivativeAtPhiL1
        epsilon omega B homega hB a ha0 haB := by
  rw [suzukiFixedWindowSignedSectionDerivativeCurveL1,
    suzukiFixedWindowSignedSectionDerivativeAtPhiL1,
    suzukiSmoothedApertureProfileIntegrand,
    suzukiFixedWindowPhiContinuousCurve_eq epsilon homega hB ha0 haB.le,
    Set.projIcc_of_mem (by linarith) ⟨ha0.le, haB.le⟩,
    suzukiHankelKernelContinuousRowOnReal,
    Set.projIcc_of_mem (by linarith) ⟨ha0.le, haB.le⟩]

theorem suzukiFixedWindowBoundarySourceDerivativeL1_eq_fixedExtension
    {omega B R b : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (hR : 0 ≤ R) (hb0 : 0 < b) (hbB : b < B)
    (hbR : Real.log b + Real.log B < R) :
    suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB b =
      suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB b := by
  have hlit := hasDerivAt_suzukiFixedWindowBoundarySourceL1 homega hB hb0 hbB
  have hfix := hasDerivAt_suzukiFixedExtensionBoundarySourceL1
    (R := R) homega hB hb0
  have hev : suzukiFixedWindowBoundarySourceL1 omega B homega hB =ᶠ[𝓝 b]
      suzukiFixedExtensionBoundarySourceL1 omega B R homega hB := by
    have hpos : ∀ᶠ c : ℝ in 𝓝 b, 0 < c := Ioi_mem_nhds hb0
    have hbelow : ∀ᶠ c : ℝ in 𝓝 b, c < B := Iio_mem_nhds hbB
    have hhor : ∀ᶠ c : ℝ in 𝓝 b, Real.log c + Real.log B < R :=
      (Real.continuousAt_log hb0.ne').add continuousAt_const |>.eventually
        (Iio_mem_nhds hbR)
    filter_upwards [hpos, hbelow, hhor] with c hc0 hcB hcR
    rw [suzukiFixedExtensionBoundarySourceL1]
    have heq := suzukiFixedWindowBoundarySourceL1_eq_logPullback_smoothExtension
      (omega := omega) (B := B) (R := R) (t := Real.log c)
      homega hB hR (by rw [Real.exp_log hc0]; exact hcB.le) hcR.le
    rw [Real.exp_log hc0] at heq
    exact heq
  exact hlit.unique (hfix.congr_of_eventuallyEq hev)

def suzukiFixedWindowPhiDerivativeCurveL1
    (epsilon : SuzukiHankelSign) (omega B R : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b : ℝ) : IntervalL1 0 B :=
  suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB b
    (suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB b -
      suzukiFixedWindowSignedSectionDerivativeCurveL1 epsilon omega B homega hB b)

theorem continuousAt_suzukiFixedWindowPhiDerivativeCurveL1
    (epsilon : SuzukiHankelSign) {omega B R a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContinuousAt
      (suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB) a := by
  have hsource : ContinuousAt
      (suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB) a :=
    (continuousOn_suzukiFixedExtensionBoundarySourceDerivativeL1
      omega B R homega hB).continuousAt (isOpen_Ioi.mem_nhds ha0)
  have hendpoint := continuousAt_suzukiFixedWindowSignedSectionDerivativeCurveL1
    epsilon homega hB ha0 haB
  exact continuousAt_suzukiFixedWindowResolventOperatorL1Inverse_apply₂
    epsilon homega hB (hsource.sub hendpoint)

theorem contDiffAt_one_suzukiFixedWindowPhiL1
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContDiffAt ℝ 1 (suzukiFixedWindowPhiL1 epsilon omega B homega hB) a := by
  let R := suzukiSourceLogExtensionHorizon B (Real.log a)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B (Real.log a)
  have haR : Real.log a + Real.log B < R :=
    lt_suzukiSourceLogExtensionHorizon B (Real.log a)
  let d := suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB
  let d' := fun b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (d b)
  have hdcont : ContinuousAt d a :=
    continuousAt_suzukiFixedWindowPhiDerivativeCurveL1
      epsilon homega hB ha0 haB
  rw [contDiffAt_one_iff]
  let U := Ioo 0 B ∩ {b : ℝ | Real.log b + Real.log B < R}
  have hUa : U ∈ 𝓝 a := by
    apply Filter.inter_mem (Ioo_mem_nhds ha0 haB)
    exact ((Real.continuousAt_log ha0.ne').add continuousAt_const).eventually
      (Iio_mem_nhds haR)
  refine ⟨d', U, hUa, ?_, ?_⟩
  · have hdc : ContinuousOn d U := by
      intro b hb
      exact (continuousAt_suzukiFixedWindowPhiDerivativeCurveL1
        epsilon homega hB hb.1.1 hb.1.2).continuousWithinAt
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := IntervalL1 0 B)).continuous.comp_continuousOn hdc
  · intro b hb
    have hbase := hasDerivAt_suzukiFixedWindowPhiL1
      epsilon homega hB hb.1.1 hb.1.2
    have hsource := suzukiFixedWindowBoundarySourceDerivativeL1_eq_fixedExtension
      homega hB hR hb.1.1 hb.1.2 hb.2
    have hendpoint := suzukiFixedWindowSignedSectionDerivativeCurveL1_eq
      epsilon homega hB hb.1.1 hb.1.2
    change HasFDerivAt _ (ContinuousLinearMap.toSpanSingleton ℝ (d b)) b
    apply HasDerivAt.hasFDerivAt
    change HasDerivAt _
      (suzukiFixedWindowResolventOperatorL1Inverse epsilon omega B homega hB b
        (suzukiFixedExtensionBoundarySourceDerivativeL1 omega B R homega hB b -
          suzukiFixedWindowSignedSectionDerivativeCurveL1 epsilon omega B homega hB b)) b
    simpa [suzukiFixedWindowPhiDerivativeL1, hsource, hendpoint] using hbase

theorem suzukiFixedWindowPhiDerivativeL1_eq_curve
    (epsilon : SuzukiHankelSign) {omega B R b : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (hR : 0 ≤ R)
    (hb0 : 0 < b) (hbB : b < B) (hbR : Real.log b + Real.log B < R) :
    suzukiFixedWindowPhiDerivativeL1 epsilon omega B homega hB b hb0 hbB =
      suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB b := by
  rw [suzukiFixedWindowPhiDerivativeL1, suzukiFixedWindowPhiDerivativeCurveL1,
    suzukiFixedWindowBoundarySourceDerivativeL1_eq_fixedExtension
      homega hB hR hb0 hbB hbR,
    suzukiFixedWindowSignedSectionDerivativeCurveL1_eq
      epsilon homega hB hb0 hbB]

def suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
    (epsilon : SuzukiHankelSign) (omega B R : ℝ)
    (homega : 1 < omega) (hB : 1 < B) (b : ℝ)
    (x : ClosedInterval 0 B) : ℂ :=
  suzukiHankelL1FunctionalContinuous omega B homega x
      (suzukiApertureCutoffL1 b B
        (suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB b)) +
    (suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b)
        (Set.projIcc 0 B (by linarith) b) *
      suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) b x

theorem continuousAt_suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
    (epsilon : SuzukiHankelSign) {omega B R a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) :
    ContinuousAt (fun b : ℝ =>
      suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
        epsilon omega B R homega hB b x) a := by
  have hd := continuousAt_suzukiFixedWindowPhiDerivativeCurveL1
    (R := R) epsilon homega hB ha0 haB
  have hcut := continuousAt_suzukiApertureCutoffL1_apply₂ B a hd
  have hfirst := (suzukiHankelL1FunctionalContinuous omega B homega x).continuous
    |>.continuousAt.comp hcut
  let hB0 : 0 ≤ B := by linarith
  have hcurve := continuousAt_suzukiFixedWindowPhiContinuousCurve
    epsilon homega hB ha0 haB
  have hproj : ContinuousAt (fun b : ℝ => Set.projIcc 0 B hB0 b) a :=
    continuous_projIcc.continuousAt
  have heval : ContinuousAt (fun b : ℝ =>
      suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
        (Set.projIcc 0 B hB0 b)) a :=
    continuous_eval.continuousAt.comp (hcurve.prodMk hproj)
  have hrow : ContinuousAt (fun b : ℝ =>
      suzukiHankelKernelContinuousRowOnReal omega B homega hB0 b x) a :=
    (ContinuousMap.evalCLM ℂ x).continuous.comp
      (continuous_suzukiHankelKernelContinuousRowOnReal omega B homega hB0)
      |>.continuousAt
  exact hfirst.add (heval.mul hrow)

theorem contDiffAt_one_suzukiFixedWindowSmoothedPhiPoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) :
    ContDiffAt ℝ 1 (fun b : ℝ =>
      suzukiCompressedHankelL1ContinuousOutput omega B homega
        (suzukiApertureCutoffL1 b B
          (suzukiFixedWindowPhiL1 epsilon omega B homega hB b)) x) a := by
  let R := suzukiSourceLogExtensionHorizon B (Real.log a)
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B (Real.log a)
  have haR : Real.log a + Real.log B < R :=
    lt_suzukiSourceLogExtensionHorizon B (Real.log a)
  let d := fun b : ℝ =>
    suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
      epsilon omega B R homega hB b x
  let d' := fun b : ℝ => ContinuousLinearMap.toSpanSingleton ℝ (d b)
  rw [contDiffAt_one_iff]
  let U := Ioo 0 B ∩ {b : ℝ | Real.log b + Real.log B < R}
  have hUa : U ∈ 𝓝 a := by
    apply Filter.inter_mem (Ioo_mem_nhds ha0 haB)
    exact ((Real.continuousAt_log ha0.ne').add continuousAt_const).eventually
      (Iio_mem_nhds haR)
  refine ⟨d', U, hUa, ?_, ?_⟩
  · have hdc : ContinuousOn d U := by
      intro b hb
      exact (continuousAt_suzukiFixedWindowSmoothedPhiDerivativeCurvePoint
        (R := R) epsilon homega hB hb.1.1 hb.1.2 x).continuousWithinAt
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := ℂ)).continuous.comp_continuousOn hdc
  · intro b hb
    have hbase := hasDerivAt_suzukiFixedWindowSmoothedPhiPoint
      epsilon homega hB hb.1.1 hb.1.2 x
    have hdEq := suzukiFixedWindowPhiDerivativeL1_eq_curve
      epsilon homega hB hR hb.1.1 hb.1.2 hb.2
    have hfEq := suzukiFixedWindowPhiContinuousCurve_eq
      epsilon homega hB hb.1.1 hb.1.2.le
    change HasFDerivAt _ (ContinuousLinearMap.toSpanSingleton ℝ (d b)) b
    apply HasDerivAt.hasFDerivAt
    change HasDerivAt _
      (suzukiHankelL1FunctionalContinuous omega B homega x
          (suzukiApertureCutoffL1 b B
            (suzukiFixedWindowPhiDerivativeCurveL1 epsilon omega B R homega hB b)) +
        suzukiFixedWindowPhiContinuousCurve epsilon omega B homega hB b
            (Set.projIcc 0 B (by linarith) b) *
          suzukiHankelKernelContinuousRowOnReal omega B homega (by linarith) b x) b
    simpa [suzukiFixedWindowSmoothedPhiDerivativePoint, hdEq, ← hfEq,
      suzukiSmoothedApertureProfileIntegrand,
      suzukiHankelKernelContinuousRowOnReal] using hbase

theorem contDiffAt_one_suzukiFixedWindowPhiPoint
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B)
    (x : ClosedInterval 0 B) (hx : 0 < (x : ℝ))
    (hregular : ∀ n : ℕ, a * (x : ℝ) ≠ (n : ℝ)) :
    ContDiffAt ℝ 1 (fun b : ℝ =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b x) a := by
  have hsource : ContDiffAt ℝ 1
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ))) a :=
    (contDiffAt_one_suzukiSourceHFinite_of_not_nat homega
      (mul_pos ha0 hx) hregular).comp a (contDiffAt_id.mul contDiffAt_const)
  have hout := contDiffAt_one_suzukiFixedWindowSmoothedPhiPoint
    epsilon homega hB ha0 haB x
  have hformula : (fun b : ℝ =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b x) =
      fun b : ℝ => suzukiSourceHFinite omega (b * (x : ℝ)) - epsilon.coeff *
        suzukiCompressedHankelL1ContinuousOutput omega B homega
          (suzukiApertureCutoffL1 b B
            (suzukiFixedWindowPhiL1 epsilon omega B homega hB b)) x := by
    funext b
    exact suzukiFixedWindowPhiPoint_eq_L1_formula epsilon homega hB x
  rw [hformula]
  exact hsource.sub (contDiffAt_const.mul hout)

theorem contDiffAt_one_suzukiHankelPhiGlobalApertureReal
    (epsilon : SuzukiHankelSign) {omega x a : ℝ}
    (homega : 1 < omega) (hx : 0 < x)
    (ha : a ∈ SuzukiHankelRegularAperture x) :
    ContDiffAt ℝ 1
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
  have hlocal := contDiffAt_one_suzukiFixedWindowPhiPoint
    epsilon homega hB (lt_trans zero_lt_one ha.1) haB xB hx hregular
  have hev : suzukiHankelPhiGlobalApertureReal epsilon omega x homega =ᶠ[𝓝 a]
      fun b : ℝ => suzukiFixedWindowPhiPoint epsilon omega B homega hB b xB := by
    filter_upwards [Ioo_mem_nhds ha.1 haB] with b hb
    rw [suzukiHankelPhiGlobalApertureReal, dif_pos hb.1]
    exact (suzukiFixedWindowPhiPoint_eq_global
      epsilon homega hb.1 hB hb.2.le xB hx).symm
  exact hlocal.congr_of_eventuallyEq hev

theorem continuousAt_suzukiHankelPhiGlobalApertureReal
    (epsilon : SuzukiHankelSign) {omega x a : ℝ}
    (homega : 1 < omega) (hx : 0 < x) (ha : 1 < a) :
    ContinuousAt
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) a := by
  let B : ℝ := max a x + 1
  have haB : a < B := by dsimp only [B]; linarith [le_max_left a x]
  have hxB : x < B := by dsimp only [B]; linarith [le_max_right a x]
  have hB : 1 < B := ha.trans haB
  let xB : ClosedInterval 0 B := ⟨x, ⟨hx.le, hxB.le⟩⟩
  have hlocal := continuousAt_suzukiFixedWindowPhiPoint epsilon homega hB
    (lt_trans zero_lt_one ha) haB xB hx
  have hev : suzukiHankelPhiGlobalApertureReal epsilon omega x homega =ᶠ[𝓝 a]
      fun b : ℝ => suzukiFixedWindowPhiPoint epsilon omega B homega hB b xB := by
    filter_upwards [Ioo_mem_nhds ha haB] with b hb
    rw [suzukiHankelPhiGlobalApertureReal, dif_pos hb.1]
    exact (suzukiFixedWindowPhiPoint_eq_global
      epsilon homega hb.1 hB hb.2.le xB hx).symm
  exact hlocal.congr_of_eventuallyEq hev

theorem continuousOn_suzukiHankelPhiGlobalApertureReal
    (epsilon : SuzukiHankelSign) {omega x : ℝ}
    (homega : 1 < omega) (hx : 0 < x) :
    ContinuousOn
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) (Ioi 1) := by
  intro a ha
  exact (continuousAt_suzukiHankelPhiGlobalApertureReal
    epsilon homega hx ha).continuousWithinAt

theorem contDiffOn_one_suzukiHankelPhiGlobalApertureReal_regular
    (epsilon : SuzukiHankelSign) {omega x : ℝ}
    (homega : 1 < omega) (hx : 0 < x) :
    ContDiffOn ℝ 1
      (suzukiHankelPhiGlobalApertureReal epsilon omega x homega)
      (SuzukiHankelRegularAperture x) := by
  intro a ha
  exact (contDiffAt_one_suzukiHankelPhiGlobalApertureReal
    epsilon homega hx ha).contDiffWithinAt

/-- Closed universal formulation of Suzuki (2012), Lemma `lem_ad2`.  Continuity holds for every
`a>1`; continuous differentiability holds off exactly the printed loci `a=n/x` and `a=√n`. -/
theorem suzuki_lemma_ad2 :
    ∀ (epsilon : SuzukiHankelSign) (omega x : ℝ)
      (homega : 1 < omega) (hx : 0 < x),
      ContinuousOn
          (suzukiHankelPhiGlobalApertureReal epsilon omega x homega) (Ioi 1) ∧
        ContDiffOn ℝ 1
          (suzukiHankelPhiGlobalApertureReal epsilon omega x homega)
          (SuzukiHankelRegularAperture x) := by
  intro epsilon omega x homega hx
  exact ⟨continuousOn_suzukiHankelPhiGlobalApertureReal epsilon homega hx,
    contDiffOn_one_suzukiHankelPhiGlobalApertureReal_regular epsilon homega hx⟩

end RHTower
