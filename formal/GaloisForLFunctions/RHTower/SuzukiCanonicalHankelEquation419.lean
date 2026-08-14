import GaloisForLFunctions.HTGeometry.ContinuousKernelFredholmChamber
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelLemmaAd2Continuity

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace RHTower

open ContinuousKernelFredholm

attribute [local instance] Measure.Subtype.measureSpace

private theorem suzukiFredholm_closedInterval_volume_isOpenPosMeasure
    {B : ℝ} (hB : 0 < B) :
    (volume : Measure (ClosedInterval 0 B)).IsOpenPosMeasure := by
  constructor
  intro U hU hUne hzero
  rcases hUne with ⟨x, hxU⟩
  rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVU⟩
  have hxV : (x : ℝ) ∈ V := by
    rw [← Set.mem_preimage, hVU]
    exact hxU
  have hxClosure : (x : ℝ) ∈ closure (Ioo (0 : ℝ) B) := by
    rw [closure_Ioo (by linarith : (0 : ℝ) ≠ B)]
    exact x.property
  have hnonempty : (V ∩ Ioo (0 : ℝ) B).Nonempty :=
    mem_closure_iff.mp hxClosure V hVopen hxV
  have hopen : IsOpen (V ∩ Ioo (0 : ℝ) B) := hVopen.inter isOpen_Ioo
  have himageZero : volume (((↑) : ClosedInterval 0 B → ℝ) '' U) = 0 :=
    Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero
      (u := Icc (0 : ℝ) B) (t := U) measurableSet_Icc.nullMeasurableSet hzero
  have hsub : V ∩ Ioo (0 : ℝ) B ⊆
      ((↑) : ClosedInterval 0 B → ℝ) '' U := by
    intro y hy
    let ys : ClosedInterval 0 B := ⟨y, ⟨hy.2.1.le, hy.2.2.le⟩⟩
    refine ⟨ys, ?_, rfl⟩
    rw [← hVU]
    exact hy.1
  exact (hopen.measure_ne_zero volume hnonempty)
    (measure_mono_null hsub himageZero)

/-- Literal continuous kernel whose Fredholm series is Suzuki's compressed Hankel determinant. -/
def suzukiFredholmKernel (omega : ℝ) (x y : ℝ) : ℂ :=
  suzukiSourceHFinite omega (x * y)

/-- For `omega > 1`, Suzuki's literal product kernel is continuous on the whole plane, including
both zero-product axes. -/
theorem continuous_suzukiFredholmKernel
    {omega : ℝ} (homega : 1 < omega) :
    Continuous (suzukiFredholmKernel omega).uncurry := by
  rw [continuous_iff_continuousAt]
  intro p
  change ContinuousAt (fun q : ℝ × ℝ ↦
    suzukiSourceHFinite omega (q.1 * q.2)) p
  let m : ℝ × ℝ → ℝ := fun q ↦ q.1 * q.2
  have hm : Continuous m := by
    dsimp only [m]
    fun_prop
  by_cases hp : 0 < m p
  · exact (continuousAt_suzukiSourceHFinite homega hp).comp hm.continuousAt
  · have hmp : m p < 1 := lt_of_le_of_lt (le_of_not_gt hp) zero_lt_one
    have hev : (fun q ↦ suzukiSourceHFinite omega (m q)) =ᶠ[nhds p] fun _ ↦ 0 := by
      filter_upwards [hm.continuousAt (Iio_mem_nhds hmp)] with q hq
      rw [suzukiSourceHFinite, if_neg (not_lt_of_ge hq.le)]
    exact continuousAt_const.congr_of_eventuallyEq (by simpa only [m] using hev)

/-- A nonnegative uniform norm bound for Suzuki's kernel on each compact aperture square. -/
theorem exists_suzukiFredholmKernel_bound
    {omega a : ℝ} (homega : 1 < omega) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a,
        ‖suzukiFredholmKernel omega x y‖ ≤ M := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) a ×ˢ Icc (0 : ℝ) a
  have hS : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hS.bddAbove_image
    (continuous_suzukiFredholmKernel homega).norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hp : (x, y) ∈ S := ⟨hx, hy⟩
  have himem : ‖(suzukiFredholmKernel omega).uncurry (x, y)‖ ∈
      (fun p : ℝ × ℝ ↦ ‖(suzukiFredholmKernel omega).uncurry p‖) '' S :=
    ⟨(x, y), hp, rfl⟩
  exact (hC himem).trans (le_max_left _ _)

/-- Classical Fredholm determinant attached to Suzuki's signed compressed Hankel kernel. -/
def suzukiFredholmDeterminant
    (epsilon : SuzukiHankelSign) (omega a : ℝ) : ℂ :=
  determinant (suzukiFredholmKernel omega) a epsilon.coeff

/-- Boundary first minor, with its column point fixed at the aperture. -/
def suzukiFredholmBoundaryMinor
    (epsilon : SuzukiHankelSign) (omega a x : ℝ) : ℂ :=
  fredholmMinor (suzukiFredholmKernel omega) a epsilon.coeff x a

theorem continuousOn_suzukiFredholmBoundaryMinor
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 0 ≤ a) :
    ContinuousOn (suzukiFredholmBoundaryMinor epsilon omega a) (Icc (0 : ℝ) a) := by
  obtain ⟨M, hM, hbound⟩ := exists_suzukiFredholmKernel_bound (a := a) homega
  exact continuousOn_fredholmMinor_left (suzukiFredholmKernel omega)
    (continuous_suzukiFredholmKernel homega) ha hM ⟨ha, le_rfl⟩ hbound epsilon.coeff

/-- Continuous compact realization of Suzuki's boundary first minor. -/
def suzukiFredholmBoundaryMinorContinuous
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 0 ≤ a) : C(ClosedInterval 0 a, ℂ) where
  toFun x := suzukiFredholmBoundaryMinor epsilon omega a (x : ℝ)
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (continuousOn_suzukiFredholmBoundaryMinor epsilon homega ha)

/-- `L²` class of the continuous boundary first minor. -/
def suzukiFredholmBoundaryMinorL2
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 0 ≤ a) : IntervalL2 0 a :=
  ContinuousMap.toLp 2 (volume : Measure (ClosedInterval 0 a)) ℂ
    (suzukiFredholmBoundaryMinorContinuous epsilon omega a homega ha)

theorem suzukiFredholmBoundaryMinorL2_ae
    (epsilon : SuzukiHankelSign) (omega a : ℝ)
    (homega : 1 < omega) (ha : 0 ≤ a) :
    (suzukiFredholmBoundaryMinorL2 epsilon omega a homega ha :
        ClosedInterval 0 a → ℂ) =ᵐ[volume]
      suzukiFredholmBoundaryMinorContinuous epsilon omega a homega ha := by
  exact ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 a))) (𝕜 := ℂ)
    (suzukiFredholmBoundaryMinorContinuous epsilon omega a homega ha)

/-- The literal boundary minor satisfies Suzuki's signed resolvent equation with the boundary
source multiplied by the classical Fredholm determinant. -/
theorem suzukiFredholmBoundaryMinorL2_resolvent_equation_scaled
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelResolventOperator epsilon omega a (by linarith)
        (suzukiFredholmBoundaryMinorL2 epsilon omega a homega
          (lt_trans zero_lt_one ha).le) =
      suzukiFredholmDeterminant epsilon omega a •
        suzukiHankelBoundarySource omega a (by linarith) ha := by
  let K := suzukiFredholmKernel omega
  have ha0 : 0 ≤ a := (lt_trans zero_lt_one ha).le
  let V := suzukiFredholmBoundaryMinorL2 epsilon omega a homega ha0
  let C := suzukiFredholmBoundaryMinorContinuous epsilon omega a homega ha0
  let det := suzukiFredholmDeterminant epsilon omega a
  have homegaHalf : 1 / 2 < omega := by linarith
  obtain ⟨M, hM, hbound⟩ := exists_suzukiFredholmKernel_bound (a := a) homega
  have hfred (x : ClosedInterval 0 a) :
      suzukiFredholmBoundaryMinor epsilon omega a (x : ℝ) +
          epsilon.coeff * (∫ u in (0 : ℝ)..a,
            K (x : ℝ) u * suzukiFredholmBoundaryMinor epsilon omega a u) =
        K (x : ℝ) a * det := by
    exact fredholmMinor_add_integral_eq_kernel_mul_determinant K
      (continuous_suzukiFredholmKernel homega) ha0 hM x.property
      ⟨ha0, le_rfl⟩ hbound epsilon.coeff
  have hVae : (V : ClosedInterval 0 a → ℂ) =ᵐ[volume] C := by
    exact suzukiFredholmBoundaryMinorL2_ae epsilon omega a homega ha0
  have hIntegral (x : ClosedInterval 0 a) :
      (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * V y ∂volume) =
        ∫ u in (0 : ℝ)..a,
          K (x : ℝ) u * suzukiFredholmBoundaryMinor epsilon omega a u := by
    change (∫ y : ClosedInterval 0 a,
      K (x : ℝ) (y : ℝ) * V y ∂volume) = _
    calc
      (∫ y : ClosedInterval 0 a, K (x : ℝ) (y : ℝ) * V y ∂volume) =
          ∫ y : ClosedInterval 0 a, K (x : ℝ) (y : ℝ) * C y ∂volume := by
        apply integral_congr_ae
        filter_upwards [hVae] with y hy
        rw [hy]
      _ = ∫ u in Icc (0 : ℝ) a,
          K (x : ℝ) u * suzukiFredholmBoundaryMinor epsilon omega a u := by
        rw [← MeasureTheory.integral_subtype measurableSet_Icc]
        rfl
      _ = ∫ u in (0 : ℝ)..a,
          K (x : ℝ) u * suzukiFredholmBoundaryMinor epsilon omega a u := by
        rw [intervalIntegral.integral_of_le ha0, ← integral_Icc_eq_integral_Ioc]
  change V + epsilon.coeff •
      suzukiCompressedHankelOperator omega a homegaHalf V =
    det • suzukiHankelBoundarySource omega a homegaHalf ha
  apply Lp.ext
  filter_upwards [Lp.coeFn_add V
      (epsilon.coeff • suzukiCompressedHankelOperator omega a homegaHalf V),
    Lp.coeFn_smul epsilon.coeff
      (suzukiCompressedHankelOperator omega a homegaHalf V),
    suzukiCompressedHankelOperator_coeFn omega a homegaHalf (lt_trans zero_lt_one ha) V,
    hVae, Lp.coeFn_smul det (suzukiHankelBoundarySource omega a homegaHalf ha),
    suzukiHankelBoundarySource_ae homegaHalf ha] with
      x hadd hsmul hoperator hV hdetSmul hsource
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hoperator,
    hV, hdetSmul, Pi.smul_apply, smul_eq_mul, hsource, hIntegral]
  change suzukiFredholmBoundaryMinor epsilon omega a (x : ℝ) +
      epsilon.coeff * _ = det * suzukiSourceHFinite omega (a * (x : ℝ))
  rw [hfred]
  simp only [K, suzukiFredholmKernel]
  rw [mul_comm a (x : ℝ)]
  ring

/-- Invertibility of Suzuki's signed Hankel resolvent identifies the literal first minor with the
Fredholm determinant times Suzuki's `L²` solution, without dividing by the determinant. -/
theorem suzukiFredholmBoundaryMinorL2_eq_det_smul_phi
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiFredholmBoundaryMinorL2 epsilon omega a homega
        (lt_trans zero_lt_one ha).le =
      suzukiFredholmDeterminant epsilon omega a •
        suzukiHankelPhi epsilon omega a (by linarith) ha := by
  let homegaHalf : 1 / 2 < omega := by linarith
  let V := suzukiFredholmBoundaryMinorL2 epsilon omega a homega
    (lt_trans zero_lt_one ha).le
  let phi := suzukiHankelPhi epsilon omega a homegaHalf ha
  let det := suzukiFredholmDeterminant epsilon omega a
  let R := suzukiHankelResolventOperator epsilon omega a homegaHalf
  have hV : R V = det • suzukiHankelBoundarySource omega a homegaHalf ha := by
    exact suzukiFredholmBoundaryMinorL2_resolvent_equation_scaled epsilon homega ha
  have hphi : R phi = suzukiHankelBoundarySource omega a homegaHalf ha :=
    suzukiHankelPhi_resolvent_equation epsilon homegaHalf ha
  have hscaled : R (det • phi) =
      det • suzukiHankelBoundarySource omega a homegaHalf ha := by
    rw [map_smul, hphi]
  have hEq : R V = R (det • phi) := hV.trans hscaled.symm
  let hunit := suzukiHankelResolventOperator_isUnit epsilon homegaHalf ha
  let U := hunit.unit
  have hU : (↑U : IntervalL2 0 a →L[ℂ] IntervalL2 0 a) = R := hunit.unit_spec
  rw [← hU] at hEq
  have hcancel := congrArg
    (fun W : IntervalL2 0 a ↦
      (↑(U⁻¹) : IntervalL2 0 a →L[ℂ] IntervalL2 0 a) W) hEq
  simpa only [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self] using hcancel

/-- Pointwise division-free Fredholm/Suzuki identification on the whole compact aperture. -/
theorem suzukiFredholmBoundaryMinor_eq_det_mul_phiContinuous
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) (x : ClosedInterval 0 a) :
    suzukiFredholmBoundaryMinor epsilon omega a (x : ℝ) =
      suzukiFredholmDeterminant epsilon omega a *
        suzukiHankelPhiContinuous epsilon omega a homega ha x := by
  let ha0 : 0 ≤ a := (lt_trans zero_lt_one ha).le
  let homegaHalf : 1 / 2 < omega := by linarith
  let V := suzukiFredholmBoundaryMinorL2 epsilon omega a homega ha0
  let C := suzukiFredholmBoundaryMinorContinuous epsilon omega a homega ha0
  let phi := suzukiHankelPhi epsilon omega a homegaHalf ha
  let phiC := suzukiHankelPhiContinuous epsilon omega a homega ha
  let det := suzukiFredholmDeterminant epsilon omega a
  have hL2 : V = det • phi := by
    exact suzukiFredholmBoundaryMinorL2_eq_det_smul_phi epsilon homega ha
  have hLpAe : (V : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      (det • phi : IntervalL2 0 a) := by rw [hL2]
  have hCae : (V : ClosedInterval 0 a → ℂ) =ᵐ[volume] C :=
    suzukiFredholmBoundaryMinorL2_ae epsilon omega a homega ha0
  have hsmul := Lp.coeFn_smul det phi
  have hphiC : (phiC : ClosedInterval 0 a → ℂ) =ᵐ[volume] phi :=
    suzukiHankelPhiContinuous_ae epsilon homega ha
  have hae : (C : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      (det • phiC : C(ClosedInterval 0 a, ℂ)) := by
    filter_upwards [hLpAe, hCae, hsmul, hphiC] with y hLp hC hsmulY hphiY
    calc
      C y = V y := hC.symm
      _ = (det • phi : IntervalL2 0 a) y := hLp
      _ = det * phi y := by rw [hsmulY, Pi.smul_apply, smul_eq_mul]
      _ = det * phiC y := by rw [hphiY]
      _ = (det • phiC : C(ClosedInterval 0 a, ℂ)) y := by
        rw [ContinuousMap.smul_apply, smul_eq_mul]
  letI := suzukiFredholm_closedInterval_volume_isOpenPosMeasure
    (lt_trans zero_lt_one ha)
  have hpoint : (C : ClosedInterval 0 a → ℂ) =
      (det • phiC : C(ClosedInterval 0 a, ℂ)) :=
    (Continuous.ae_eq_iff_eq (volume : Measure (ClosedInterval 0 a))
      C.continuous (det • phiC).continuous).mp hae
  exact congrFun hpoint x

/-- Joint diagonal continuity of the fixed-window pointwise solution: aperture and evaluation
point move together, with the latter clipped to the fixed compact window. -/
theorem continuousAt_suzukiFixedWindowPhiPoint_diagonal
    (epsilon : SuzukiHankelSign) {omega B a : ℝ}
    (homega : 1 < omega) (hB : 1 < B) (ha0 : 0 < a) (haB : a < B) :
    ContinuousAt (fun b : ℝ =>
      suzukiFixedWindowPhiPoint epsilon omega B homega hB b
        (Set.projIcc 0 B (by linarith) b)) a := by
  let u : ℝ → IntervalL2 0 B :=
    suzukiFixedWindowPhi epsilon omega B (by linarith) hB
  let x : ℝ → ClosedInterval 0 B := Set.projIcc 0 B (by linarith)
  have hu : ContinuousAt u a :=
    continuousAt_suzukiFixedWindowPhi epsilon (by linarith) hB ha0 haB
  have hcut : ContinuousAt (fun b => suzukiApertureCutoff b B (u b)) a :=
    continuousAt_suzukiApertureCutoff_apply₂ B a hu
  have hx : Continuous x := by
    exact continuous_projIcc
  have hout : ContinuousAt (fun b =>
      suzukiCompressedHankelContinuousOutput omega B (by linarith) hB
        (suzukiApertureCutoff b B (u b)) (x b)) a := by
    change ContinuousAt (fun b =>
      suzukiCompressedHankelFunctionalContinuous omega B (by linarith) hB (x b)
        (suzukiApertureCutoff b B (u b))) a
    exact ((suzukiCompressedHankelFunctionalContinuous omega B (by linarith) hB).continuous
      |>.comp hx).continuousAt.clm_apply hcut
  have hxa : x a = ⟨a, ⟨ha0.le, haB.le⟩⟩ := by
    change Set.projIcc 0 B (by linarith) a = _
    exact Set.projIcc_of_mem (by linarith) ⟨ha0.le, haB.le⟩
  have hproduct : ContinuousAt (fun b : ℝ => b * (x b : ℝ)) a :=
    continuousAt_id.mul (continuous_subtype_val.comp hx).continuousAt
  have hsource : ContinuousAt
      (fun b : ℝ => suzukiSourceHFinite omega (b * (x b : ℝ))) a := by
    exact (continuousAt_suzukiSourceHFinite homega (mul_pos ha0 ha0)).comp_of_eq
      hproduct (by rw [hxa])
  exact hsource.sub (continuousAt_const.mul hout)

/-- Suzuki's diagonal endpoint value `a ↦ φ_a(a)` on the physical aperture half-line. -/
def suzukiHankelPhiEndpoint
    (epsilon : SuzukiHankelSign) (omega : ℝ) (homega : 1 < omega) :
    Ioi (1 : ℝ) → ℂ := fun a =>
  suzukiHankelPhiGlobal epsilon omega (a : ℝ) homega a.property (a : ℝ)

/-- The moving endpoint value `a ↦ φ_a(a)` is continuous. -/
theorem continuous_suzukiHankelPhiEndpoint
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) :
    Continuous (suzukiHankelPhiEndpoint epsilon omega homega) := by
  rw [continuous_iff_continuousAt]
  intro a
  let B : ℝ := (a : ℝ) + 1
  have haB : (a : ℝ) < B := by simp [B]
  have hB : 1 < B := lt_trans a.property haB
  let localPhi : ℝ → ℂ := fun b =>
    suzukiFixedWindowPhiPoint epsilon omega B homega hB b
      (Set.projIcc 0 B (by linarith) b)
  have hlocal : ContinuousAt localPhi (a : ℝ) :=
    continuousAt_suzukiFixedWindowPhiPoint_diagonal epsilon homega hB
      (lt_trans zero_lt_one a.property) haB
  have hlocalSubtype : ContinuousAt (fun b : Ioi (1 : ℝ) => localPhi (b : ℝ)) a :=
    hlocal.comp_of_eq continuousAt_subtype_val rfl
  have hbelow : ∀ᶠ b : Ioi (1 : ℝ) in 𝓝 a, (b : ℝ) < B :=
    continuousAt_subtype_val (Iio_mem_nhds haB)
  have heq : suzukiHankelPhiEndpoint epsilon omega homega =ᶠ[𝓝 a]
      fun b : Ioi (1 : ℝ) => localPhi (b : ℝ) := by
    filter_upwards [hbelow] with b hbB
    have hb0 : 0 ≤ (b : ℝ) := le_trans (by norm_num) b.property.le
    have hproj : Set.projIcc 0 B (by linarith) (b : ℝ) =
        (⟨(b : ℝ), ⟨hb0, hbB.le⟩⟩ : ClosedInterval 0 B) := by
      exact Set.projIcc_of_mem (by linarith) ⟨hb0, hbB.le⟩
    change suzukiHankelPhiGlobal epsilon omega (b : ℝ) homega b.property (b : ℝ) =
      suzukiFixedWindowPhiPoint epsilon omega B homega hB (b : ℝ)
        (Set.projIcc 0 B (by linarith) (b : ℝ))
    rw [hproj]
    exact (suzukiFixedWindowPhiPoint_eq_global epsilon homega b.property hB hbB.le
      ⟨(b : ℝ), ⟨hb0, hbB.le⟩⟩ (lt_trans zero_lt_one b.property)).symm
  exact hlocalSubtype.congr_of_eventuallyEq heq

/-- Real-line form of the endpoint field, extended by zero outside physical apertures. -/
def suzukiHankelPhiEndpointReal
    (epsilon : SuzukiHankelSign) (omega : ℝ) (homega : 1 < omega) (a : ℝ) : ℂ :=
  if ha : 1 < a then
    suzukiHankelPhiGlobal epsilon omega a homega ha a
  else 0

theorem suzukiHankelPhiEndpointReal_of_one_lt
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiHankelPhiEndpointReal epsilon omega homega a =
      suzukiHankelPhiGlobal epsilon omega a homega ha a := by
  simp only [suzukiHankelPhiEndpointReal, dif_pos ha]

theorem suzukiHankelPhiEndpointReal_im
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) (a : ℝ) :
    (suzukiHankelPhiEndpointReal epsilon omega homega a).im = 0 := by
  rw [suzukiHankelPhiEndpointReal]
  split_ifs with ha
  · exact suzukiHankelPhiGlobal_real epsilon homega ha
  · rfl

/-- The real-line endpoint field is continuous throughout the physical aperture half-line. -/
theorem continuousOn_suzukiHankelPhiEndpointReal
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) :
    ContinuousOn (suzukiHankelPhiEndpointReal epsilon omega homega) (Ioi (1 : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (fun a : Ioi (1 : ℝ) =>
      suzukiHankelPhiEndpointReal epsilon omega homega (a : ℝ)) =
      suzukiHankelPhiEndpoint epsilon omega homega := by
    funext a
    exact suzukiHankelPhiEndpointReal_of_one_lt epsilon homega a.property
  change Continuous (fun a : Ioi (1 : ℝ) =>
    suzukiHankelPhiEndpointReal epsilon omega homega (a : ℝ))
  rw [heq]
  exact continuous_suzukiHankelPhiEndpoint epsilon homega

/-- Division-free moving-aperture ODE for Suzuki's literal Fredholm determinant. -/
theorem hasDerivAt_suzukiFredholmDeterminant
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    HasDerivAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u)
      (epsilon.coeff * suzukiFredholmDeterminant epsilon omega a *
        suzukiHankelPhiGlobal epsilon omega a homega ha a) a := by
  let A : ℝ := a + 1
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have haA : a < A := by simp [A]
  obtain ⟨M, hM, hbound⟩ :=
    exists_suzukiFredholmKernel_bound (a := A) homega
  have hderiv := hasDerivAt_determinant (suzukiFredholmKernel omega)
    (continuous_suzukiFredholmKernel homega) ha0 haA hM hbound epsilon.coeff
  have hminorOrdered :
      orderedFredholmMinor (suzukiFredholmKernel omega) a epsilon.coeff a a =
        fredholmMinor (suzukiFredholmKernel omega) a epsilon.coeff a a := by
    exact (fredholmMinor_eq_orderedFredholmMinor (suzukiFredholmKernel omega)
      (continuous_suzukiFredholmKernel homega) ha0.le epsilon.coeff a a).symm
  let endpoint : ClosedInterval 0 a := ⟨a, ⟨ha0.le, le_rfl⟩⟩
  have hminor :
      fredholmMinor (suzukiFredholmKernel omega) a epsilon.coeff a a =
        suzukiFredholmDeterminant epsilon omega a *
          suzukiHankelPhiGlobal epsilon omega a homega ha a := by
    change suzukiFredholmBoundaryMinor epsilon omega a (endpoint : ℝ) = _
    rw [suzukiFredholmBoundaryMinor_eq_det_mul_phiContinuous epsilon homega ha endpoint,
      ← suzukiHankelPhiGlobal_eq_continuousRepresentative epsilon homega ha endpoint]
  change HasDerivAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u)
    (epsilon.coeff *
      orderedFredholmMinor (suzukiFredholmKernel omega) a epsilon.coeff a a) a at hderiv
  simpa only [hminorOrdered, hminor, mul_assoc] using hderiv

theorem hasDerivAt_suzukiFredholmDeterminant_endpointReal
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    HasDerivAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u)
      (epsilon.coeff * suzukiFredholmDeterminant epsilon omega a *
        suzukiHankelPhiEndpointReal epsilon omega homega a) a := by
  simpa only [suzukiHankelPhiEndpointReal_of_one_lt epsilon homega ha] using
    hasDerivAt_suzukiFredholmDeterminant epsilon homega ha

/-- On every nonnegative subcritical aperture Suzuki's kernel vanishes on the entire compression
square, so the literal Fredholm series has only its zeroth coefficient. -/
theorem suzukiFredholmDeterminant_eq_one_of_nonneg_of_le_one
    (epsilon : SuzukiHankelSign) {omega a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    suzukiFredholmDeterminant epsilon omega a = 1 := by
  let K := suzukiFredholmKernel omega
  have hzero : ∀ x ∈ Icc (0 : ℝ) a, ∀ y ∈ Icc (0 : ℝ) a, ‖K x y‖ ≤ 0 := by
    intro x hx y hy
    have hxy : x * y ≤ 1 := by
      calc
        x * y ≤ a * a := mul_le_mul hx.2 hy.2 hy.1 ha0
        _ ≤ 1 := by nlinarith
    have hKxy : K x y = 0 := by
      simp only [K, suzukiFredholmKernel, suzukiSourceHFinite]
      rw [if_neg (not_lt_of_ge hxy)]
    rw [hKxy, norm_zero]
  have hcoeff (n : ℕ) : fredholmCoefficient K a (n + 1) = 0 := by
    have hnorm := fredholmCoefficient_norm_le K (a := a) (M := 0)
      ha0 hzero (n + 1)
    have hnorm0 : ‖fredholmCoefficient K a (n + 1)‖ ≤ 0 := by
      simpa using hnorm
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  have hsum : Summable (fun n : ℕ =>
      epsilon.coeff ^ n * fredholmCoefficient K a n) :=
    determinant_summable K ha0 le_rfl hzero epsilon.coeff
  change (∑' n : ℕ, epsilon.coeff ^ n * fredholmCoefficient K a n) = 1
  rw [hsum.tsum_eq_zero_add]
  simp only [fredholmCoefficient_zero, pow_zero, one_mul, hcoeff, mul_zero, tsum_zero,
    add_zero]

/-- At aperture one the literal Fredholm determinant is exactly one. -/
theorem suzukiFredholmDeterminant_one
    (epsilon : SuzukiHankelSign) {omega : ℝ} :
    suzukiFredholmDeterminant epsilon omega 1 = 1 := by
  exact suzukiFredholmDeterminant_eq_one_of_nonneg_of_le_one epsilon zero_le_one le_rfl

/-- Exact transport law obtained from the division-free determinant ODE. -/
theorem suzukiFredholmDeterminant_transport
    (epsilon : SuzukiHankelSign) {omega b a : ℝ}
    (homega : 1 < omega) (hb : 1 < b) (hba : b ≤ a) :
    suzukiFredholmDeterminant epsilon omega a =
      Complex.exp (∫ u in b..a,
        epsilon.coeff * suzukiHankelPhiEndpointReal epsilon omega homega u) *
        suzukiFredholmDeterminant epsilon omega b := by
  let D : ℝ → ℂ := fun u => suzukiFredholmDeterminant epsilon omega u
  let c : ℝ → ℂ := fun u =>
    epsilon.coeff * suzukiHankelPhiEndpointReal epsilon omega homega u
  let P : ℝ → ℂ := fun t => ∫ u in b..t, c u
  let E : ℝ → ℂ := fun t => Complex.exp (-P t) * D t
  have hcOn : ContinuousOn c (Ioi (1 : ℝ)) := by
    exact continuousOn_const.mul
      (continuousOn_suzukiHankelPhiEndpointReal epsilon homega)
  have hEderiv : ∀ x ∈ Icc b a, HasDerivAt E 0 x := by
    intro x hx
    have hxOne : x ∈ Ioi (1 : ℝ) := hb.trans_le hx.1
    have hcx : ContinuousAt c x :=
      hcOn.continuousAt (Ioi_mem_nhds hxOne)
    have hcInt : IntervalIntegrable c volume b x := by
      apply ContinuousOn.intervalIntegrable
      apply hcOn.mono
      intro u hu
      rw [uIcc_of_le hx.1] at hu
      exact hb.trans_le hu.1
    have hP : HasDerivAt P (c x) x := by
      exact intervalIntegral.integral_hasDerivAt_right hcInt
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcOn x hxOne) hcx
    have hD : HasDerivAt D (c x * D x) x := by
      have hraw := hasDerivAt_suzukiFredholmDeterminant_endpointReal epsilon homega hxOne
      simpa only [D, c, mul_assoc, mul_comm, mul_left_comm] using hraw
    dsimp only [E]
    exact (hP.neg.cexp.mul hD).congr_deriv (by ring)
  have hEcont : ContinuousOn E (Icc b a) :=
    HasDerivAt.continuousOn hEderiv
  have hEconst : ∀ x ∈ Icc b a, E x = E b :=
    constant_of_has_deriv_right_zero hEcont fun x hx =>
      (hEderiv x (Ico_subset_Icc_self hx)).hasDerivWithinAt
  have hEa : E a = E b := hEconst a ⟨hba, le_rfl⟩
  have hscaled : Complex.exp (-P a) * D a = D b := by
    simpa only [E, P, intervalIntegral.integral_same, neg_zero, Complex.exp_zero,
      one_mul] using hEa
  change D a = Complex.exp (P a) * D b
  rw [← hscaled]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The literal Fredholm determinant is continuous at the degenerate physical aperture `a = 1`. -/
theorem continuousAt_suzukiFredholmDeterminant_one
    (epsilon : SuzukiHankelSign) {omega : ℝ} (homega : 1 < omega) :
    ContinuousAt (fun u : ℝ => suzukiFredholmDeterminant epsilon omega u) 1 := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_suzukiFredholmKernel_bound (a := (2 : ℝ)) homega
  have hderiv := hasDerivAt_determinant (suzukiFredholmKernel omega)
    (continuous_suzukiFredholmKernel homega) zero_lt_one one_lt_two hM hbound
    epsilon.coeff
  change ContinuousAt (fun u : ℝ =>
    determinant (suzukiFredholmKernel omega) u epsilon.coeff) 1
  exact hderiv.continuousAt

/-- Suzuki's signed classical Fredholm determinant never vanishes at a physical aperture. -/
theorem suzukiFredholmDeterminant_ne_zero
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiFredholmDeterminant epsilon omega a ≠ 0 := by
  let D : ℝ → ℂ := fun u => suzukiFredholmDeterminant epsilon omega u
  have hDOne : D 1 = 1 := suzukiFredholmDeterminant_one epsilon
  have hDOneNe : D 1 ≠ 0 := by
    rw [hDOne]
    exact one_ne_zero
  have hnear : ∀ᶠ b in 𝓝 (1 : ℝ), D b ≠ 0 :=
    (continuousAt_suzukiFredholmDeterminant_one epsilon homega).eventually_ne
      hDOneNe
  have hright : ∀ᶠ b in 𝓝[>] (1 : ℝ), D b ≠ 0 :=
    Filter.Eventually.filter_mono inf_le_left hnear
  obtain ⟨b, hbne, hb⟩ := (hright.and (Ioo_mem_nhdsGT ha)).exists
  have htransport := suzukiFredholmDeterminant_transport epsilon homega hb.1 hb.2.le
  change D a = Complex.exp (∫ u in b..a,
    epsilon.coeff * suzukiHankelPhiEndpointReal epsilon omega homega u) * D b at htransport
  change D a ≠ 0
  rw [htransport]
  exact mul_ne_zero (Complex.exp_ne_zero _) hbne

private theorem positiveReal_mul_mem_slitPlane
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (r : ℂ) * z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hz ⊢
  rcases hz with hz | hz
  · left
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using mul_pos hr hz
  · right
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      using mul_ne_zero hr.ne' hz

/-- The determinant stays in the principal logarithm's slit plane. -/
theorem suzukiFredholmDeterminant_mem_slitPlane
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    suzukiFredholmDeterminant epsilon omega a ∈ Complex.slitPlane := by
  let D : ℝ → ℂ := fun u => suzukiFredholmDeterminant epsilon omega u
  have hDOne : D 1 = 1 := suzukiFredholmDeterminant_one epsilon
  have hDOneSlit : D 1 ∈ Complex.slitPlane := by
    rw [hDOne]
    exact Complex.one_mem_slitPlane
  have hnear : ∀ᶠ b in 𝓝 (1 : ℝ), D b ∈ Complex.slitPlane :=
    (continuousAt_suzukiFredholmDeterminant_one epsilon homega)
      (Complex.isOpen_slitPlane.mem_nhds hDOneSlit)
  have hright : ∀ᶠ b in 𝓝[>] (1 : ℝ), D b ∈ Complex.slitPlane :=
    Filter.Eventually.filter_mono inf_le_left hnear
  obtain ⟨b, hbSlit, hb⟩ := (hright.and (Ioo_mem_nhdsGT ha)).exists
  let c : ℝ → ℂ := fun u =>
    epsilon.coeff * suzukiHankelPhiEndpointReal epsilon omega homega u
  let I : ℂ := ∫ u in b..a, c u
  have hcOn : ContinuousOn c (Ioi (1 : ℝ)) := by
    exact continuousOn_const.mul
      (continuousOn_suzukiHankelPhiEndpointReal epsilon homega)
  have hcInt : IntervalIntegrable c volume b a := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb.2.le
    apply hcOn.mono
    intro u hu
    exact hb.1.trans_le hu.1
  have hcIm (u : ℝ) : (c u).im = 0 := by
    cases epsilon <;>
      simp [c, SuzukiHankelSign.coeff, suzukiHankelPhiEndpointReal_im]
  have hIim : I.im = 0 := by
    dsimp only [I]
    calc
      (∫ u in b..a, c u).im = ∫ u in b..a, (c u).im := by
        symm
        simpa only [RCLike.im_eq_complex_im] using
          (intervalIntegral.intervalIntegral_im hcInt)
      _ = 0 := by
        simp only [hcIm]
        exact intervalIntegral.integral_zero
  have hIeq : I = (I.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hIim
  have hExp : Complex.exp I = (Real.exp I.re : ℂ) := by
    rw [hIeq]
    exact (Complex.ofReal_exp I.re).symm
  have htransport := suzukiFredholmDeterminant_transport epsilon homega hb.1 hb.2.le
  change D a = Complex.exp I * D b at htransport
  change D a ∈ Complex.slitPlane
  rw [htransport, hExp]
  exact positiveReal_mul_mem_slitPlane (Real.exp_pos _) hbSlit

/-- Suzuki (2012), Eq. (4.19), simultaneously for both signs: the logarithmic derivative of the
literal classical Fredholm determinant is the signed endpoint resolvent value. -/
theorem suzukiCanonicalHankelEquation419
    (epsilon : SuzukiHankelSign) {omega a : ℝ}
    (homega : 1 < omega) (ha : 1 < a) :
    HasDerivAt
      (fun u : ℝ => Complex.log (suzukiFredholmDeterminant epsilon omega u))
      (epsilon.coeff *
        suzukiHankelPhiGlobal epsilon omega a homega ha a) a := by
  have hD := hasDerivAt_suzukiFredholmDeterminant epsilon homega ha
  have hslit := suzukiFredholmDeterminant_mem_slitPlane epsilon homega ha
  have hlog := hD.clog_real hslit
  convert hlog using 1
  field_simp [suzukiFredholmDeterminant_ne_zero epsilon homega ha]

/-- Positive-sign form of Suzuki's first identity in Eq. (4.19). -/
theorem suzukiCanonicalHankelEquation419_positive
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    HasDerivAt
      (fun u : ℝ => Complex.log
        (suzukiFredholmDeterminant SuzukiHankelSign.positive omega u))
      (suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha a) a := by
  simpa using suzukiCanonicalHankelEquation419 SuzukiHankelSign.positive homega ha

/-- Negative-sign form of Suzuki's second identity in Eq. (4.19). -/
theorem suzukiCanonicalHankelEquation419_negative
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    HasDerivAt
      (fun u : ℝ => Complex.log
        (suzukiFredholmDeterminant SuzukiHankelSign.negative omega u))
      (-suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha a) a := by
  simpa using suzukiCanonicalHankelEquation419 SuzukiHankelSign.negative homega ha

end RHTower
