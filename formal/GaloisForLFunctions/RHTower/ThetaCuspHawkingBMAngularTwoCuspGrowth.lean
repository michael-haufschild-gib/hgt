import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoPrincipalTensor
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoCuspNative
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets

/-!
# Cusp growth of both original tensor polarizations

Integer translation identifies the full restored inverse with the native correction
minus the complete principal response throughout the high cusp. Exact principal tensor
cancellation leaves the full gradient-product remainder and the correction Hessian.
Compact evaluation, modular unfolding and integration by parts give polynomial growth
for both independent holomorphic polarizations, retaining every connection term.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff MatrixGroups ComplexConjugate
namespace RHTower.D4BMAngularTwoCuspGrowth
open D4BMModularCore D4BMHorizon D4BMAngularTwoTensor
noncomputable section
set_option autoImplicit false

/-- Above the cutoff, the actual invariant extension equals the complete principal response,
including at every translated closed-cell seam. -/
theorem globalCuspCutoff_high (q : XiZeroCopy) (z : UpperHalfPlane) (hz : 3 < z.im) :
    D4BMAngularTwo.globalCuspCutoff q z =
      D4BMAngularTwo.cuspResponse q (D4BMGlobalAngularResponse.coordinates z) := by
  let n : ℤ := -⌊z.re+1/2⌋
  have hn0 := Int.floor_le (z.re+1/2)
  have hn1 := Int.lt_floor_add_one (z.re+1/2)
  have hr : |(T^n • z).re| ≤ (1:ℝ)/2 := by
    rw [ModularGroup.re_T_zpow_smul]
    simp only [n,Int.cast_neg]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hfd : T^n • z ∈ fd := by
    refine ⟨?_,hr⟩
    change 1 ≤ (T^n • z).re * (T^n • z).re + (T^n • z).im * (T^n • z).im
    rw [ModularGroup.im_T_zpow_smul]
    nlinarith [sq_nonneg (T^n • z).re]
  have hi := D4BMAngularTwo.globalCuspCutoff_invariant q (QuotientGroup.mk (T^n)) z
  simp only [PSL2Z_mk_smul] at hi
  rw [← hi,D4BMAngularTwo.globalCuspCutoff_eq_on_fd q _ hfd]
  simp only [D4BMAngularTwo.cutoffResponse,D4BMGlobalAngularResponse.cutoff,
    D4BMAngularTwo.cuspResponse,D4BMQuadraticMixedSource.cuspPowerResponse,
    D4BMQuadraticMixedSource.powerResponse,D4BMGlobalAngularResponse.coordinates,
    Matrix.cons_val_one,Matrix.cons_val_zero,ModularGroup.im_T_zpow_smul]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp

/-- The native finite-energy correction in the original angular coordinates. -/
def correction (q : XiZeroCopy) (z : Fin 2 → ℝ) : ℂ :=
  D4BMAngularTwo.globalResponse q (ofComplex (angularCoordinates.symm z))

private theorem symm_im (z : Fin 2 → ℝ) : (angularCoordinates.symm z).im = z 1 := by
  change ((z 0:ℂ)+(z 1:ℂ)*Complex.I).im = z 1
  simp

private theorem coordinates_section (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    D4BMGlobalAngularResponse.coordinates (ofComplex (angularCoordinates.symm z)) = z := by
  have hi : 0 < (angularCoordinates.symm z).im := by simpa only [symm_im] using hz
  change angularCoordinates (ofComplex (angularCoordinates.symm z) : ℂ) = z
  rw [ofComplex_apply_of_im_pos hi,angularCoordinates.apply_symm_apply]

/-- Full germ equality, so every derivative of the restored inverse splits without seam terms. -/
theorem coordinateResponse_high_germ (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    D4BMAngularTwo.coordinateResponse q =ᶠ[𝓝 z]
      (fun w => correction q w + -D4BMAngularTwo.cuspResponse q w) := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
  have hi : 0 < (angularCoordinates.symm w).im := by
    rw [symm_im]
    linarith
  have hh : 3 < (ofComplex (angularCoordinates.symm w)).im := by
    rw [← UpperHalfPlane.coe_im,ofComplex_apply_of_im_pos hi,symm_im]
    exact hw
  simp only [D4BMAngularTwo.coordinateResponse,D4BMAngularTwo.smoothFullResponse,correction,
    globalCuspCutoff_high q _ hh,coordinates_section w (by linarith),sub_eq_add_neg]

private theorem correction_smooth (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (correction q) z := by
  have hi : 0 < (angularCoordinates.symm z).im := by simpa only [symm_im] using hz
  have h := D4BMAngularTwo.globalResponse_smooth q (ofComplex (angularCoordinates.symm z))
  change ContDiffAt ℝ ∞ (D4BMAngularTwo.globalResponse q ∘ ofComplex) _ at h
  rw [ofComplex_apply_of_im_pos hi] at h
  change ContDiffAt ℝ ∞ ((D4BMAngularTwo.globalResponse q ∘ ofComplex) ∘ angularCoordinates.symm) z
  exact h.comp z angularCoordinates.symm.contDiff.contDiffAt

private theorem principalResponse_smooth (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (fun w => -D4BMAngularTwo.cuspResponse q w) z := by
  have h : ContDiffOn ℝ ∞ (D4BMAngularTwo.cuspResponse q) D4BMAngularSeries.domain := by
    unfold D4BMAngularTwo.cuspResponse D4BMQuadraticMixedSource.cuspPowerResponse
      D4BMQuadraticMixedSource.powerResponse
    exact ((contDiffOn_const.mul (D4BMAngularSeries.height_cpow_contDiffOn _ ∞)).add
      (contDiffOn_const.mul (D4BMAngularSeries.height_cpow_contDiffOn _ ∞))).add
      (contDiffOn_const.mul (D4BMAngularSeries.height_cpow_contDiffOn _ ∞))
  exact (h.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).neg

private theorem partial_add {f g : (Fin 2 → ℝ) → ℂ} {z : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin 2) :
    coordDeriv i (fun w => f w+g w) z = coordDeriv i f z+coordDeriv i g z := by
  simp only [coordDeriv,fderiv_fun_add hf hg,add_apply]

private theorem response_partial (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) (i : Fin 2) :
    coordDeriv i (D4BMAngularTwo.coordinateResponse q) z =
      coordDeriv i (correction q) z + coordDeriv i (fun w => -D4BMAngularTwo.cuspResponse q w) z := by
  have he := (coordinateResponse_high_germ q z hz).fderiv_eq (𝕜 := ℝ)
  change (fderiv ℝ (D4BMAngularTwo.coordinateResponse q) z) _ = _
  rw [he]
  exact partial_add ((correction_smooth q z (by linarith)).differentiableAt (by simp))
    ((principalResponse_smooth q z (by linarith)).differentiableAt (by simp)) i

private theorem response_second (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) (i j : Fin 2) :
    coordDeriv i (coordDeriv j (D4BMAngularTwo.coordinateResponse q)) z =
      coordDeriv i (coordDeriv j (correction q)) z +
      coordDeriv i (coordDeriv j (fun w => -D4BMAngularTwo.cuspResponse q w)) z := by
  have he : coordDeriv j (D4BMAngularTwo.coordinateResponse q) =ᶠ[𝓝 z]
      (fun w => coordDeriv j (correction q) w +
        coordDeriv j (fun v => -D4BMAngularTwo.cuspResponse q v) w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact response_partial q w hw j
  change (fderiv ℝ (coordDeriv j (D4BMAngularTwo.coordinateResponse q)) z) _ = _
  rw [he.fderiv_eq (𝕜 := ℝ)]
  exact partial_add
    (D4BMHorizon.coordDeriv_hasFDerivAt ((contDiffAt_infty.mp (correction_smooth q z (by linarith))) 2) j).differentiableAt
    (D4BMHorizon.coordDeriv_hasFDerivAt ((contDiffAt_infty.mp (principalResponse_smooth q z (by linarith))) 2) j).differentiableAt i

/-- Exact first component: the complete gradient remainder plus the native correction Hessian. -/
theorem defectA_high (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    defectA q z =
      (D4BMSquareCuspJets.gradientProductRemainder (D4BMGlobalAngularResponse.center q) 0 0 z-
        D4BMSquareCuspJets.gradientProductRemainder (D4BMGlobalAngularResponse.center q) 1 1 z)/2+
      eigenvalue q*((coordDeriv 0 (coordDeriv 0 (correction q)) z-
        coordDeriv 1 (coordDeriv 1 (correction q)) z)/2-(z 1:ℂ)⁻¹*coordDeriv 1 (correction q) z) := by
  have hp := (D4BMAngularTwoPrincipalTensor.actual_principal_components_zero q
    (ofComplex (angularCoordinates.symm z))).1
  rw [coordinates_section z (by linarith)] at hp
  simp only [defectA,componentA,response_partial q z hz,response_second q z hz]
  simp only [componentA] at hp
  change _ = ( (coordDeriv 0 (source q) z*coordDeriv 0 (source q) z-
    coordDeriv 0 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z*
    coordDeriv 0 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z)-
    (coordDeriv 1 (source q) z*coordDeriv 1 (source q) z-
    coordDeriv 1 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z*
    coordDeriv 1 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z))/2+_
  linear_combination hp

/-- Exact off-diagonal component, retaining the inverse-height connection term. -/
theorem defectB_high (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 3 < z 1) :
    defectB q z =
      D4BMSquareCuspJets.gradientProductRemainder (D4BMGlobalAngularResponse.center q) 0 1 z+
      eigenvalue q*(coordDeriv 0 (coordDeriv 1 (correction q)) z+
        (z 1:ℂ)⁻¹*coordDeriv 0 (correction q) z) := by
  have hp := (D4BMAngularTwoPrincipalTensor.actual_principal_components_zero q
    (ofComplex (angularCoordinates.symm z))).2
  rw [coordinates_section z (by linarith)] at hp
  simp only [defectB,componentB,response_partial q z hz,response_second q z hz]
  simp only [componentB] at hp
  change _ = (coordDeriv 0 (source q) z*coordDeriv 1 (source q) z-
    coordDeriv 0 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z*
    coordDeriv 1 (D4BMGlobalAngularResponse.principal (D4BMGlobalAngularResponse.center q)) z)+_
  linear_combination hp

/-- The native correction transports to its actual planar field, with no restriction on height. -/
theorem correction_planar (q : XiZeroCopy) :
    correction q ∘ angularCoordinates = D4BMAngularTwo.globalResponse q ∘ ofComplex := by
  funext z
  simp only [Function.comp_apply,correction,angularCoordinates.symm_apply_apply]

/-- Mixed correction derivatives use the same two original chart directions. -/
theorem correction_planar_second (q : XiZeroCopy) (i j : Fin 2) (z : ℂ) :
    coordDeriv i (coordDeriv j (correction q)) (angularCoordinates z) =
      fderiv ℝ (fun w => fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) w (direction j))
        z (direction i) := by
  rw [← correction_planar]
  simp_rw [angularCoordinates_derivative]
  exact (angularCoordinates_derivative (coordDeriv j (correction q)) i z).symm

/-- First correction derivatives transport through the same exact linear chart. -/
theorem correction_planar_first (q : XiZeroCopy) (i : Fin 2) (z : ℂ) :
    coordDeriv i (correction q) (angularCoordinates z) =
      fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) z (direction i) := by
  rw [← correction_planar]
  exact (angularCoordinates_derivative (correction q) i z).symm

open MeasureTheory Metric D4BMAngularTwoCuspTest D4BMAngularTwoCuspNative

/-- Both tests needed for the independent complex polarizations. -/
def evaluationKernel (b : Bool) (z : ℂ) : ℂ :=
  if b then conj (kernel z) else kernel z

private theorem evaluationKernel_smooth (b : Bool) : ContDiff ℝ ∞ (evaluationKernel b) := by
  cases b
  · exact kernel_smooth
  · exact Complex.conjCLE.contDiff.comp kernel_smooth

private theorem evaluationKernel_compact (b : Bool) : HasCompactSupport (evaluationKernel b) := by
  cases b
  · exact kernel_compact
  · exact kernel_compact.mono (by intro z hz he; exact hz (by simp [evaluationKernel,he]))

private theorem evaluationKernel_support (b : Bool) :
    tsupport (evaluationKernel b) ⊆ closedBall 0 (1/4) := by
  cases b
  · exact kernel_support
  · exact (closure_mono (by intro z hz he; exact hz (by simp [evaluationKernel,he]))).trans kernel_support

private theorem translated_support (b : Bool) (c : ℂ) :
    tsupport (fun z => evaluationKernel b (z-c)) ⊆ closedBall c (1/4) := by
  intro z hz
  have h := evaluationKernel_support b
    (tsupport_comp_subset_preimage (evaluationKernel b) (continuous_id.sub continuous_const) hz)
  simpa only [mem_closedBall,dist_eq_norm,sub_zero,Pi.sub_apply,id_eq] using h

/-- The actual evaluation kernel or its conjugate on the original positive-height chart. -/
def evaluationTest (b : Bool) (c : ℂ) (hc : 3 < c.im) : PlanarChartTest where
  field z := evaluationKernel b (z-c)
  smooth := (evaluationKernel_smooth b).comp (contDiff_id.sub contDiff_const)
  compact := (evaluationKernel_compact b).comp_homeomorph (Homeomorph.subRight c)
  support := by
    intro z hz
    have h := translated_support b c hz
    rw [mem_closedBall,dist_eq_norm] at h
    have hi := (Complex.abs_im_le_norm (z-c)).trans h
    rw [Complex.sub_im] at hi
    have hl := (abs_le.mp hi).1
    change 0 < z.im
    linarith

private theorem translated_derivative (k : ℂ → ℂ) (hk : ContDiff ℝ ∞ k) (c v z : ℂ) :
    fderiv ℝ (fun w => k (w-c)) z v = fderiv ℝ k (z-c) v := by
  have he := ((hk.differentiable (by simp) (z-c)).hasFDerivAt).comp z
    ((hasFDerivAt_id z).sub_const c)
  change fderiv ℝ (k ∘ fun x => id x-c) z v = _
  rw [he.fderiv,ContinuousLinearMap.comp_apply]
  rfl

private def kernelPartial (b : Bool) (v z : ℂ) : ℂ := fderiv ℝ (evaluationKernel b) z v

private theorem kernelPartial_smooth (b : Bool) (v : ℂ) : ContDiff ℝ ∞ (kernelPartial b v) :=
  ((evaluationKernel_smooth b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem kernelPartial_compact (b : Bool) (v : ℂ) : HasCompactSupport (kernelPartial b v) :=
  (evaluationKernel_compact b).fderiv_apply ℝ v

private theorem evaluationTest_partial (b : Bool) (c : ℂ) (hc : 3 < c.im) (v : ℂ) :
    ((evaluationTest b c hc).derivative v).field = fun z => kernelPartial b v (z-c) := by
  funext z
  exact translated_derivative (evaluationKernel b) (evaluationKernel_smooth b) c v z

/-- Both independent polarization tests control all actual mixed second derivatives. -/
theorem exists_second_test_bound (b : Bool) (v w : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (evaluationTest b c hc).field z*
        fderiv ℝ (fun u => fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) u w) z v‖ ≤
          C*(c.im+1)^2*responseMass q := by
  have hsm : ContDiff ℝ ∞ (fun z => fderiv ℝ (kernelPartial b v) z w) :=
    ((kernelPartial_smooth b v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  obtain ⟨B,hB⟩ := ((kernelPartial_compact b v).fderiv_apply ℝ w).exists_bound_of_continuous hsm.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ (kernelPartial b v) 0 w)).trans (hB 0)
  refine ⟨3*B,by positivity,?_⟩
  intro q c hc
  let g := evaluationTest b c hc
  have hs : tsupport ((g.derivative v).derivative w).field ⊆ closedBall c (1/4) :=
    (tsupport_fderiv_apply_subset ℝ w).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans (translated_support b c))
  have hb (z : ℂ) : ‖((g.derivative v).derivative w).field z‖ ≤ B := by
    change ‖fderiv ℝ (g.derivative v).field z w‖ ≤ B
    rw [show (g.derivative v).field = _ from evaluationTest_partial b c hc v,
      translated_derivative (kernelPartial b v) (kernelPartial_smooth b v)]
    exact hB (z-c)
  have htest := response_test_pairing_bound q ((g.derivative v).derivative w) c hc hs B hb
  have hgreen := congrArg norm (mixed_green g (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v w)
  have he : ‖∫ z : ℂ, (D4BMAngularTwo.globalResponse q ∘ ofComplex) z*
      ((g.derivative v).derivative w).field z‖ ≤ 3*(c.im+1)^2*B*responseMass q := by
    simpa only [Function.comp_apply,mul_comm] using htest
  rw [hgreen] at he
  convert he using 1
  · simp only [mul_comm,g]
  · ring

private theorem divHeight_support (g : PlanarChartTest) :
    tsupport (g.divHeight 1).field ⊆ tsupport g.field :=
  closure_mono (by intro z hz he; exact hz (by simp [PlanarChartTest.divHeight,he]))

/-- Both tests retain the native bound for the complete inverse-height connection term. -/
theorem exists_connection_test_bound (b : Bool) (v : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (evaluationTest b c hc).field z/(z.im:ℂ)*
        fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) z v‖ ≤
          C*(c.im+1)^2*responseMass q := by
  obtain ⟨B,hB⟩ := (evaluationKernel_compact b).exists_bound_of_continuous (evaluationKernel_smooth b).continuous
  obtain ⟨D,hD⟩ := (kernelPartial_compact b v).exists_bound_of_continuous (kernelPartial_smooth b v).continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨3*(D+B*‖(v.im:ℂ)‖),by positivity,?_⟩
  intro q c hc
  let g := evaluationTest b c hc
  have hs : tsupport ((g.divHeight 1).derivative v).field ⊆ closedBall c (1/4) :=
    (tsupport_fderiv_apply_subset ℝ v).trans ((divHeight_support g).trans (translated_support b c))
  have hd (z : ℂ) : ‖(g.derivative v).field z‖ ≤ D := by
    rw [show (g.derivative v).field = _ from evaluationTest_partial b c hc v]
    exact hD (z-c)
  have hb := response_test_pairing_bound q ((g.divHeight 1).derivative v) c hc hs
    (D+B*‖(v.im:ℂ)‖) (divHeight_derivative_bound g c hc (translated_support b c) v B D
      (fun z => hB (z-c)) hd)
  have he := congrArg norm (first_green (g.divHeight 1) (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v)
  simp only [norm_neg,Function.comp_apply] at he
  have hb' : ‖∫ z : ℂ, D4BMAngularTwo.globalResponse q (ofComplex z)*
      ((g.divHeight 1).derivative v).field z‖ ≤
        3*(c.im+1)^2*(D+B*‖(v.im:ℂ)‖)*responseMass q := by
    simpa only [mul_comm] using hb
  rw [he] at hb'
  convert hb' using 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [PlanarChartTest.divHeight,pow_one,mul_comm,g]
  · ring

private def Controlled (b : Bool) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℂ) (hc : 4 < c.im),
      ‖∫ z : ℂ, (evaluationTest b c (by linarith)).field z*f z‖ ≤ C*(c.im+1)^2

private theorem Controlled.integrable {b : Bool} {f : ℂ → ℂ} (hf : Controlled b f)
    (c : ℂ) (hc : 4 < c.im) :
    Integrable (fun z => (evaluationTest b c (by linarith)).field z*f z) := by
  simpa only [mul_comm] using
    (evaluationTest b c (by linarith)).integrable_mul_planar f hf.1.continuousOn

private theorem Controlled.congr {b : Bool} {f g : ℂ → ℂ} (hf : Controlled b f)
    (he : ∀ z, f z = g z) : Controlled b g := (funext he) ▸ hf

private theorem Controlled.add {b : Bool} {f g : ℂ → ℂ}
    (hf : Controlled b f) (hg : Controlled b g) : Controlled b (fun z => f z+g z) := by
  obtain ⟨A,hA,hfa⟩ := hf.2
  obtain ⟨B,hB,hgb⟩ := hg.2
  refine ⟨hf.1.add hg.1,A+B,by positivity,?_⟩
  intro c hc
  simp_rw [mul_add]
  rw [integral_add (hf.integrable c hc) (hg.integrable c hc)]
  exact (norm_add_le _ _).trans ((add_le_add (hfa c hc) (hgb c hc)).trans_eq (by ring))

private theorem Controlled.scale {b : Bool} {f : ℂ → ℂ}
    (hf : Controlled b f) (a : ℂ) : Controlled b (fun z => a*f z) := by
  obtain ⟨A,hA,hfa⟩ := hf.2
  refine ⟨contDiffOn_const.mul hf.1,‖a‖*A,by positivity,?_⟩
  intro c hc
  have he : (fun z => (evaluationTest b c (by linarith)).field z*(a*f z)) =
      fun z => a*((evaluationTest b c (by linarith)).field z*f z) := by funext z; ring
  rw [he,integral_const_mul,norm_mul]
  exact (mul_le_mul_of_nonneg_left (hfa c hc) (norm_nonneg a)).trans_eq (by ring)

private theorem Controlled.sub {b : Bool} {f g : ℂ → ℂ}
    (hf : Controlled b f) (hg : Controlled b g) : Controlled b (fun z => f z-g z) :=
  (hf.add (hg.scale (-1))).congr (fun z => by ring)

private def remainder (q : XiZeroCopy) (i j : Fin 2) : ℂ → ℂ :=
  D4BMSquareCuspJets.gradientProductRemainder (D4BMGlobalAngularResponse.center q) i j ∘ angularCoordinates

private theorem remainder_controlled (q : XiZeroCopy) (b : Bool) (i j : Fin 2) :
    Controlled b (remainder q i j) := by
  have hsm : ContDiffOn ℝ ∞ (remainder q i j) {z : ℂ | 0 < z.im} :=
    (D4BMSquareCuspJets.gradientProductRemainder_jet_smooth
      (D4BMGlobalAngularResponse.center q) i j []).comp
      angularCoordinates.contDiff.contDiffOn (fun z hz => hz)
  obtain ⟨B,hB,hbound⟩ := D4BMSquareCuspJets.gradientProductRemainder_jet_weighted_bound
    (D4BMGlobalAngularResponse.center q) 0 i j [] ⟨1,by norm_num⟩
  have hb (z : ℂ) (hz : 1 ≤ z.im) : ‖remainder q i j z‖ ≤ B := by
    simpa only [remainder,Function.comp_apply,D4BMSquareCuspJets.coordinateJet,
      Complex.cpow_zero,one_mul] using hbound (angularCoordinates z) hz
  let M : ℝ := ∫ z : ℂ, ‖evaluationKernel b z‖
  have hM : 0 ≤ M := integral_nonneg (fun z => norm_nonneg _)
  refine ⟨hsm,B*M,by positivity,?_⟩
  intro c hc
  let g := evaluationTest b c (by linarith)
  have hkg : Integrable (fun z => ‖g.field z‖) :=
    (g.smooth.continuous.integrable_of_hasCompactSupport g.compact).norm
  have hdom : ∀ z : ℂ, ‖g.field z*remainder q i j z‖ ≤ B*‖g.field z‖ := by
    intro z
    by_cases hn : g.field z = 0
    · simp only [hn,zero_mul,norm_zero,mul_zero,le_refl]
    · have hs := translated_support b c (subset_tsupport g.field hn)
      rw [mem_closedBall,dist_eq_norm] at hs
      have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-c)).trans hs)).1
      simp only [Complex.sub_im] at hi
      rw [norm_mul,mul_comm B]
      exact mul_le_mul_of_nonneg_left (hb z (by linarith)) (norm_nonneg _)
  have he := norm_integral_le_of_norm_le (hkg.const_mul B) (Filter.Eventually.of_forall hdom)
  rw [integral_const_mul] at he
  have hm : (∫ z : ℂ, ‖g.field z‖) = M := by
    have ht := integral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun z : ℂ => ‖evaluationKernel b (z-c)‖) c
    simp only [add_sub_cancel_right] at ht
    exact ht.symm
  rw [hm] at he
  have hY : 1 ≤ (c.im+1)^2 := by nlinarith
  exact he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hY (mul_nonneg hB hM))

private def second (q : XiZeroCopy) (i j : Fin 2) (z : ℂ) : ℂ :=
  fderiv ℝ (fun w => fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) w (direction j))
    z (direction i)

private def connection (q : XiZeroCopy) (i : Fin 2) (z : ℂ) : ℂ :=
  (z.im:ℂ)⁻¹*fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) z (direction i)

private theorem second_controlled (q : XiZeroCopy) (b : Bool) (i j : Fin 2) :
    Controlled b (second q i j) := by
  have hsm := planar_derivative_contDiffOn
    (planar_derivative_contDiffOn (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn
      (direction j)) (direction i)
  obtain ⟨C,hC,hb⟩ := exists_second_test_bound b (direction i) (direction j)
  have hM : 0 ≤ responseMass q := integral_nonneg (fun z => norm_nonneg _)
  refine ⟨hsm,C*responseMass q,by positivity,?_⟩
  intro c hc
  exact (hb q c (by linarith)).trans_eq (by ring)

private theorem connection_controlled (q : XiZeroCopy) (b : Bool) (i : Fin 2) :
    Controlled b (connection q i) := by
  have hi : ContDiffOn ℝ ∞ (fun z : ℂ => (z.im:ℂ)⁻¹) {z : ℂ | 0 < z.im} :=
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffOn).fun_inv
      (fun z hz => Complex.ofReal_ne_zero.mpr (ne_of_gt hz))
  have hd := planar_derivative_contDiffOn (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn (direction i)
  obtain ⟨C,hC,hb⟩ := exists_connection_test_bound b (direction i)
  have hM : 0 ≤ responseMass q := integral_nonneg (fun z => norm_nonneg _)
  refine ⟨hi.mul hd,C*responseMass q,by positivity,?_⟩
  intro c hc
  have he := hb q c (by linarith)
  convert he using 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [connection,div_eq_mul_inv,mul_assoc]
  · ring

private def modelA (q : XiZeroCopy) (z : ℂ) : ℂ :=
  (remainder q 0 0 z-remainder q 1 1 z)/2+
    eigenvalue q*((second q 0 0 z-second q 1 1 z)/2-connection q 1 z)

private def modelB (q : XiZeroCopy) (z : ℂ) : ℂ :=
  remainder q 0 1 z+eigenvalue q*(second q 0 1 z+connection q 0 z)

private theorem modelA_controlled (q : XiZeroCopy) (b : Bool) : Controlled b (modelA q) := by
  have hR := ((remainder_controlled q b 0 0).sub (remainder_controlled q b 1 1)).scale (1/2)
  have hW := (((second_controlled q b 0 0).sub (second_controlled q b 1 1)).scale (1/2)).sub
    (connection_controlled q b 1)
  apply (hR.add (hW.scale (eigenvalue q))).congr
  intro z
  dsimp [modelA]
  ring

private theorem modelB_controlled (q : XiZeroCopy) (b : Bool) : Controlled b (modelB q) :=
  (remainder_controlled q b 0 1).add
    (((second_controlled q b 0 1).add (connection_controlled q b 0)).scale (eigenvalue q))

private theorem defectA_planar_high (q : XiZeroCopy) (z : ℂ) (hz : 3 < z.im) :
    defectA q (angularCoordinates z) = modelA q z := by
  rw [defectA_high q _ hz]
  simp only [correction_planar_second,correction_planar_first,modelA,second,connection,
    remainder,Function.comp_apply]
  rfl

private theorem defectB_planar_high (q : XiZeroCopy) (z : ℂ) (hz : 3 < z.im) :
    defectB q (angularCoordinates z) = modelB q z := by
  rw [defectB_high q _ hz]
  simp only [correction_planar_second,correction_planar_first,modelB,second,connection,
    remainder,Function.comp_apply]
  rfl

private theorem kernel_support_high (c z : ℂ) (hc : 4 < c.im) (hk : kernel (z-c) ≠ 0) :
    3 < z.im := by
  have hs := translated_kernel_support c (subset_tsupport _ hk)
  rw [mem_closedBall,dist_eq_norm] at hs
  have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-c)).trans hs)).1
  simp only [Complex.sub_im] at hi
  linarith

/-- The first actual holomorphic tensor polarization has polynomial cusp growth. -/
theorem holomorphicPolarization_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, 4 < c.im →
      ‖holomorphicPolarization q c‖ ≤ C*(c.im+1)^2 := by
  obtain ⟨C,hC,hbound⟩ :=
    ((modelA_controlled q false).sub ((modelB_controlled q false).scale Complex.I)).2
  refine ⟨C/Real.pi,div_nonneg hC Real.pi_pos.le,?_⟩
  intro c hc
  have he := holomorphicPolarization_evaluation q c (by linarith)
  have hb := hbound c hc
  have hid : (∫ z : ℂ, (evaluationTest false c (by linarith)).field z*
      (modelA q z-Complex.I*modelB q z)) =
      ∫ z : ℂ, (kernelTest c (by linarith)).field z*holomorphicPolarization q z := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hk : kernel (z-c) = 0
    · simp only [evaluationTest,evaluationKernel,Bool.false_eq_true,if_false,kernelTest,hk,zero_mul]
    · have hz := kernel_support_high c z hc hk
      simp only [evaluationTest,evaluationKernel,Bool.false_eq_true,if_false,kernelTest,
        holomorphicPolarization,Function.comp_apply,defectA_planar_high q z hz,defectB_planar_high q z hz]
  rw [hid,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hb
  calc
    ‖holomorphicPolarization q c‖ ≤ (C*(c.im+1)^2)/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hb])
    _ = C/Real.pi*(c.im+1)^2 := by ring

/-- The independent conjugate polarization has the same order of cusp growth, without reality. -/
theorem conjugatePolarization_growth (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, 4 < c.im →
      ‖conjugatePolarization q c‖ ≤ C*(c.im+1)^2 := by
  obtain ⟨C,hC,hbound⟩ :=
    ((modelA_controlled q true).add ((modelB_controlled q true).scale Complex.I)).2
  refine ⟨C/Real.pi,div_nonneg hC Real.pi_pos.le,?_⟩
  intro c hc
  have he := conjugatePolarization_evaluation q c (by linarith)
  have hb := hbound c hc
  have hid : conj (∫ z : ℂ, (evaluationTest true c (by linarith)).field z*
      (modelA q z+Complex.I*modelB q z)) =
      ∫ z : ℂ, (kernelTest c (by linarith)).field z*conjugatePolarization q z := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hk : kernel (z-c) = 0
    · simp [evaluationTest,evaluationKernel,kernelTest,hk]
    · have hz := kernel_support_high c z hc hk
      simp [evaluationTest,evaluationKernel,kernelTest,conjugatePolarization,
        defectA_planar_high q z hz,defectB_planar_high q z hz,sub_eq_add_neg]
  have hnorm := congrArg norm hid
  rw [Complex.norm_conj,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hnorm
  rw [hnorm] at hb
  calc
    ‖conjugatePolarization q c‖ ≤ (C*(c.im+1)^2)/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hb])
    _ = C/Real.pi*(c.im+1)^2 := by ring

end
end RHTower.D4BMAngularTwoCuspGrowth
