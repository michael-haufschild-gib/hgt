import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoCuspTest
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPeriodization

/-!
# Native mass bounds for the actual inverse's cusp derivatives

The constructed finite-energy correction has finite native absolute mass.
Exact modular unfolding and high-cusp periodization bound every compact
fixed-radius test by three integer translates. Transferring derivatives onto
the fixed evaluation kernel gives uniform polynomial bounds for the actual
second derivatives and the inverse-height first derivatives of the correction.
No pointwise derivative-growth assumption is used.
-/

open Complex MeasureTheory Set Filter Topology Metric UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff MatrixGroups ENNReal
namespace RHTower.D4BMAngularTwoCuspNative
open D4BMModularCore D4BMAngularTwo D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- The constructed correction has finite native absolute mass. -/
theorem response_integrable (q : XiZeroCopy) : Integrable (D4BMAngularTwo.globalResponse q) measure := by
  have hm : MemLp (D4BMAngularTwo.globalResponse q) 2 measure :=
    (memLp_congr_ae (D4BMAngularTwo.globalResponse_native_ae q)).2
      (MeasureTheory.Lp.memLp (D4BMModularCore.embedding (D4BMAngularTwo.weakResponse q)))
  exact MemLp.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2) hm

def responseMass (q : XiZeroCopy) : ℝ := ∫ z : UpperHalfPlane, ‖D4BMAngularTwo.globalResponse q z‖ ∂measure

/-- A high-cusp compact test has only three possible integer translates, uniformly in its center. -/
theorem periodized_height_test_bound (g : PlanarChartTest) (c : ℂ) (hc : 3 < c.im)
    (hs : tsupport g.field ⊆ closedBall c (1/4)) (C : ℝ) (hC : ∀ w, ‖g.field w‖ ≤ C)
    (z : UpperHalfPlane) (hz : z ∈ fd) :
    ‖periodize (fun w : UpperHalfPlane => (w.im:ℂ)^(2 : ℕ)*g.field w) z‖ ≤
      3*(c.im+1)^(2 : ℕ)*C := by
  classical
  let f : UpperHalfPlane → ℂ := fun w => (w.im:ℂ)^(2 : ℕ)*g.field w
  have hC0 : 0 ≤ C := (norm_nonneg (g.field c)).trans (hC c)
  have hsupport (w : UpperHalfPlane) (hw : g.field w ≠ 0) : ‖(w:ℂ)-c‖ ≤ 1/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hs (subset_tsupport g.field hw)
  have hlow (w : UpperHalfPlane) (hw : w.im ≤ 2) : f w = 0 := by
    have hg : g.field w = 0 := by
      by_contra hn
      have hi := (Complex.abs_im_le_norm ((w:ℂ)-c)).trans (hsupport w hn)
      simp only [Complex.sub_im,UpperHalfPlane.coe_im] at hi
      have hl := (abs_le.mp hi).1
      linarith
    simp only [f,hg,mul_zero]
  have hbound (w : UpperHalfPlane) : ‖f w‖ ≤ (c.im+1)^(2 : ℕ)*C := by
    by_cases hg : g.field w = 0
    · simp only [f,hg,mul_zero,norm_zero]
      positivity
    · have hi := (Complex.abs_im_le_norm ((w:ℂ)-c)).trans (hsupport w hg)
      simp only [Complex.sub_im,UpperHalfPlane.coe_im] at hi
      have hu := (abs_le.mp hi).2
      have hsquare : w.im^(2 : ℕ) ≤ (c.im+1)^(2 : ℕ) := by nlinarith [w.im_pos]
      simp only [f,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos w.im_pos]
      exact mul_le_mul hsquare (hC w) (norm_nonneg _) (sq_nonneg _)
  let m : ℤ := ⌊c.re⌋
  let s : Finset ℤ := {m-1,m,m+1}
  have hm : (m:ℝ) ≤ c.re := Int.floor_le c.re
  have hm' : c.re < (m:ℝ)+1 := Int.lt_floor_add_one c.re
  have hfinite (n : ℤ) (hn : n ∉ s) : f (T^n • z) = 0 := by
    have hn' : n ≠ m-1 ∧ n ≠ m ∧ n ≠ m+1 := by simpa only [s,Finset.mem_insert,
      Finset.mem_singleton,not_or] using hn
    have hcases : n ≤ m-2 ∨ m+2 ≤ n := by omega
    have hg : g.field (T^n • z : UpperHalfPlane) = 0 := by
      by_contra hne
      have hr := (Complex.abs_re_le_norm (((T^n • z : UpperHalfPlane):ℂ)-c)).trans
        (hsupport (T^n • z) hne)
      simp only [Complex.sub_re,UpperHalfPlane.coe_re,ModularGroup.re_T_zpow_smul] at hr
      have hzr := abs_le.mp hz.2
      have hrr := abs_le.mp hr
      rcases hcases with hl | hu
      · have hl' : (n:ℝ) ≤ (m:ℝ)-2 := by exact_mod_cast hl
        linarith
      · have hu' : (m:ℝ)+2 ≤ (n:ℝ) := by exact_mod_cast hu
        linarith
    simp only [f,hg,mul_zero]
  change ‖periodize f z‖ ≤ _
  rw [periodize_high_cusp f hlow z hz,tsum_eq_sum hfinite]
  have hcard : s.card = 3 := by
    have h0 : m-1 ∉ ({m,m+1}:Finset ℤ) := by simp only [Finset.mem_insert,Finset.mem_singleton,not_or]; omega
    have h1 : m ∉ ({m+1}:Finset ℤ) := by simp only [Finset.mem_singleton]; omega
    simp only [s,Finset.card_insert_of_notMem h0,Finset.card_insert_of_notMem h1,Finset.card_singleton]
  calc
    ‖∑ n ∈ s, f (T^n • z)‖ ≤ ∑ n ∈ s, ‖f (T^n • z)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ s, (c.im+1)^(2 : ℕ)*C := Finset.sum_le_sum (fun n _ => hbound (T^n • z))
    _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul]; ring

/-- The exact flat chart pairing unfolds into the original native correction. -/
theorem response_pairing_unfold (q : XiZeroCopy) (g : PlanarChartTest) :
    (∫ w : ℂ, g.field w*D4BMAngularTwo.globalResponse q (ofComplex w)) =
      ∫ z : UpperHalfPlane,
        periodize (fun w : UpperHalfPlane => (w.im:ℂ)^(2 : ℕ)*g.field w) z*D4BMAngularTwo.globalResponse q z ∂measure := by
  let a := g.mulSmooth (fun w : ℂ => (w.im:ℂ)^(2 : ℕ))
    ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow 2)
  have hl : LocallyIntegrable (D4BMAngularTwo.globalResponse q) (volume : Measure UpperHalfPlane) :=
    (globalLift_locallyIntegrable (embedding (D4BMAngularTwo.weakResponse q))).congr (D4BMAngularTwo.globalResponse_ae_lift q).symm
  have he := compact_test_modular_pairing_unfold a.toChartTest (D4BMAngularTwo.globalResponse q) hl
    (D4BMAngularTwo.globalResponse_invariant q)
  have hp := integral_volume_height_sq_chart (fun w => g.field w*D4BMAngularTwo.globalResponse q (ofComplex w))
  have hz : (∫ w in {w : ℂ | 0 < w.im}, g.field w*D4BMAngularTwo.globalResponse q (ofComplex w)) =
      ∫ w : ℂ, g.field w*D4BMAngularTwo.globalResponse q (ofComplex w) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    have hn : w ∉ tsupport g.field := fun hg => hw (g.support hg)
    rw [image_eq_zero_of_notMem_tsupport hn,zero_mul]
  rw [hz] at hp
  calc
    _ = ∫ z : UpperHalfPlane, (z.im:ℂ)^(2 : ℕ)*(g.field z*D4BMAngularTwo.globalResponse q (ofComplex z)) := hp.symm
    _ = ∫ z : UpperHalfPlane, a.toChartTest.field z*D4BMAngularTwo.globalResponse q z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [a,PlanarChartTest.mulSmooth,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
        ofComplex_apply,coe_im]
      ring
    _ = _ := he.symm

/-- Every bounded fixed-radius cusp test has a uniform polynomial pairing bound against the actual correction. -/
theorem response_test_pairing_bound (q : XiZeroCopy) (g : PlanarChartTest) (c : ℂ) (hc : 3 < c.im)
    (hs : tsupport g.field ⊆ closedBall c (1/4)) (C : ℝ) (hC : ∀ w, ‖g.field w‖ ≤ C) :
    ‖∫ w : ℂ, g.field w*D4BMAngularTwo.globalResponse q (ofComplex w)‖ ≤
      (3*(c.im+1)^(2 : ℕ)*C)*responseMass q := by
  rw [response_pairing_unfold]
  have hb := norm_integral_le_of_norm_le ((response_integrable q).norm.const_mul (3*(c.im+1)^(2 : ℕ)*C))
    (show ∀ᵐ z ∂measure,
      ‖periodize (fun w : UpperHalfPlane => (w.im:ℂ)^(2 : ℕ)*g.field w) z*D4BMAngularTwo.globalResponse q z‖ ≤
        (3*(c.im+1)^(2 : ℕ)*C)*‖D4BMAngularTwo.globalResponse q z‖ from by
      filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (periodized_height_test_bound g c hc hs C hC z hz)
        (norm_nonneg _))
  simpa only [integral_const_mul,responseMass] using hb

open D4BMAngularTwoCuspTest

/-- The same fixed evaluation test in the high cusp. -/
def highKernelTest (c : ℂ) (hc : 3 < c.im) : PlanarChartTest :=
  kernelTest c (by linarith)

private theorem translated_derivative (k : ℂ → ℂ) (hk : ContDiff ℝ ∞ k) (c v z : ℂ) :
    fderiv ℝ (fun w => k (w-c)) z v = fderiv ℝ k (z-c) v := by
  have he := ((hk.differentiable (by simp) (z-c)).hasFDerivAt).comp z
    ((hasFDerivAt_id z).sub_const c)
  change fderiv ℝ (k ∘ fun x => id x-c) z v = _
  rw [he.fderiv,ContinuousLinearMap.comp_apply]
  rfl

private def kernelDerivative (v z : ℂ) : ℂ := fderiv ℝ kernel z v

private theorem kernelDerivative_smooth (v : ℂ) : ContDiff ℝ ∞ (kernelDerivative v) :=
  (kernel_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem kernelDerivative_compact (v : ℂ) : HasCompactSupport (kernelDerivative v) :=
  kernel_compact.fderiv_apply ℝ v

private theorem first_field_eq (c : ℂ) (hc : 3 < c.im) (v : ℂ) :
    ((highKernelTest c hc).derivative v).field = fun z => kernelDerivative v (z-c) := by
  funext z
  exact translated_derivative kernel kernel_smooth c v z

/-- The actual correction obeys a uniform polynomial bound against every translated evaluation kernel. -/
theorem exists_kernel_pairing_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (highKernelTest c hc).field z*D4BMAngularTwo.globalResponse q (ofComplex z)‖ ≤
        C*(c.im+1)^(2 : ℕ)*responseMass q := by
  obtain ⟨B,hB⟩ := kernel_compact.exists_bound_of_continuous kernel_smooth.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (kernel 0)).trans (hB 0)
  refine ⟨3*B,by positivity,?_⟩
  intro q c hc
  have he := response_test_pairing_bound q (highKernelTest c hc) c hc
    (translated_kernel_support c) B (fun w => hB (w-c))
  convert he using 1; ring

/-- The same uniform control holds after transferring either first coordinate derivative. -/
theorem exists_kernel_first_pairing_bound (v : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, ((highKernelTest c hc).derivative v).field z*
        D4BMAngularTwo.globalResponse q (ofComplex z)‖ ≤ C*(c.im+1)^(2 : ℕ)*responseMass q := by
  obtain ⟨B,hB⟩ := (kernelDerivative_compact v).exists_bound_of_continuous
    (kernelDerivative_smooth v).continuous
  have hB0 : 0 ≤ B := (norm_nonneg (kernelDerivative v 0)).trans (hB 0)
  refine ⟨3*B,by positivity,?_⟩
  intro q c hc
  have hs : tsupport ((highKernelTest c hc).derivative v).field ⊆ closedBall c (1/4) :=
    (tsupport_fderiv_apply_subset ℝ v).trans (translated_kernel_support c)
  have hb (z : ℂ) : ‖((highKernelTest c hc).derivative v).field z‖ ≤ B := by
    rw [first_field_eq]
    exact hB (z-c)
  have he := response_test_pairing_bound q _ c hc hs B hb
  convert he using 1; ring

/-- Both transferred derivatives have one bound independent of cusp center and Xi occurrence. -/
theorem exists_kernel_second_pairing_bound (v w : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (((highKernelTest c hc).derivative v).derivative w).field z*
        D4BMAngularTwo.globalResponse q (ofComplex z)‖ ≤ C*(c.im+1)^(2 : ℕ)*responseMass q := by
  have hsm : ContDiff ℝ ∞ (fun z => fderiv ℝ (kernelDerivative v) z w) :=
    ((kernelDerivative_smooth v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcp := (kernelDerivative_compact v).fderiv_apply ℝ w
  obtain ⟨B,hB⟩ := hcp.exists_bound_of_continuous hsm.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ (kernelDerivative v) 0 w)).trans (hB 0)
  refine ⟨3*B,by positivity,?_⟩
  intro q c hc
  have hs : tsupport (((highKernelTest c hc).derivative v).derivative w).field ⊆
      closedBall c (1/4) :=
    (tsupport_fderiv_apply_subset ℝ w).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans (translated_kernel_support c))
  have hb (z : ℂ) : ‖(((highKernelTest c hc).derivative v).derivative w).field z‖ ≤ B := by
    change ‖fderiv ℝ ((highKernelTest c hc).derivative v).field z w‖ ≤ B
    rw [first_field_eq,translated_derivative (kernelDerivative v) (kernelDerivative_smooth v)]
    exact hB (z-c)
  have he := response_test_pairing_bound q _ c hc hs B hb
  convert he using 1; ring

/-- Two compact integrations by parts retain the order of arbitrary coordinate directions. -/
theorem mixed_green (g : PlanarChartTest) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) (v w : ℂ) :
    (∫ z : ℂ, f z*((g.derivative v).derivative w).field z) =
      ∫ z : ℂ, fderiv ℝ (fun u => fderiv ℝ f u w) z v*g.field z := by
  have hd := planar_derivative_contDiffOn hf w
  have hdd := planar_derivative_contDiffOn hd v
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((g.derivative v).integrable_mul_planar _ hd.continuousOn)
    (((g.derivative v).derivative w).integrable_mul_planar _ hf.continuousOn)
    ((g.derivative v).integrable_mul_planar _ hf.continuousOn)
    (fun z hz => (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
      ((g.derivative v).support hz))).differentiableAt (by simp))
    (fun z _ => (g.derivative v).smooth.differentiable (by simp) z)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (g.integrable_mul_planar _ hdd.continuousOn)
    ((g.derivative v).integrable_mul_planar _ hd.continuousOn)
    (g.integrable_mul_planar _ hd.continuousOn)
    (fun z hz => (hd.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
      (g.support hz))).differentiableAt (by simp))
    (fun z _ => g.smooth.differentiable (by simp) z)
  change (∫ z : ℂ, f z*fderiv ℝ (g.derivative v).field z w) = _ at h1 ⊢
  rw [h1]
  change (∫ z : ℂ, fderiv ℝ f z w*(g.derivative v).field z) = _ at h2
  rw [h2,neg_neg]

/-- The actual second derivatives of the retained correction satisfy the same polynomial tested bound. -/
theorem exists_response_second_test_bound (v w : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (highKernelTest c hc).field z*
        fderiv ℝ (fun u => fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) u w) z v‖ ≤
          C*(c.im+1)^(2 : ℕ)*responseMass q := by
  obtain ⟨C,hC,hb⟩ := exists_kernel_second_pairing_bound v w
  refine ⟨C,hC,?_⟩
  intro q c hc
  have he := mixed_green (highKernelTest c hc) (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v w
  have hnorm := congrArg norm he
  have hb' : ‖∫ z : ℂ, (D4BMAngularTwo.globalResponse q ∘ ofComplex) z*
      (((highKernelTest c hc).derivative v).derivative w).field z‖ ≤
      C*(c.im+1)^(2 : ℕ)*responseMass q := by
    simpa only [Function.comp_apply,mul_comm] using hb q c hc
  rw [hnorm] at hb'
  simpa only [mul_comm] using hb'


/-- One compact integration by parts for the actual planar derivative. -/
theorem first_green (g : PlanarChartTest) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) (v : ℂ) :
    (∫ z : ℂ, f z*(g.derivative v).field z) =
      -(∫ z : ℂ, fderiv ℝ f z v*g.field z) := by
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (g.integrable_mul_planar _ (planar_derivative_contDiffOn hf v).continuousOn)
    ((g.derivative v).integrable_mul_planar _ hf.continuousOn)
    (g.integrable_mul_planar _ hf.continuousOn)
    (fun z hz => (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
      (g.support hz))).differentiableAt (by simp))
    (fun z _ => g.smooth.differentiable (by simp) z)

private theorem divHeight_support (g : PlanarChartTest) :
    tsupport (g.divHeight 1).field ⊆ tsupport g.field :=
  closure_mono (by intro z hz he; exact hz (by simp [PlanarChartTest.divHeight,he]))

/-- Dividing by height retains a uniform first-test bound in the high cusp. -/
theorem divHeight_derivative_bound (g : PlanarChartTest) (c : ℂ) (hc : 3 < c.im)
    (hs : tsupport g.field ⊆ closedBall c (1/4)) (v : ℂ)
    (B D : ℝ) (hB : ∀ z, ‖g.field z‖ ≤ B)
    (hD : ∀ z, ‖(g.derivative v).field z‖ ≤ D) (z : ℂ) :
    ‖((g.divHeight 1).derivative v).field z‖ ≤ D+B*‖(v.im:ℂ)‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB z)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD z)
  by_cases hz : z ∈ tsupport g.field
  · have hi := (Complex.abs_im_le_norm (z-c)).trans
      (show ‖z-c‖ ≤ 1/4 from by simpa only [mem_closedBall,dist_eq_norm] using hs hz)
    simp only [Complex.sub_im] at hi
    have hy : 1 ≤ z.im := by have := (abs_le.mp hi).1; linarith
    have hy0 : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hY := Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
    have hI := (hasDerivAt_inv hy0).comp_hasFDerivAt z hY
    have hd := ((g.smooth.differentiable (by simp) z).hasFDerivAt.mul hI).fderiv
    change fderiv ℝ (fun w => g.field w*(w.im:ℂ)⁻¹) z = _ at hd
    have he : ((g.divHeight 1).derivative v).field z =
        (g.derivative v).field z*(z.im:ℂ)⁻¹ +
          g.field z*(-(z.im:ℂ)⁻¹^(2 : ℕ)*(v.im:ℂ)) := by
      change fderiv ℝ (fun w => g.field w/(w.im:ℂ)^(1 : ℕ)) z v = _
      simp only [pow_one,div_eq_mul_inv]
      rw [hd]
      simp only [add_apply,smul_apply,
        ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.imCLM_apply,
        smul_eq_mul,PlanarChartTest.derivative,Function.comp_apply,inv_pow]
      ring
    have hInv : ‖(z.im:ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < z.im)]
      exact inv_le_one_of_one_le₀ hy
    rw [he]
    calc
      _ ≤ ‖(g.derivative v).field z*(z.im:ℂ)⁻¹‖ +
          ‖g.field z*(-(z.im:ℂ)⁻¹^(2 : ℕ)*(v.im:ℂ))‖ := norm_add_le _ _
      _ ≤ D+B*‖(v.im:ℂ)‖ := by
        simp only [norm_mul,norm_neg,norm_pow]
        have hsq : ‖(z.im:ℂ)⁻¹‖^(2 : ℕ) ≤ 1 := by nlinarith [norm_nonneg ((z.im:ℂ)⁻¹)]
        have h0 := mul_le_mul (hD z) hInv (norm_nonneg _) hD0
        have h1 := mul_le_mul (hB z)
          (mul_le_mul_of_nonneg_right hsq (norm_nonneg (v.im:ℂ)))
          (by positivity) hB0
        simpa only [mul_one,one_mul] using add_le_add h0 h1
  · have hn : z ∉ tsupport ((g.divHeight 1).derivative v).field :=
      fun h => hz ((divHeight_support g) (tsupport_fderiv_apply_subset ℝ v h))
    rw [image_eq_zero_of_notMem_tsupport hn,norm_zero]
    positivity

/-- The connection term of the actual correction has the same polynomial tested bound. -/
theorem exists_response_connection_test_bound (v : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 3 < c.im),
      ‖∫ z : ℂ, (highKernelTest c hc).field z/(z.im:ℂ)*
        fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) z v‖ ≤
          C*(c.im+1)^(2 : ℕ)*responseMass q := by
  obtain ⟨B,hB⟩ := kernel_compact.exists_bound_of_continuous kernel_smooth.continuous
  obtain ⟨D,hD⟩ := (kernelDerivative_compact v).exists_bound_of_continuous
    (kernelDerivative_smooth v).continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨3*(D+B*‖(v.im:ℂ)‖),by positivity,?_⟩
  intro q c hc
  let g := highKernelTest c hc
  have hs : tsupport ((g.divHeight 1).derivative v).field ⊆ closedBall c (1/4) :=
    (tsupport_fderiv_apply_subset ℝ v).trans ((divHeight_support g).trans
      (translated_kernel_support c))
  have hd (z : ℂ) : ‖(g.derivative v).field z‖ ≤ D := by
    rw [show (g.derivative v).field = _ from first_field_eq c hc v]
    exact hD (z-c)
  have hb := response_test_pairing_bound q ((g.divHeight 1).derivative v) c hc hs
    (D+B*‖(v.im:ℂ)‖) (divHeight_derivative_bound g c hc
      (translated_kernel_support c) v B D (fun z => hB (z-c)) hd)
  have he := congrArg norm (first_green (g.divHeight 1)
    (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v)
  simp only [norm_neg,Function.comp_apply] at he
  have hb' : ‖∫ z : ℂ, D4BMAngularTwo.globalResponse q (ofComplex z)*
      ((g.divHeight 1).derivative v).field z‖ ≤
        3*(c.im+1)^(2 : ℕ)*(D+B*‖(v.im:ℂ)‖)*responseMass q := by
    simpa only [mul_comm] using hb
  rw [he] at hb'
  convert hb' using 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [PlanarChartTest.divHeight,pow_one,mul_comm,g]
  · ring

end
end RHTower.D4BMAngularTwoCuspNative
