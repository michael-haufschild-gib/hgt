import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoCuspGrowth
import Mathlib.Data.Int.Interval
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAngularTwoWeight
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Cusp decay and closure of the actual angular tensor

Expanding evaluation disks transfer both correction Hessian derivatives to tests
of size inverse height to the fourth power. Exact modular periodization and the
native absolute mass give inverse-height decay. The complete gradient-product
remainder has the same decay, including both principal--tail cross terms.
Both original complex tensor polarizations are therefore weight-four cusp forms.
The vanishing of this cusp-form space closes the original angular tensor identity.
-/

open Complex MeasureTheory Set Filter Topology Metric UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff MatrixGroups ComplexConjugate
namespace RHTower.D4BMAngularTwoCuspDecay
open D4BMModularCore D4BMAngularTwoCuspNative D4BMAngularTwoCuspTest
open D4BMAngularTwoCuspGrowth D4BMAngularTwoTensor D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false

/-- Expanding cusp disks turn fourth-order test decay into first-order native decay. -/
theorem periodized_scaled_test_bound (g : PlanarChartTest) (c : ℂ) (hc : 4 < c.im)
    (hs : tsupport g.field ⊆ closedBall c (c.im/4)) (B : ℝ)
    (hB : ∀ w, ‖g.field w‖ ≤ B/c.im^(4 : ℕ)) (z : UpperHalfPlane) (hz : z ∈ fd) :
    ‖periodize (fun w : UpperHalfPlane => (w.im:ℂ)^(2 : ℕ)*g.field w) z‖ ≤ 16*B/c.im := by
  classical
  have hY : 0 < c.im := by linarith
  have hB0 : 0 ≤ B := by
    have hb := (norm_nonneg (g.field c)).trans (hB c)
    have he := (le_div_iff₀ (pow_pos hY 4)).mp hb
    simpa only [zero_mul] using he
  let f : UpperHalfPlane → ℂ := fun w => (w.im:ℂ)^(2 : ℕ)*g.field w
  have hsupport (w : UpperHalfPlane) (hw : g.field w ≠ 0) : ‖(w:ℂ)-c‖ ≤ c.im/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hs (subset_tsupport g.field hw)
  have hlow (w : UpperHalfPlane) (hw : w.im ≤ 2) : f w = 0 := by
    have hg : g.field w = 0 := by
      by_contra hn
      have hi := (Complex.abs_im_le_norm ((w:ℂ)-c)).trans (hsupport w hn)
      simp only [Complex.sub_im,UpperHalfPlane.coe_im] at hi
      have hl := (abs_le.mp hi).1
      linarith
    simp only [f,hg,mul_zero]
  have hbound (w : UpperHalfPlane) : ‖f w‖ ≤ 4*c.im^(2 : ℕ)*(B/c.im^(4 : ℕ)) := by
    by_cases hg : g.field w = 0
    · simp only [f,hg,mul_zero,norm_zero]
      positivity
    · have hi := (Complex.abs_im_le_norm ((w:ℂ)-c)).trans (hsupport w hg)
      simp only [Complex.sub_im,UpperHalfPlane.coe_im] at hi
      have hu := (abs_le.mp hi).2
      have hsquare : w.im^(2 : ℕ) ≤ 4*c.im^(2 : ℕ) := by nlinarith [w.im_pos]
      simp only [f,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos w.im_pos]
      exact mul_le_mul hsquare (hB w) (norm_nonneg _) (by positivity)
  let m : ℤ := ⌊c.re⌋
  let N : ℤ := ⌈c.im⌉
  let s := Finset.Icc (m-N-2) (m+N+2)
  have hm : (m:ℝ) ≤ c.re := Int.floor_le c.re
  have hm' : c.re < (m:ℝ)+1 := Int.lt_floor_add_one c.re
  have hN : c.im ≤ (N:ℝ) := Int.le_ceil c.im
  have hN' : (N:ℝ) < c.im+1 := Int.ceil_lt_add_one c.im
  have hN0 : 0 ≤ N := by exact_mod_cast (show (0:ℝ) ≤ (N:ℝ) by linarith)
  have hfinite (n : ℤ) (hn : n ∉ s) : f (T^n • z) = 0 := by
    have hcases : n < m-N-2 ∨ m+N+2 < n := by
      simpa only [s,Finset.mem_Icc,not_and_or,not_le] using hn
    have hg : g.field (T^n • z : UpperHalfPlane) = 0 := by
      by_contra hne
      have hr := (Complex.abs_re_le_norm (((T^n • z : UpperHalfPlane):ℂ)-c)).trans
        (hsupport (T^n • z) hne)
      simp only [Complex.sub_re,UpperHalfPlane.coe_re,ModularGroup.re_T_zpow_smul] at hr
      have hzr := abs_le.mp hz.2
      have hrr := abs_le.mp hr
      rcases hcases with hl | hu
      · have hl' : (n:ℝ) < (m:ℝ)-(N:ℝ)-2 := by exact_mod_cast hl
        linarith
      · have hu' : (m:ℝ)+(N:ℝ)+2 < (n:ℝ) := by exact_mod_cast hu
        linarith
    simp only [f,hg,mul_zero]
  have hcard : (s.card:ℝ) ≤ 4*c.im := by
    have he : (s.card:ℤ) = 2*N+5 := by
      dsimp only [s]
      rw [Int.card_Icc_of_le (a := m-N-2) (b := m+N+2) (by omega)]
      ring
    have he' : (s.card:ℝ) = 2*(N:ℝ)+5 := by exact_mod_cast he
    rw [he']
    linarith
  change ‖periodize f z‖ ≤ _
  rw [periodize_high_cusp f hlow z hz,tsum_eq_sum hfinite]
  calc
    ‖∑ n ∈ s, f (T^n • z)‖ ≤ ∑ n ∈ s, ‖f (T^n • z)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ s, 4*c.im^(2 : ℕ)*(B/c.im^(4 : ℕ)) := Finset.sum_le_sum (fun n _ => hbound (T^n • z))
    _ = (s.card:ℝ)*(4*c.im^(2 : ℕ)*(B/c.im^(4 : ℕ))) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (4*c.im)*(4*c.im^(2 : ℕ)*(B/c.im^(4 : ℕ))) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 16*B/c.im := by field_simp; ring

/-- The original finite-energy correction has a decaying pairing against expanding cusp tests. -/
theorem response_scaled_test_bound (q : XiZeroCopy) (g : PlanarChartTest) (c : ℂ)
    (hc : 4 < c.im) (hs : tsupport g.field ⊆ closedBall c (c.im/4))
    (B : ℝ) (hB : ∀ w, ‖g.field w‖ ≤ B/c.im^(4 : ℕ)) :
    ‖∫ w : ℂ, g.field w*D4BMAngularTwo.globalResponse q (ofComplex w)‖ ≤
      (16*B/c.im)*responseMass q := by
  rw [response_pairing_unfold]
  have hb := norm_integral_le_of_norm_le ((response_integrable q).norm.const_mul (16*B/c.im))
    (show ∀ᵐ z ∂measure,
      ‖periodize (fun w : UpperHalfPlane => (w.im:ℂ)^(2 : ℕ)*g.field w) z*D4BMAngularTwo.globalResponse q z‖ ≤
        (16*B/c.im)*‖D4BMAngularTwo.globalResponse q z‖ from by
      filter_upwards [ae_restrict_mem isClosed_fd.measurableSet] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (periodized_scaled_test_bound g c hc hs B hB z hz)
        (norm_nonneg _))
  simpa only [integral_const_mul,responseMass] using hb

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

/-- The evaluation density normalized by the area of its cusp-scale disk. -/
def scaledKernel (b : Bool) (c z : ℂ) : ℂ :=
  (c.im⁻¹:ℝ)^(2 : ℕ) • evaluationKernel b (c.im⁻¹ • (z-c))

theorem scaledKernel_smooth (b : Bool) (c : ℂ) : ContDiff ℝ ∞ (scaledKernel b c) :=
  ((evaluationKernel_smooth b).comp
    ((contDiff_id.sub contDiff_const).const_smul c.im⁻¹)).const_smul ((c.im⁻¹)^(2 : ℕ))

/-- The normalized kernel stays in a disk whose height is comparable to its center. -/
theorem scaledKernel_support (b : Bool) (c : ℂ) (hc : 0 < c.im) :
    tsupport (scaledKernel b c) ⊆ closedBall c (c.im/4) := by
  have hs : tsupport (scaledKernel b c) ⊆
      tsupport (fun z => evaluationKernel b (c.im⁻¹ • (z-c))) :=
    closure_mono (by
      intro z hz he
      apply hz
      change (c.im⁻¹:ℝ)^(2 : ℕ) • evaluationKernel b (c.im⁻¹ • (z-c)) = 0
      change evaluationKernel b (c.im⁻¹ • (z-c)) = 0 at he
      rw [he,smul_zero])
  intro z hz
  have h := evaluationKernel_support b
    (tsupport_comp_subset_preimage (evaluationKernel b)
      ((continuous_id.sub continuous_const).const_smul c.im⁻¹) (hs hz))
  simp only [mem_closedBall,dist_eq_norm,sub_zero,Pi.smul_apply,Pi.sub_apply,id_eq] at h
  simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)] at h
  rw [mem_closedBall,dist_eq_norm]
  have he : c.im*(c.im⁻¹*‖z-c‖) = ‖z-c‖ := by rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul]
  have hb := mul_le_mul_of_nonneg_left h hc.le
  rw [he] at hb
  linarith

/-- The cusp-scale evaluation density is a genuine compact planar chart test. -/
def scaledTest (b : Bool) (c : ℂ) (hc : 0 < c.im) : PlanarChartTest where
  field := scaledKernel b c
  smooth := scaledKernel_smooth b c
  compact := (isCompact_closedBall c (c.im/4)).of_isClosed_subset isClosed_closure
    (scaledKernel_support b c hc)
  support := by
    intro z hz
    have h := scaledKernel_support b c hc hz
    rw [mem_closedBall,dist_eq_norm] at h
    have hi := (Complex.abs_im_le_norm (z-c)).trans h
    rw [Complex.sub_im] at hi
    have hl := (abs_le.mp hi).1
    change 0 < z.im
    linarith

private theorem rescaled_derivative (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (a r : ℝ) (c v z : ℂ) :
    fderiv ℝ (fun w => a • f (r • (w-c))) z v =
      (a*r) • fderiv ℝ f (r • (z-c)) v := by
  have hi := ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const c).const_smul r
  have he := (((hf.differentiable (by simp) (r • (z-c))).hasFDerivAt).comp z hi).const_smul a
  change HasFDerivAt (fun w => a • f (r • (w-c))) _ z at he
  rw [he.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_smul]

private def kernelPartial (b : Bool) (v z : ℂ) : ℂ := fderiv ℝ (evaluationKernel b) z v

private theorem kernelPartial_smooth (b : Bool) (v : ℂ) : ContDiff ℝ ∞ (kernelPartial b v) :=
  ((evaluationKernel_smooth b).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem kernelPartial_compact (b : Bool) (v : ℂ) : HasCompactSupport (kernelPartial b v) :=
  (evaluationKernel_compact b).fderiv_apply ℝ v

private theorem scaledTest_partial (b : Bool) (c : ℂ) (hc : 0 < c.im) (v : ℂ) :
    ((scaledTest b c hc).derivative v).field = fun z =>
      (c.im⁻¹:ℝ)^(3 : ℕ) • kernelPartial b v (c.im⁻¹ • (z-c)) := by
  funext z
  change fderiv ℝ (fun w => (c.im⁻¹:ℝ)^(2 : ℕ) • evaluationKernel b (c.im⁻¹ • (w-c))) z v = _
  rw [rescaled_derivative _ (evaluationKernel_smooth b)]
  congr 1

private theorem scaledTest_second (b : Bool) (c : ℂ) (hc : 0 < c.im) (v w : ℂ) :
    (((scaledTest b c hc).derivative v).derivative w).field = fun z =>
      (c.im⁻¹:ℝ)^(4 : ℕ) • fderiv ℝ (kernelPartial b v) (c.im⁻¹ • (z-c)) w := by
  funext z
  change fderiv ℝ ((scaledTest b c hc).derivative v).field z w = _
  rw [scaledTest_partial,rescaled_derivative _ (kernelPartial_smooth b v)]
  congr 1

/-- The two actual correction derivatives decay after testing on expanding disks. -/
theorem exists_second_scaled_bound (b : Bool) (v w : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 4 < c.im),
      ‖∫ z : ℂ, (scaledTest b c (by linarith)).field z*
        fderiv ℝ (fun u => fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) u w) z v‖ ≤
          C/c.im*responseMass q := by
  have hsm : ContDiff ℝ ∞ (fun z => fderiv ℝ (kernelPartial b v) z w) :=
    ((kernelPartial_smooth b v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  obtain ⟨B,hB⟩ := ((kernelPartial_compact b v).fderiv_apply ℝ w).exists_bound_of_continuous hsm.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ (kernelPartial b v) 0 w)).trans (hB 0)
  refine ⟨16*B,by positivity,?_⟩
  intro q c hc
  have hY : 0 < c.im := by linarith
  let g := scaledTest b c hY
  have hs : tsupport ((g.derivative v).derivative w).field ⊆ closedBall c (c.im/4) :=
    (tsupport_fderiv_apply_subset ℝ w).trans
      ((tsupport_fderiv_apply_subset ℝ v).trans (scaledKernel_support b c hY))
  have hb (z : ℂ) : ‖((g.derivative v).derivative w).field z‖ ≤ B/c.im^(4 : ℕ) := by
    rw [show ((g.derivative v).derivative w).field = _ from scaledTest_second b c hY v w]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hY.le) 4)]
    calc
      _ ≤ (c.im⁻¹)^(4 : ℕ)*B := mul_le_mul_of_nonneg_left (hB _) (by positivity)
      _ = _ := by rw [inv_pow]; ring
  have ht := response_scaled_test_bound q ((g.derivative v).derivative w) c hc hs B hb
  have he := congrArg norm (mixed_green g (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v w)
  have ht' : ‖∫ z : ℂ, (D4BMAngularTwo.globalResponse q ∘ ofComplex) z*
      ((g.derivative v).derivative w).field z‖ ≤ 16*B/c.im*responseMass q := by
    simpa only [Function.comp_apply,mul_comm] using ht
  rw [he] at ht'
  simpa only [mul_comm,g] using ht'

private theorem divHeight_support (g : PlanarChartTest) :
    tsupport (g.divHeight 1).field ⊆ tsupport g.field :=
  closure_mono (by intro z hz he; exact hz (by simp [PlanarChartTest.divHeight,he]))

private theorem scaled_divHeight_derivative_bound (g : PlanarChartTest) (c : ℂ) (hc : 0 < c.im)
    (hs : tsupport g.field ⊆ closedBall c (c.im/4)) (v : ℂ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hgb : ∀ z, ‖g.field z‖ ≤ B/c.im^(2 : ℕ))
    (hgd : ∀ z, ‖(g.derivative v).field z‖ ≤ D/c.im^(3 : ℕ)) (z : ℂ) :
    ‖((g.divHeight 1).derivative v).field z‖ ≤ (2*D+4*B*‖(v.im:ℂ)‖)/c.im^(4 : ℕ) := by
  by_cases hz : z ∈ tsupport g.field
  · have hi := (Complex.abs_im_le_norm (z-c)).trans
      (show ‖z-c‖ ≤ c.im/4 from by simpa only [mem_closedBall,dist_eq_norm] using hs hz)
    simp only [Complex.sub_im] at hi
    have hy : c.im/2 ≤ z.im := by have := (abs_le.mp hi).1; linarith
    have hypos : 0 < z.im := by linarith
    have hy0 : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hypos.ne'
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
    have hInv : ‖(z.im:ℂ)⁻¹‖ ≤ 2/c.im := by
      rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hypos]
      have hh := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
        (by linarith : 0 < c.im/2) hy
      simpa only [one_div,inv_div] using hh
    have hsq : ‖(z.im:ℂ)⁻¹‖^(2 : ℕ) ≤ (2/c.im)^(2 : ℕ) := by
      nlinarith [norm_nonneg ((z.im:ℂ)⁻¹)]
    rw [he]
    calc
      _ ≤ ‖(g.derivative v).field z*(z.im:ℂ)⁻¹‖ +
          ‖g.field z*(-(z.im:ℂ)⁻¹^(2 : ℕ)*(v.im:ℂ))‖ := norm_add_le _ _
      _ ≤ (D/c.im^(3 : ℕ))*(2/c.im)+(B/c.im^(2 : ℕ))*((2/c.im)^(2 : ℕ)*‖(v.im:ℂ)‖) := by
        simp only [norm_mul,norm_neg,norm_pow]
        exact add_le_add
          (mul_le_mul (hgd z) hInv (norm_nonneg _) (by positivity))
          (mul_le_mul (hgb z) (mul_le_mul_of_nonneg_right hsq (norm_nonneg _))
            (by positivity) (by positivity))
      _ = _ := by ring
  · have hn : z ∉ tsupport ((g.divHeight 1).derivative v).field :=
      fun h => hz ((divHeight_support g) (tsupport_fderiv_apply_subset ℝ v h))
    rw [image_eq_zero_of_notMem_tsupport hn,norm_zero]
    positivity

/-- The original inverse-height connection term has the same decaying native bound. -/
theorem exists_connection_scaled_bound (b : Bool) (v : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : XiZeroCopy) (c : ℂ) (hc : 4 < c.im),
      ‖∫ z : ℂ, (scaledTest b c (by linarith)).field z/(z.im:ℂ)*
        fderiv ℝ (D4BMAngularTwo.globalResponse q ∘ ofComplex) z v‖ ≤
          C/c.im*responseMass q := by
  obtain ⟨B,hB⟩ := (evaluationKernel_compact b).exists_bound_of_continuous (evaluationKernel_smooth b).continuous
  obtain ⟨D,hD⟩ := (kernelPartial_compact b v).exists_bound_of_continuous (kernelPartial_smooth b v).continuous
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  refine ⟨16*(2*D+4*B*‖(v.im:ℂ)‖),by positivity,?_⟩
  intro q c hc
  have hY : 0 < c.im := by linarith
  let g := scaledTest b c hY
  have hs : tsupport ((g.divHeight 1).derivative v).field ⊆ closedBall c (c.im/4) :=
    (tsupport_fderiv_apply_subset ℝ v).trans ((divHeight_support g).trans (scaledKernel_support b c hY))
  have hgb (z : ℂ) : ‖g.field z‖ ≤ B/c.im^(2 : ℕ) := by
    change ‖(c.im⁻¹:ℝ)^(2 : ℕ) • evaluationKernel b (c.im⁻¹ • (z-c))‖ ≤ _
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (c.im⁻¹))]
    exact (mul_le_mul_of_nonneg_left (hB _) (sq_nonneg (c.im⁻¹))).trans_eq (by rw [inv_pow]; ring)
  have hgd (z : ℂ) : ‖(g.derivative v).field z‖ ≤ D/c.im^(3 : ℕ) := by
    rw [show (g.derivative v).field = _ from scaledTest_partial b c hY v]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hY.le) 3)]
    exact (mul_le_mul_of_nonneg_left (hD _) (by positivity)).trans_eq (by rw [inv_pow]; ring)
  have hb := response_scaled_test_bound q ((g.divHeight 1).derivative v) c hc hs
    (2*D+4*B*‖(v.im:ℂ)‖) (scaled_divHeight_derivative_bound g c hY
      (scaledKernel_support b c hY) v B D hB0 hD0 hgb hgd)
  have he := congrArg norm (first_green (g.divHeight 1) (D4BMAngularTwo.globalResponse q ∘ ofComplex)
    (D4BMAngularTwo.globalResponse_smooth q).planar_contDiffOn v)
  simp only [norm_neg,Function.comp_apply] at he
  have hb' : ‖∫ z : ℂ, D4BMAngularTwo.globalResponse q (ofComplex z)*
      ((g.divHeight 1).derivative v).field z‖ ≤
        16*(2*D+4*B*‖(v.im:ℂ)‖)/c.im*responseMass q := by
    simpa only [mul_comm] using hb
  rw [he] at hb'
  convert hb' using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.divHeight,pow_one,mul_comm,g]

private theorem normalized_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) (hc : 0 < c.im) :
    (∫ z : ℂ, (c.im⁻¹:ℝ)^(2 : ℕ) • f (c.im⁻¹ • (z-c))) = ∫ z : ℂ, f z := by
  have ht := integral_add_right_eq_self (μ := (volume : Measure ℂ))
    (fun z : ℂ => (c.im⁻¹:ℝ)^(2 : ℕ) • f (c.im⁻¹ • (z-c))) c
  simp only [add_sub_cancel_right] at ht
  rw [← ht,integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume f hc.le,
    Complex.finrank_real_complex,smul_smul,← mul_pow,inv_mul_cancel₀ hc.ne',one_pow,one_smul]

/-- Expanding the evaluation disk does not change its absolute test mass. -/
theorem scaledTest_norm_integral (b : Bool) (c : ℂ) (hc : 0 < c.im) :
    (∫ z : ℂ, ‖(scaledTest b c hc).field z‖) = ∫ z : ℂ, ‖evaluationKernel b z‖ := by
  change (∫ z : ℂ, ‖(c.im⁻¹:ℝ)^(2 : ℕ) • evaluationKernel b (c.im⁻¹ • (z-c))‖) = _
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (c.im⁻¹))]
  exact normalized_integral (fun z => ‖evaluationKernel b z‖) c hc

/-- The normalized expanding test still recovers the exact holomorphic value. -/
theorem scaled_evaluation (F : ℂ → ℂ) (c : ℂ) (hc : 0 < c.im)
    (hF : DifferentiableOn ℂ F (ball c c.im)) :
    (∫ z : ℂ, (scaledTest false c hc).field z*F z) = (Real.pi:ℂ)*F c := by
  have hh : DifferentiableOn ℂ (fun w : ℂ => F (c.im • w+c)) (ball 0 1) := by
    intro w hw
    have hm : c.im • w+c ∈ ball c c.im := by
      simp only [mem_ball,dist_eq_norm,sub_zero] at hw
      simp only [mem_ball,dist_eq_norm,add_sub_cancel_right,norm_smul,
        Real.norm_eq_abs,abs_of_pos hc]
      nlinarith
    have hd : DifferentiableAt ℂ (fun w : ℂ => c.im • w+c) w := by
      simpa only [Complex.real_smul,id_eq] using (differentiableAt_id.const_mul (c.im:ℂ)).add_const c
    exact ((hF.differentiableAt (isOpen_ball.mem_nhds hm)).comp w hd).differentiableWithinAt
  have he := kernel_evaluation (fun w : ℂ => F (c.im • w+c)) hh
  simp only [smul_zero,zero_add] at he
  have hn (z : ℂ) : c.im • (c.im⁻¹ • (z-c))+c = z := by
    rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul,sub_add_cancel]
  have hi := normalized_integral (fun w : ℂ => kernel w*F (c.im • w+c)) c hc
  simp only [hn] at hi
  calc
    _ = ∫ z : ℂ, (c.im⁻¹:ℝ)^(2 : ℕ) • (kernel (c.im⁻¹ • (z-c))*F z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      change ((c.im⁻¹:ℝ)^(2 : ℕ) • kernel (c.im⁻¹ • (z-c)))*F z = _
      exact smul_mul_assoc _ _ _
    _ = _ := hi.trans he

private theorem expanding_ball_positive (c : ℂ) :
    ball c c.im ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  rw [mem_ball,dist_eq_norm] at hz
  have hi := (Complex.abs_im_le_norm (z-c)).trans_lt hz
  rw [Complex.sub_im] at hi
  have hl := (abs_lt.mp hi).1
  change 0 < z.im
  linarith

theorem holomorphicPolarization_scaled_evaluation (q : XiZeroCopy) (c : ℂ) (hc : 0 < c.im) :
    (∫ z : ℂ, (scaledTest false c hc).field z*D4BMAngularTwoTensor.holomorphicPolarization q z) =
      (Real.pi:ℂ)*D4BMAngularTwoTensor.holomorphicPolarization q c := by
  apply scaled_evaluation
  intro z hz
  exact (D4BMAngularTwoTensor.holomorphicPolarization_differentiableAt q z
    (expanding_ball_positive c hz)).differentiableWithinAt

theorem conjugatePolarization_scaled_evaluation (q : XiZeroCopy) (c : ℂ) (hc : 0 < c.im) :
    (∫ z : ℂ, (scaledTest false c hc).field z*D4BMAngularTwoTensor.conjugatePolarization q z) =
      (Real.pi:ℂ)*D4BMAngularTwoTensor.conjugatePolarization q c := by
  apply scaled_evaluation
  intro z hz
  exact (D4BMAngularTwoTensor.conjugatePolarization_differentiableAt q z
    (expanding_ball_positive c hz)).differentiableWithinAt
private def Controlled (b : Bool) (f : ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ℂ) (hc : 4 < c.im),
      ‖∫ z : ℂ, (scaledTest b c (by linarith)).field z*f z‖ ≤ C/c.im

private theorem Controlled.integrable {b : Bool} {f : ℂ → ℂ} (hf : Controlled b f)
    (c : ℂ) (hc : 4 < c.im) :
    Integrable (fun z => (scaledTest b c (by linarith)).field z*f z) := by
  simpa only [mul_comm] using
    (scaledTest b c (by linarith)).integrable_mul_planar f hf.1.continuousOn

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
  have he : (fun z => (scaledTest b c (by linarith)).field z*(a*f z)) =
      fun z => a*((scaledTest b c (by linarith)).field z*f z) := by funext z; ring
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
    (D4BMGlobalAngularResponse.center q) 1 i j [] ⟨1,by norm_num⟩
  have hb (z : ℂ) (hz : 1 ≤ z.im) : z.im*‖remainder q i j z‖ ≤ B := by
    have he := hbound (angularCoordinates z) hz
    change ‖(z.im:ℂ)^(1:ℂ)*remainder q i j z‖ ≤ B at he
    simpa only [Complex.cpow_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < z.im)] using he
  let M : ℝ := ∫ z : ℂ, ‖evaluationKernel b z‖
  have hM : 0 ≤ M := integral_nonneg (fun z => norm_nonneg _)
  refine ⟨hsm,2*B*M,by positivity,?_⟩
  intro c hc
  have hY : 0 < c.im := by linarith
  let g := scaledTest b c hY
  have hkg : Integrable (fun z => ‖g.field z‖) :=
    (g.smooth.continuous.integrable_of_hasCompactSupport g.compact).norm
  have hdom : ∀ z : ℂ, ‖g.field z*remainder q i j z‖ ≤ (2*B/c.im)*‖g.field z‖ := by
    intro z
    by_cases hn : g.field z = 0
    · simp only [hn,zero_mul,norm_zero,mul_zero,le_refl]
    · have hs := scaledKernel_support b c hY (subset_tsupport g.field hn)
      rw [mem_closedBall,dist_eq_norm] at hs
      have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-c)).trans hs)).1
      simp only [Complex.sub_im] at hi
      have hrem : ‖remainder q i j z‖ ≤ 2*B/c.im := by
        apply (le_div_iff₀ hY).mpr
        have ht := hb z (by linarith)
        nlinarith [norm_nonneg (remainder q i j z)]
      rw [norm_mul,mul_comm (2*B/c.im)]
      exact mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
  have he := norm_integral_le_of_norm_le (hkg.const_mul (2*B/c.im)) (Filter.Eventually.of_forall hdom)
  rw [integral_const_mul,show (∫ z : ℂ, ‖g.field z‖) = M from scaledTest_norm_integral b c hY] at he
  exact he.trans_eq (by ring)

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
  obtain ⟨C,hC,hb⟩ := exists_second_scaled_bound b (direction i) (direction j)
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
  obtain ⟨C,hC,hb⟩ := exists_connection_scaled_bound b (direction i)
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


private theorem scaled_support_high (c z : ℂ) (hc : 4 < c.im)
    (hk : (scaledTest false c (by linarith)).field z ≠ 0) : 3 < z.im := by
  have hs := scaledKernel_support false c (by linarith) (subset_tsupport _ hk)
  rw [mem_closedBall,dist_eq_norm] at hs
  have hi := (abs_le.mp ((Complex.abs_im_le_norm (z-c)).trans hs)).1
  simp only [Complex.sub_im] at hi
  linarith

/-- The first original holomorphic tensor polarization decays uniformly as inverse cusp height. -/
theorem holomorphicPolarization_decay (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, 4 < c.im → ‖holomorphicPolarization q c‖ ≤ C/c.im := by
  obtain ⟨C,hC,hbound⟩ :=
    ((modelA_controlled q false).sub ((modelB_controlled q false).scale Complex.I)).2
  refine ⟨C/Real.pi,div_nonneg hC Real.pi_pos.le,?_⟩
  intro c hc
  have he := holomorphicPolarization_scaled_evaluation q c (by linarith)
  have hb := hbound c hc
  have hid : (∫ z : ℂ, (scaledTest false c (by linarith)).field z*
      (modelA q z-Complex.I*modelB q z)) =
      ∫ z : ℂ, (scaledTest false c (by linarith)).field z*holomorphicPolarization q z := by
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hk : (scaledTest false c (by linarith)).field z = 0
    · simp only [hk,zero_mul]
    · have hz := scaled_support_high c z hc hk
      simp only [holomorphicPolarization,Function.comp_apply,
        defectA_planar_high q z hz,defectB_planar_high q z hz]
  rw [hid,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hb
  calc
    ‖holomorphicPolarization q c‖ ≤ (C/c.im)/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hb])
    _ = (C/Real.pi)/c.im := by ring

/-- The independent conjugate polarization has the same decay, without any reality premise. -/
theorem conjugatePolarization_decay (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, 4 < c.im → ‖conjugatePolarization q c‖ ≤ C/c.im := by
  obtain ⟨C,hC,hbound⟩ :=
    ((modelA_controlled q true).add ((modelB_controlled q true).scale Complex.I)).2
  refine ⟨C/Real.pi,div_nonneg hC Real.pi_pos.le,?_⟩
  intro c hc
  have he := conjugatePolarization_scaled_evaluation q c (by linarith)
  have hb := hbound c hc
  have hconj (z : ℂ) : conj ((scaledTest true c (by linarith)).field z) =
      (scaledTest false c (by linarith)).field z := by
    simp [scaledTest,scaledKernel,evaluationKernel]
  have hid : conj (∫ z : ℂ, (scaledTest true c (by linarith)).field z*
      (modelA q z+Complex.I*modelB q z)) =
      ∫ z : ℂ, (scaledTest false c (by linarith)).field z*conjugatePolarization q z := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [map_mul,hconj]
    by_cases hk : (scaledTest false c (by linarith)).field z = 0
    · simp only [hk,zero_mul]
    · have hz := scaled_support_high c z hc hk
      simp [conjugatePolarization,defectA_planar_high q z hz,defectB_planar_high q z hz,
        sub_eq_add_neg]
  have hnorm := congrArg norm hid
  rw [Complex.norm_conj,he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos] at hnorm
  rw [hnorm] at hb
  calc
    ‖conjugatePolarization q c‖ ≤ (C/c.im)/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith [hb])
    _ = (C/Real.pi)/c.im := by ring

open scoped Manifold ModularForm
open CongruenceSubgroup

private def tensorPolarization (b : Bool) (q : XiZeroCopy) (z : ℂ) : ℂ :=
  if b then conjugatePolarization q z else holomorphicPolarization q z

private theorem tensorPolarization_decay (b : Bool) (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℂ, 4 < c.im → ‖tensorPolarization b q c‖ ≤ C/c.im := by
  cases b
  · exact holomorphicPolarization_decay q
  · exact conjugatePolarization_decay q

private theorem tensorPolarization_zero_at_cusp (b : Bool) (q : XiZeroCopy) :
    IsZeroAtImInfty (fun z : UpperHalfPlane => tensorPolarization b q z) := by
  obtain ⟨C,hC,hbound⟩ := tensorPolarization_decay b q
  apply isZeroAtImInfty_iff.mpr
  intro ε hε
  refine ⟨max 5 (C/ε),?_⟩
  intro z hz
  have hz5 : 5 ≤ z.im := (le_max_left _ _).trans hz
  have hzC : C/ε ≤ z.im := (le_max_right _ _).trans hz
  have he : C/z.im ≤ ε := by
    apply (div_le_iff₀ z.im_pos).mpr
    have hh := (div_le_iff₀ hε).mp hzC
    nlinarith
  exact (hbound z (by simpa only [coe_im] using (show 4 < z.im by linarith))).trans he

private theorem tensorPolarization_slash (b : Bool) (q : XiZeroCopy) (A : SL(2, ℤ)) :
    (fun z : UpperHalfPlane => tensorPolarization b q z) ∣[(4:ℤ)] A =
      fun z : UpperHalfPlane => tensorPolarization b q z := by
  funext z
  apply (ModularForm.slash_action_eq'_iff 4 _ A z).mpr
  cases b
  · simpa only [tensorPolarization,Bool.false_eq_true,if_false,zpow_ofNat] using
      D4BMAngularTwoWeight.holomorphicPolarization_weight_four q A z
  · simpa only [tensorPolarization,if_true,zpow_ofNat] using
      D4BMAngularTwoWeight.conjugatePolarization_weight_four q A z

private theorem tensorPolarization_holo (b : Bool) (q : XiZeroCopy) :
    MDiff (fun z : UpperHalfPlane => tensorPolarization b q z) := by
  rw [mdifferentiable_iff]
  intro z hz
  have hf : DifferentiableAt ℂ (tensorPolarization b q) z := by
    cases b
    · exact holomorphicPolarization_differentiableAt q z hz
    · exact conjugatePolarization_differentiableAt q z hz
  refine hf.differentiableWithinAt.congr (fun w hw => ?_) ?_
  · simp only [Function.comp_apply,ofComplex_apply_of_im_pos hw]
  · simp only [Function.comp_apply,ofComplex_apply_of_im_pos hz]

/-- Each original polarization is an actual weight-four cusp form. -/
private def tensorCuspForm (b : Bool) (q : XiZeroCopy) : CuspForm 𝒮ℒ 4 where
  toFun z := tensorPolarization b q z
  slash_action_eq' A hA := by
    obtain ⟨γ,rfl⟩ := hA
    exact tensorPolarization_slash b q γ
  holo' := tensorPolarization_holo b q
  zero_at_cusps' hc := by
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [tensorPolarization_slash]
    exact tensorPolarization_zero_at_cusp b q

private theorem tensorPolarization_zero (b : Bool) (q : XiZeroCopy) (z : UpperHalfPlane) :
    tensorPolarization b q z = 0 := by
  have h0 : tensorCuspForm b q = 0 :=
    rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) (tensorCuspForm b q)
  exact DFunLike.congr_fun h0 z

/-- Both original complex tensor components vanish for every actual Xi occurrence. -/
theorem actual_components_zero (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    defectA q z = 0 ∧ defectB q z = 0 := by
  let w : UpperHalfPlane := ⟨angularCoordinates.symm z,by
    change 0 < ((z 0:ℂ)+(z 1:ℂ)*Complex.I).im
    simpa using hz⟩
  have hm := tensorPolarization_zero false q w
  have hp := congrArg conj (tensorPolarization_zero true q w)
  have hm' : defectA q z-Complex.I*defectB q z = 0 := by
    simpa only [tensorPolarization,Bool.false_eq_true,if_false,holomorphicPolarization,
      w,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply] using hm
  have hp' : defectA q z+Complex.I*defectB q z = 0 := by
    simpa only [tensorPolarization,if_true,conjugatePolarization,
      w,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply,map_sub,map_mul,Complex.conj_conj,
      Complex.conj_I,map_zero,neg_mul,sub_neg_eq_add] using hp
  constructor
  · linear_combination (hm'+hp')/2
  · have hI : Complex.I*defectB q z = 0 := by linear_combination (hp'-hm')/2
    exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero

/-- The literal scalar and the constructed restored inverse satisfy the full angular tensor identity. -/
theorem actual_tensor_zero (q : XiZeroCopy) (z : Fin 2 → ℝ) (hz : 0 < z 1) :
    defectTensor q z = 0 := by
  obtain ⟨hA,hB⟩ := actual_components_zero q z hz
  rw [defectTensor_components q z hz,hA,hB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end
end RHTower.D4BMAngularTwoCuspDecay
