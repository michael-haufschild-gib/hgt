import GaloisForLFunctions.RHTower.Suzuki.SuzukiSmallApertureClosedModulus

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem norm_suzukiLimitingLogFormEmbedding_eq_physical
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    ‖suzukiLimitingLogFormEmbedding q‖ =
      ‖ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q‖ := by
  unfold suzukiLimitingLogFormEmbedding
  convert norm_suzukiWeilIntervalFormEmbedding_eq_physical
    suzukiLimitingUnitAperture q using 1
  rfl

theorem inner_suzukiScaledRemainderOperator_realDomain_left_core_im_eq_zero
    (a : SuzukiPrimeFreeSmallAperture)
    (x : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (u : SuzukiRestrictedWeilCore 1) :
    (inner ℂ
      (suzukiScaledRemainderOperator a
        (suzukiLimitingLogFormEmbedding x))
      (suzukiLimitingCoreIntervalVector u)).im = 0 := by
  change x ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hx
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hx
  have hclosed : IsClosed {w :
      CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (inner ℂ
        (suzukiScaledRemainderOperator a
          (suzukiLimitingLogFormEmbedding w))
        (suzukiLimitingCoreIntervalVector u)).im = 0} := by
    apply isClosed_eq
    · exact Complex.continuous_im.comp
        (((suzukiScaledRemainderOperator a).continuous.comp
          suzukiLimitingLogFormEmbedding.continuous).inner
            (𝕜 := ℂ) continuous_const)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  change (inner ℂ
    (suzukiScaledRemainderOperator a
      (suzukiLimitingLogFormEmbedding
        (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
          (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t))))
    (suzukiLimitingCoreIntervalVector u)).im = 0
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  exact inner_suzukiScaledRemainderOperator_core_mixed_im_eq_zero a
    (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t) u

theorem inner_suzukiScaledRemainderOperator_realDomain_mixed_im_eq_zero
    (a : SuzukiPrimeFreeSmallAperture)
    (x y : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hx : x ∈ SuzukiLimitingRealFormDomain)
    (hy : y ∈ SuzukiLimitingRealFormDomain) :
    (inner ℂ
      (suzukiScaledRemainderOperator a
        (suzukiLimitingLogFormEmbedding x))
      (suzukiLimitingLogFormEmbedding y)).im = 0 := by
  change y ∈ closure
    (suzukiLimitingRealCoreSubmodule : Set
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture)) at hy
  obtain ⟨z, hzcore, hztend⟩ := mem_closure_iff_seq_limit.mp hy
  have hclosed : IsClosed {w :
      CCMArchimedeanFormDomain suzukiLimitingUnitAperture |
      (inner ℂ
        (suzukiScaledRemainderOperator a
          (suzukiLimitingLogFormEmbedding x))
        (suzukiLimitingLogFormEmbedding w)).im = 0} := by
    apply isClosed_eq
    · exact Complex.continuous_im.comp
        ((continuous_const : Continuous (fun _ :
          CCMArchimedeanFormDomain suzukiLimitingUnitAperture =>
            suzukiScaledRemainderOperator a
              (suzukiLimitingLogFormEmbedding x))).inner
          (𝕜 := ℂ) suzukiLimitingLogFormEmbedding.continuous)
    · fun_prop
  apply hclosed.mem_of_tendsto hztend
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨t, ht⟩ := hzcore n
  rw [← ht]
  change (inner ℂ
    (suzukiScaledRemainderOperator a
      (suzukiLimitingLogFormEmbedding x))
    (suzukiLimitingLogFormEmbedding
      (suzukiRestrictedWeilCoreCCMFormVector suzukiLimitingUnitAperture
        (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t)))).im = 0
  rw [← suzukiLimitingCoreIntervalVector_eq_limitingFormEmbedding]
  exact inner_suzukiScaledRemainderOperator_realDomain_left_core_im_eq_zero
    a x hx (suzukiRestrictedWeilRealTestToCore suzukiLimitingUnitAperture t)

theorem suzukiScaledRemainderClosedQuadratic_real_add_I_real
    (a : SuzukiPrimeFreeSmallAperture)
    (r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain) :
    suzukiScaledRemainderClosedQuadratic a
        (suzukiLimitingLogFormEmbedding (r + I • s)) =
      suzukiScaledRemainderClosedQuadratic a
          (suzukiLimitingLogFormEmbedding r) +
        suzukiScaledRemainderClosedQuadratic a
          (suzukiLimitingLogFormEmbedding s) := by
  let R := suzukiScaledRemainderOperator a
  let x := suzukiLimitingLogFormEmbedding r
  let y := suzukiLimitingLogFormEmbedding s
  have hxy : (inner ℂ (R x) y).im = 0 :=
    inner_suzukiScaledRemainderOperator_realDomain_mixed_im_eq_zero a r s hr hs
  have hyx : (inner ℂ (R y) x).im = 0 :=
    inner_suzukiScaledRemainderOperator_realDomain_mixed_im_eq_zero a s r hs hr
  unfold suzukiScaledRemainderClosedQuadratic
  rw [map_add, map_smul]
  change (inner ℂ (R (x + I • y)) (x + I • y)).re =
    (inner ℂ (R x) x).re + (inner ℂ (R y) y).re
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, Complex.add_re, Complex.mul_re,
    Complex.conj_I, Complex.I_re, Complex.I_im, zero_mul, one_mul, neg_mul]
  simp [Complex.mul_re, hxy, hyx]

/-- Exact finite energy splitting across the complete real/imaginary form decomposition. -/
theorem suzukiSmallScaledClosedEnergy_real_add_I_real
    (a : SuzukiPrimeFreeSmallAperture)
    (r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain) :
    suzukiSmallScaledClosedEnergy a (r + I • s) =
      suzukiSmallScaledClosedEnergy a r +
        suzukiSmallScaledClosedEnergy a s := by
  rw [suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder,
    suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder,
    suzukiSmallScaledClosedEnergy_eq_limiting_sub_remainder,
    norm_sq_suzukiLimitingLogFormEmbedding_real_add_I_real r s hr hs,
    suzukiLimitingLogClosedForm_real_add_I_real r s hr hs,
    suzukiScaledRemainderClosedQuadratic_real_add_I_real a r s hr hs]
  simp only [Complex.add_re]
  ring

/-- Actual finite-aperture sesquilinear form transported to the fixed unit form domain. -/
def suzukiSmallScaledClosedForm
    (a : SuzukiPrimeFreeSmallAperture)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) : ℂ :=
  ccmRestrictedWeilForm ⟨a.val, a.pos⟩
    (ccmArchimedeanUnitSmallFormEquiv a q)
    (ccmArchimedeanUnitSmallFormEquiv a r)

theorem suzukiSmallScaledClosedForm_self_re_eq_energy
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    (suzukiSmallScaledClosedForm a q q).re =
      suzukiSmallScaledClosedEnergy a q := by
  unfold suzukiSmallScaledClosedForm suzukiSmallScaledClosedEnergy
  exact ccmRestrictedWeilForm_self_re_eq_source _ _

theorem suzukiSmallScaledClosedForm_add_left
    (a : SuzukiPrimeFreeSmallAperture)
    (q r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledClosedForm a (q + r) s =
      suzukiSmallScaledClosedForm a q s +
        suzukiSmallScaledClosedForm a r s := by
  unfold suzukiSmallScaledClosedForm ccmRestrictedWeilForm
  simp only [map_add, inner_add_left]
  ring

theorem suzukiSmallScaledClosedForm_add_right
    (a : SuzukiPrimeFreeSmallAperture)
    (q r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledClosedForm a q (r + s) =
      suzukiSmallScaledClosedForm a q r +
        suzukiSmallScaledClosedForm a q s := by
  unfold suzukiSmallScaledClosedForm ccmRestrictedWeilForm
  simp only [map_add, inner_add_right]
  ring

theorem suzukiSmallScaledClosedForm_smul_left
    (a : SuzukiPrimeFreeSmallAperture)
    (c : ℂ) (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledClosedForm a (c • q) r =
      star c * suzukiSmallScaledClosedForm a q r := by
  unfold suzukiSmallScaledClosedForm ccmRestrictedWeilForm
  simp only [map_smul]
  have h₁ := inner_smul_left
    (ccmArchimedeanUnitSmallFormEquiv a q)
    (ccmArchimedeanUnitSmallFormEquiv a r) c
  have h₂ := inner_smul_left
    (ccmRestrictedWeilBoundedRemainder ⟨a.val, a.pos⟩
      (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a q)))
    (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a r)) c
  rw [h₁, h₂]
  rw [starRingEnd_apply]
  ring

theorem suzukiSmallScaledClosedForm_smul_right
    (a : SuzukiPrimeFreeSmallAperture)
    (c : ℂ) (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledClosedForm a q (c • r) =
      c * suzukiSmallScaledClosedForm a q r := by
  unfold suzukiSmallScaledClosedForm ccmRestrictedWeilForm
  simp only [map_smul]
  have h₁ := inner_smul_right
    (ccmArchimedeanUnitSmallFormEquiv a q)
    (ccmArchimedeanUnitSmallFormEquiv a r) c
  have h₂ := inner_smul_right
    (ccmRestrictedWeilBoundedRemainder ⟨a.val, a.pos⟩
      (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a q)))
    (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a r)) c
  rw [h₁, h₂]
  ring

theorem star_suzukiSmallScaledClosedForm_swap
    (a : SuzukiPrimeFreeSmallAperture)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    star (suzukiSmallScaledClosedForm a q r) =
      suzukiSmallScaledClosedForm a r q := by
  exact star_ccmRestrictedWeilForm_swap ⟨a.val, a.pos⟩
    (ccmArchimedeanUnitSmallFormEquiv a q)
    (ccmArchimedeanUnitSmallFormEquiv a r)

def suzukiSmallScaledGroundEnergy
    (a : SuzukiPrimeFreeSmallAperture) : ℝ :=
  ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩

theorem suzukiSmallScaledGroundEnergy_mul_formNorm_sq_le
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 ≤
      suzukiSmallScaledClosedEnergy a q := by
  have hfloor := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source
    ⟨a.val, a.pos⟩ (ccmArchimedeanUnitSmallFormEquiv a q)
  have hnorm :
      ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a q)‖ =
        ‖suzukiLimitingLogFormEmbedding q‖ := by
    rw [← ccmArchimedeanUnitSmallFormEquiv_embedding]
    rw [norm_suzukiLimitingLogFormEmbedding_eq_physical]
    exact (suzukiPhysicalUnitSmallEquiv a).norm_map _
  simpa [suzukiSmallScaledGroundEnergy, suzukiSmallScaledClosedEnergy,
    hnorm] using hfloor

/-- The actual finite bottom has a nonzero representative in the fixed complete form domain. -/
theorem exists_suzukiSmallScaledGroundFormState
    (a : SuzukiPrimeFreeSmallAperture) :
    ∃ q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      suzukiLimitingLogFormEmbedding q ≠ 0 ∧
      suzukiSmallScaledClosedEnergy a q =
        suzukiSmallScaledGroundEnergy a *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
  obtain ⟨u, hune, huground⟩ :=
    ccmRestrictedWeilSource_exists_groundFormState ⟨a.val, a.pos⟩
  let q := (ccmArchimedeanUnitSmallFormEquiv a).symm u
  have hqu : ccmArchimedeanUnitSmallFormEquiv a q = u :=
    (ccmArchimedeanUnitSmallFormEquiv a).apply_symm_apply u
  have hnorm :
      ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ u‖ =
        ‖suzukiLimitingLogFormEmbedding q‖ := by
    rw [← hqu, ← ccmArchimedeanUnitSmallFormEquiv_embedding]
    rw [norm_suzukiLimitingLogFormEmbedding_eq_physical]
    exact (suzukiPhysicalUnitSmallEquiv a).norm_map _
  have hqne : suzukiLimitingLogFormEmbedding q ≠ 0 := by
    intro hzero
    have hphyszero :
        ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q = 0 := by
      apply norm_eq_zero.mp
      rw [← norm_suzukiLimitingLogFormEmbedding_eq_physical, hzero, norm_zero]
    apply hune
    rw [← hqu, ← ccmArchimedeanUnitSmallFormEquiv_embedding, hphyszero, map_zero]
  refine ⟨q, hqne, ?_⟩
  change ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q) =
    ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ *
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2
  rw [hqu, huground, hnorm]

def suzukiSmallGroundShiftedRealBilinForm
    (a : SuzukiPrimeFreeSmallAperture) :
    LinearMap.BilinForm ℝ
      (CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :=
  LinearMap.mk₂ ℝ
    (fun q r => (suzukiSmallScaledClosedForm a q r).re -
      suzukiSmallScaledGroundEnergy a *
        (inner ℂ (suzukiLimitingLogFormEmbedding q)
          (suzukiLimitingLogFormEmbedding r)).re)
    (by
      intro q₁ q₂ r
      rw [suzukiSmallScaledClosedForm_add_left, map_add, inner_add_left]
      simp only [Complex.add_re]
      ring)
    (by
      intro c q r
      change (suzukiSmallScaledClosedForm a ((c : ℂ) • q) r).re -
          suzukiSmallScaledGroundEnergy a *
            (inner ℂ (suzukiLimitingLogFormEmbedding ((c : ℂ) • q))
              (suzukiLimitingLogFormEmbedding r)).re =
        c * ((suzukiSmallScaledClosedForm a q r).re -
          suzukiSmallScaledGroundEnergy a *
            (inner ℂ (suzukiLimitingLogFormEmbedding q)
              (suzukiLimitingLogFormEmbedding r)).re)
      rw [suzukiSmallScaledClosedForm_smul_left, map_smul, inner_smul_left]
      norm_num [Complex.mul_re]
      ring)
    (by
      intro q r₁ r₂
      rw [suzukiSmallScaledClosedForm_add_right, map_add, inner_add_right]
      simp only [Complex.add_re]
      ring)
    (by
      intro c q r
      change (suzukiSmallScaledClosedForm a q ((c : ℂ) • r)).re -
          suzukiSmallScaledGroundEnergy a *
            (inner ℂ (suzukiLimitingLogFormEmbedding q)
              (suzukiLimitingLogFormEmbedding ((c : ℂ) • r))).re =
        c * ((suzukiSmallScaledClosedForm a q r).re -
          suzukiSmallScaledGroundEnergy a *
            (inner ℂ (suzukiLimitingLogFormEmbedding q)
              (suzukiLimitingLogFormEmbedding r)).re)
      rw [suzukiSmallScaledClosedForm_smul_right, map_smul, inner_smul_right]
      norm_num [Complex.mul_re]
      ring)

theorem suzukiSmallGroundShiftedRealBilinForm_apply
    (a : SuzukiPrimeFreeSmallAperture)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiSmallGroundShiftedRealBilinForm a q r =
      (suzukiSmallScaledClosedForm a q r).re -
        suzukiSmallScaledGroundEnergy a *
          (inner ℂ (suzukiLimitingLogFormEmbedding q)
            (suzukiLimitingLogFormEmbedding r)).re := rfl

theorem suzukiSmallGroundShiftedRealBilinForm_nonneg
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    0 ≤ suzukiSmallGroundShiftedRealBilinForm a q q := by
  rw [suzukiSmallGroundShiftedRealBilinForm_apply,
    suzukiSmallScaledClosedForm_self_re_eq_energy,
    inner_self_eq_norm_sq_to_K]
  norm_num [Complex.mul_re, pow_two]
  simpa [pow_two] using suzukiSmallScaledGroundEnergy_mul_formNorm_sq_le a q

theorem suzukiSmallGroundShiftedRealBilinForm_isSymm
    (a : SuzukiPrimeFreeSmallAperture) :
    LinearMap.IsSymm (suzukiSmallGroundShiftedRealBilinForm a) := by
  apply LinearMap.IsSymm.mk
  intro q r
  simp only [RingHom.id_apply]
  rw [suzukiSmallGroundShiftedRealBilinForm_apply,
    suzukiSmallGroundShiftedRealBilinForm_apply]
  have hform := congrArg Complex.re
    (star_suzukiSmallScaledClosedForm_swap a q r)
  have hinner := congrArg Complex.re
    (inner_conj_symm (suzukiLimitingLogFormEmbedding r)
      (suzukiLimitingLogFormEmbedding q))
  simp only [Complex.star_def, Complex.conj_re] at hform hinner
  rw [hform, hinner]

theorem suzukiSmallGroundShiftedRealBilinForm_eq_zero_left
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∀ r, suzukiSmallGroundShiftedRealBilinForm a q r = 0 := by
  have hdiag : suzukiSmallGroundShiftedRealBilinForm a q q = 0 := by
    rw [suzukiSmallGroundShiftedRealBilinForm_apply,
      suzukiSmallScaledClosedForm_self_re_eq_energy,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    nlinarith
  have hker := ((suzukiSmallGroundShiftedRealBilinForm a).apply_apply_same_eq_zero_iff
    (suzukiSmallGroundShiftedRealBilinForm_nonneg a)
    (suzukiSmallGroundShiftedRealBilinForm_isSymm a)).mp hdiag
  intro r
  exact DFunLike.congr_fun (LinearMap.mem_ker.mp hker) r

theorem suzukiSmallGroundShiftedComplexForm_eq_zero_left
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∀ r, suzukiSmallScaledClosedForm a q r =
      (suzukiSmallScaledGroundEnergy a : ℂ) *
        inner ℂ (suzukiLimitingLogFormEmbedding q)
          (suzukiLimitingLogFormEmbedding r) := by
  intro r
  have hre := suzukiSmallGroundShiftedRealBilinForm_eq_zero_left a q hground r
  rw [suzukiSmallGroundShiftedRealBilinForm_apply] at hre
  have him := suzukiSmallGroundShiftedRealBilinForm_eq_zero_left
    a q hground (I • r)
  rw [suzukiSmallGroundShiftedRealBilinForm_apply,
    suzukiSmallScaledClosedForm_smul_right, map_smul,
    inner_smul_right] at him
  apply Complex.ext
  · norm_num [Complex.mul_re]
    nlinarith
  · norm_num [Complex.mul_re] at him ⊢
    nlinarith

theorem suzukiSmallGroundFormMinimizer_real_components_ground
    (a : SuzukiPrimeFreeSmallAperture)
    (q r s : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hr : r ∈ SuzukiLimitingRealFormDomain)
    (hs : s ∈ SuzukiLimitingRealFormDomain)
    (hq : q = r + I • s)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    (suzukiSmallScaledClosedEnergy a r =
        suzukiSmallScaledGroundEnergy a *
          ‖suzukiLimitingLogFormEmbedding r‖ ^ 2) ∧
      (suzukiSmallScaledClosedEnergy a s =
        suzukiSmallScaledGroundEnergy a *
          ‖suzukiLimitingLogFormEmbedding s‖ ^ 2) := by
  have hsum :
      suzukiSmallScaledClosedEnergy a r +
          suzukiSmallScaledClosedEnergy a s =
        suzukiSmallScaledGroundEnergy a *
          (‖suzukiLimitingLogFormEmbedding r‖ ^ 2 +
            ‖suzukiLimitingLogFormEmbedding s‖ ^ 2) := by
    rw [hq, suzukiSmallScaledClosedEnergy_real_add_I_real a r s hr hs,
      norm_sq_suzukiLimitingLogFormEmbedding_real_add_I_real r s hr hs] at hground
    exact hground
  have hrfloor := suzukiSmallScaledGroundEnergy_mul_formNorm_sq_le a r
  have hsfloor := suzukiSmallScaledGroundEnergy_mul_formNorm_sq_le a s
  constructor <;> nlinarith

/-- Strict finite modulus defect forces every real bottom minimizer to have one sign. -/
theorem suzukiSmallRealGroundMinimizer_positiveMass_mul_negativeMass_eq_zero
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    suzukiIntervalPositiveMass (suzukiLimitingLogFormEmbedding q) *
      suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) = 0 := by
  obtain ⟨w, _hwreal, hwrep, hwenergy⟩ :=
    exists_suzukiRealFormDomainModulus_with_finiteSignDefect a q hq
  have hfloor := suzukiSmallScaledGroundEnergy_mul_formNorm_sq_le a w
  rw [hwrep, norm_suzukiIntervalL2Modulus] at hfloor
  rw [hground] at hwenergy
  have hp := suzukiIntervalPositiveMass_nonneg
    (suzukiLimitingLogFormEmbedding q)
  have hn := suzukiIntervalNegativeMass_nonneg
    (suzukiLimitingLogFormEmbedding q)
  have hpn : 0 ≤ suzukiIntervalPositiveMass
      (suzukiLimitingLogFormEmbedding q) *
        suzukiIntervalNegativeMass (suzukiLimitingLogFormEmbedding q) :=
    mul_nonneg hp hn
  unfold suzukiFiniteSignDefectCoefficient at ha
  nlinarith

theorem suzukiSmallRealGroundMinimizer_fixedSign_ae
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).re ≤ 0) ∨
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        0 ≤ (suzukiLimitingLogFormEmbedding q x).re) := by
  have hprod :=
    suzukiSmallRealGroundMinimizer_positiveMass_mul_negativeMass_eq_zero
      a ha q hq hground
  rcases mul_eq_zero.mp hprod with hp | hn
  · exact Or.inl (ae_realPart_nonpos_of_suzukiIntervalPositiveMass_eq_zero hp)
  · exact Or.inr (ae_realPart_nonneg_of_suzukiIntervalNegativeMass_eq_zero hn)

theorem suzukiSmallRealGroundMinimizer_fixedComplexSign_ae
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ((∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).im = 0 ∧
          (suzukiLimitingLogFormEmbedding q x).re ≤ 0) ∨
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        (suzukiLimitingLogFormEmbedding q x).im = 0 ∧
          0 ≤ (suzukiLimitingLogFormEmbedding q x).re)) := by
  have him :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hq
  rcases suzukiSmallRealGroundMinimizer_fixedSign_ae
      a ha q hq hground with hnonpos | hnonneg
  · exact Or.inl (him.and hnonpos)
  · exact Or.inr (him.and hnonneg)

theorem suzukiSmallGroundFormMinimizer_sub_real_smul
    (a : SuzukiPrimeFreeSmallAperture)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hrground : suzukiSmallScaledClosedEnergy a r =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding r‖ ^ 2)
    (c : ℝ) :
    suzukiSmallScaledClosedEnergy a (r - c • q) =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding (r - c • q)‖ ^ 2 := by
  have hqzero :=
    suzukiSmallGroundShiftedRealBilinForm_eq_zero_left a q hqground
  have hrzero :=
    suzukiSmallGroundShiftedRealBilinForm_eq_zero_left a r hrground
  have hzero : suzukiSmallGroundShiftedRealBilinForm a
      (r - c • q) (r - c • q) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hrzero, hqzero, mul_zero, sub_zero]
  rw [suzukiSmallGroundShiftedRealBilinForm_apply,
    suzukiSmallScaledClosedForm_self_re_eq_energy,
    inner_self_eq_norm_sq_to_K] at hzero
  norm_num [Complex.mul_re, pow_two] at hzero
  simpa [pow_two] using sub_eq_zero.mp hzero

theorem suzukiSmallGroundFormMinimizer_neg
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    suzukiSmallScaledClosedEnergy a (-q) =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding (-q)‖ ^ 2 := by
  rw [← suzukiSmallScaledClosedForm_self_re_eq_energy,
    show -q = (-1 : ℂ) • q by simp,
    suzukiSmallScaledClosedForm_smul_left,
    suzukiSmallScaledClosedForm_smul_right]
  norm_num
  rw [suzukiSmallScaledClosedForm_self_re_eq_energy]
  exact hground

theorem not_orthogonal_nonzero_nonnegative_suzukiSmallRealGroundMinimizers
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hwreal : w ∈ SuzukiLimitingRealFormDomain)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hwground : suzukiSmallScaledClosedEnergy a w =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hwne : suzukiLimitingLogFormEmbedding w ≠ 0)
    (hqnonneg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ (suzukiLimitingLogFormEmbedding q x).re)
    (hwnonneg : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ (suzukiLimitingLogFormEmbedding w x).re)
    (horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0) : False := by
  let d := q - w
  have hdreal : d ∈ SuzukiLimitingRealFormDomain :=
    SuzukiLimitingRealFormDomain.sub_mem hqreal hwreal
  have hdground : suzukiSmallScaledClosedEnergy a d =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding d‖ ^ 2 := by
    have h := suzukiSmallGroundFormMinimizer_sub_real_smul
      a w q hwground hqground 1
    simpa only [one_smul] using h
  have hqimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hqreal
  have hwimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hwreal
  have hdimag :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hdreal
  have horthRev : inner ℂ (suzukiLimitingLogFormEmbedding w)
      (suzukiLimitingLogFormEmbedding q) = 0 := by
    rw [← inner_conj_symm]
    simp [horth]
  have hdembed : suzukiLimitingLogFormEmbedding d =
      suzukiLimitingLogFormEmbedding q -
        suzukiLimitingLogFormEmbedding w := by
    dsimp only [d]
    rw [map_sub]
  have hposOverlap : 0 < (inner ℂ (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding q)).re := by
    rw [hdembed, inner_sub_left, horthRev, sub_zero,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    exact hqne
  have hnegOverlap : (inner ℂ (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding w)).re < 0 := by
    rw [hdembed, inner_sub_left, horth, zero_sub,
      inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
    exact hwne
  rcases suzukiSmallRealGroundMinimizer_fixedSign_ae
      a ha d hdreal hdground with hdnonpos | hdnonneg
  · have hle := inner_re_nonpos_of_ae_real_nonpos_nonneg
      (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding q)
      hdimag hqimag hdnonpos hqnonneg
    linarith
  · have hge := inner_re_nonneg_of_ae_real_nonneg
      (suzukiLimitingLogFormEmbedding d)
      (suzukiLimitingLogFormEmbedding w)
      hdimag hwimag hdnonneg hwnonneg
    linarith

theorem exists_nonnegative_orientation_suzukiSmallRealGroundMinimizer
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0) :
    ∃ qpos : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      qpos ∈ SuzukiLimitingRealFormDomain ∧
      suzukiSmallScaledClosedEnergy a qpos =
        suzukiSmallScaledGroundEnergy a *
          ‖suzukiLimitingLogFormEmbedding qpos‖ ^ 2 ∧
      suzukiLimitingLogFormEmbedding qpos ≠ 0 ∧
      (∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
        0 ≤ (suzukiLimitingLogFormEmbedding qpos x).re) ∧
      (qpos = q ∨ qpos = -q) := by
  rcases suzukiSmallRealGroundMinimizer_fixedSign_ae
      a ha q hqreal hqground with hnonpos | hnonneg
  · refine ⟨-q, SuzukiLimitingRealFormDomain.neg_mem hqreal,
      suzukiSmallGroundFormMinimizer_neg a q hqground, ?_, ?_, Or.inr rfl⟩
    · simpa using hqne
    · rw [map_neg]
      filter_upwards [MeasureTheory.Lp.coeFn_neg
        (suzukiLimitingLogFormEmbedding q), hnonpos] with x hneg hx
      rw [hneg]
      simp
      exact hx
  · exact ⟨q, hqreal, hqground, hqne, hnonneg, Or.inl rfl⟩

theorem not_orthogonal_nonzero_suzukiSmallRealGroundMinimizers
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q w : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hwreal : w ∈ SuzukiLimitingRealFormDomain)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hwground : suzukiSmallScaledClosedEnergy a w =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hwne : suzukiLimitingLogFormEmbedding w ≠ 0)
    (horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0) : False := by
  obtain ⟨qpos, hqposReal, hqposGround, hqposNe, hqposNonneg, hqorient⟩ :=
    exists_nonnegative_orientation_suzukiSmallRealGroundMinimizer
      a ha q hqreal hqground hqne
  obtain ⟨wpos, hwposReal, hwposGround, hwposNe, hwposNonneg, hworient⟩ :=
    exists_nonnegative_orientation_suzukiSmallRealGroundMinimizer
      a ha w hwreal hwground hwne
  have horthPos : inner ℂ (suzukiLimitingLogFormEmbedding qpos)
      (suzukiLimitingLogFormEmbedding wpos) = 0 := by
    rcases hqorient with rfl | rfl <;>
      rcases hworient with rfl | rfl <;>
      simp [horth]
  exact not_orthogonal_nonzero_nonnegative_suzukiSmallRealGroundMinimizers
    a ha qpos wpos hqposReal hwposReal hqposGround hwposGround hqposNe hwposNe
      hqposNonneg hwposNonneg horthPos

/-- The actual finite real ground space is a single real line. -/
theorem exists_real_smul_eq_of_suzukiSmallRealGroundMinimizers
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hrreal : r ∈ SuzukiLimitingRealFormDomain)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hrground : suzukiSmallScaledClosedEnergy a r =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding r‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0) :
    ∃ c : ℝ, r = c • q := by
  let c : ℝ :=
    (inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding r)).re /
      ‖suzukiLimitingLogFormEmbedding q‖ ^ 2
  let w := r - c • q
  have hwreal : w ∈ SuzukiLimitingRealFormDomain :=
    SuzukiLimitingRealFormDomain.sub_mem hrreal
      (SuzukiLimitingRealFormDomain.smul_mem c hqreal)
  have hwground : suzukiSmallScaledClosedEnergy a w =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding w‖ ^ 2 :=
    suzukiSmallGroundFormMinimizer_sub_real_smul a q r hqground hrground c
  have hinnerReal :=
    inner_suzukiLimitingLogFormEmbedding_realDomain_mixed_im_eq_zero
      q r hqreal hrreal
  have hnormSqNe : ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hqne)
  have hwembed : suzukiLimitingLogFormEmbedding w =
      suzukiLimitingLogFormEmbedding r -
        (c : ℂ) • suzukiLimitingLogFormEmbedding q := by
    dsimp only [w]
    change suzukiLimitingLogFormEmbedding (r - (c : ℂ) • q) = _
    rw [map_sub, map_smul]
  have horth : inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding w) = 0 := by
    rw [hwembed, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    let z := inner ℂ (suzukiLimitingLogFormEmbedding q)
      (suzukiLimitingLogFormEmbedding r)
    let N := ‖suzukiLimitingLogFormEmbedding q‖ ^ 2
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa only [z, Complex.ofReal_im] using hinnerReal
    have hcN : c * N = z.re := by
      dsimp only [c, N, z]
      exact div_mul_cancel₀ _ hnormSqNe
    have hcastN : (‖suzukiLimitingLogFormEmbedding q‖ : ℂ) ^ 2 =
        (N : ℂ) := by
      dsimp only [N]
      push_cast
      rfl
    change z - (c : ℂ) *
      (‖suzukiLimitingLogFormEmbedding q‖ : ℂ) ^ 2 = 0
    rw [hcastN, hzreal, ← hcN]
    push_cast
    ring
  by_cases hwzero : suzukiLimitingLogFormEmbedding w = 0
  · have wz : w = 0 := suzukiLimitingLogFormEmbedding_injective
      (hwzero.trans (map_zero suzukiLimitingLogFormEmbedding).symm)
    refine ⟨c, ?_⟩
    exact sub_eq_zero.mp wz
  · exact (not_orthogonal_nonzero_suzukiSmallRealGroundMinimizers
      a ha q w hqreal hwreal hqground hwground hqne hwzero horth).elim

theorem exists_nonzero_suzukiSmallRealGroundMinimizer
    (a : SuzukiPrimeFreeSmallAperture) :
    ∃ q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture,
      q ∈ SuzukiLimitingRealFormDomain ∧
      suzukiLimitingLogFormEmbedding q ≠ 0 ∧
      suzukiSmallScaledClosedEnergy a q =
        suzukiSmallScaledGroundEnergy a *
          ‖suzukiLimitingLogFormEmbedding q‖ ^ 2 := by
  obtain ⟨p, hpne, hpground⟩ := exists_suzukiSmallScaledGroundFormState a
  obtain ⟨r, s, hrreal, hsreal, hpsplit⟩ :=
    exists_suzukiLimitingRealFormDomain_add_I_smul p
  obtain ⟨hrground, hsground⟩ :=
    suzukiSmallGroundFormMinimizer_real_components_ground
      a p r s hrreal hsreal hpsplit hpground
  have hpembed : suzukiLimitingLogFormEmbedding p =
      suzukiLimitingLogFormEmbedding r +
        I • suzukiLimitingLogFormEmbedding s := by
    rw [hpsplit, map_add, map_smul]
  by_cases hrzero : suzukiLimitingLogFormEmbedding r = 0
  · have hsne : suzukiLimitingLogFormEmbedding s ≠ 0 := by
      intro hszero
      apply hpne
      rw [hpembed, hrzero, hszero]
      simp
    exact ⟨s, hsreal, hsne, hsground⟩
  · exact ⟨r, hrreal, hrzero, hrground⟩

/-- Every actual finite closed-form bottom minimizer is a complex multiple of the real generator. -/
theorem exists_complex_smul_eq_of_suzukiSmallGroundMinimizers
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (q p : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hqreal : q ∈ SuzukiLimitingRealFormDomain)
    (hqground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2)
    (hqne : suzukiLimitingLogFormEmbedding q ≠ 0)
    (hpground : suzukiSmallScaledClosedEnergy a p =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2) :
    ∃ c : ℂ, p = c • q := by
  obtain ⟨r, s, hrreal, hsreal, hpsplit⟩ :=
    exists_suzukiLimitingRealFormDomain_add_I_smul p
  obtain ⟨hrground, hsground⟩ :=
    suzukiSmallGroundFormMinimizer_real_components_ground
      a p r s hrreal hsreal hpsplit hpground
  obtain ⟨x, hrx⟩ := exists_real_smul_eq_of_suzukiSmallRealGroundMinimizers
    a ha q r hqreal hrreal hqground hrground hqne
  obtain ⟨y, hsy⟩ := exists_real_smul_eq_of_suzukiSmallRealGroundMinimizers
    a ha q s hqreal hsreal hqground hsground hqne
  refine ⟨(x : ℂ) + I * (y : ℂ), ?_⟩
  rw [hpsplit, hrx, hsy]
  change (x : ℂ) • q + I • ((y : ℂ) • q) =
    ((x : ℂ) + I * (y : ℂ)) • q
  module

/-- Every vector in the exact finite-aperture operator domain has a canonical representative
in the complete CCM form domain, with exact quadratic-form value. -/
theorem ccmRestrictedWeilOperator_exists_completeFormLift
    (b : SuzukiPositiveAperture)
    (x : (ccmRestrictedWeilOperator b).domain) :
    ∃ u : CCMArchimedeanFormDomain b,
      ccmArchimedeanFormToAperture b u =
          (x : suzukiApertureHilbert b) ∧
        ccmRestrictedWeilForm b u u =
          inner ℂ (ccmRestrictedWeilOperator b x)
            (x : suzukiApertureHilbert b) := by
  let J := ccmArchimedeanFormToAperture b
  let B := ccmRestrictedWeilBoundedRemainder b
  let C := boundedPerturbedFormCovariance J B
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
  have hCinj : Function.Injective C :=
    boundedPerturbedFormCovariance_injective J B
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
      (ccmArchimedeanFormToAperture_injective b)
      (denseRange_ccmArchimedeanFormToAperture b)
  have hxrange : (x : suzukiApertureHilbert b) ∈ C.range := by
    simpa only [J, B, C, ccmRestrictedWeilOperator,
      boundedPerturbedFriedrichsOperator_domain,
      closedDenseInverse_domain] using x.property
  obtain ⟨y, hy⟩ := hxrange
  have hmem : C y ∈ (ccmRestrictedWeilOperator b).domain := by
    change C y ∈ (closedDenseInverse C).domain
    exact (closedDenseInverse_apply_C C hCinj y).1
  let xc : (ccmRestrictedWeilOperator b).domain := ⟨C y, hmem⟩
  let u : CCMArchimedeanFormDomain b :=
    boundedPerturbedFormRieszInv J B
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b) (J.adjoint y)
  have hrep := boundedPerturbedFriedrichsOperator_represents_form
    J B (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b)
      (ccmArchimedeanFormToAperture_injective b)
      (denseRange_ccmArchimedeanFormToAperture b) y u
  change (xc : suzukiApertureHilbert b) = J u ∧
    inner ℂ (ccmRestrictedWeilOperator b xc) (J u) =
      inner ℂ u u + inner ℂ (B (J u)) (J u) at hrep
  have hxc : xc = x := Subtype.ext hy
  refine ⟨u, ?_, ?_⟩
  · rw [← hrep.1, hxc]
  · change inner ℂ u u + inner ℂ (B (J u)) (J u) = _
    rw [← hrep.2, hxc]
    congr 1

theorem inner_ccmArchimedeanUnitSmallFormEquiv_embedding
    (a : SuzukiPrimeFreeSmallAperture)
    (q r : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    inner ℂ
        (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a q))
        (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a r)) =
      inner ℂ
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q)
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture r) := by
  rw [← ccmArchimedeanUnitSmallFormEquiv_embedding,
    ← ccmArchimedeanUnitSmallFormEquiv_embedding]
  exact (suzukiPhysicalUnitSmallEquiv a).inner_map_map _ _

/-- Every finite-aperture closed-form bottom minimizer is a genuine bottom eigenvector of the
represented Suzuki operator. -/
theorem suzukiSmallFormGroundMinimizer_exists_groundEigenstate
    (a : SuzukiPrimeFreeSmallAperture)
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hground : suzukiSmallScaledClosedEnergy a q =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding q‖ ^ 2) :
    ∃ hmem : ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a q) ∈
        (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
      ccmRestrictedWeilOperator ⟨a.val, a.pos⟩
          ⟨ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
            (ccmArchimedeanUnitSmallFormEquiv a q), hmem⟩ =
        (suzukiSmallScaledGroundEnergy a : ℂ) •
          ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
            (ccmArchimedeanUnitSmallFormEquiv a q) := by
  letI : CompleteSpace (suzukiApertureHilbert ⟨a.val, a.pos⟩) :=
    instCompleteSpaceSuzukiApertureHilbert ⟨a.val, a.pos⟩
  apply boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩)
    (ccmRestrictedWeilBoundedRemainder ⟨a.val, a.pos⟩)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint ⟨a.val, a.pos⟩)
    (ccmArchimedeanFormToAperture_injective ⟨a.val, a.pos⟩)
    (denseRange_ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩)
    (ccmArchimedeanUnitSmallFormEquiv a q)
    ((suzukiSmallScaledGroundEnergy a : ℂ) •
      ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a q))
  intro v
  let r := (ccmArchimedeanUnitSmallFormEquiv a).symm v
  have hvr : ccmArchimedeanUnitSmallFormEquiv a r = v :=
    (ccmArchimedeanUnitSmallFormEquiv a).apply_symm_apply v
  change ccmRestrictedWeilForm ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q) v =
    inner ℂ
      ((suzukiSmallScaledGroundEnergy a : ℂ) •
        ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a q))
      (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ v)
  rw [← hvr]
  change suzukiSmallScaledClosedForm a q r = _
  rw [suzukiSmallGroundShiftedComplexForm_eq_zero_left a q hground r]
  have hsmul := inner_smul_left
    (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q))
    (ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a r))
    (suzukiSmallScaledGroundEnergy a : ℂ)
  rw [hsmul]
  rw [show (starRingEnd ℂ) (suzukiSmallScaledGroundEnergy a : ℂ) =
      (suzukiSmallScaledGroundEnergy a : ℂ) by
    exact Complex.conj_ofReal _]
  congr 1
  rw [inner_ccmArchimedeanUnitSmallFormEquiv_embedding]
  change inner ℂ
      ((suzukiApertureL2Equiv suzukiLimitingUnitAperture).symm
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q))
      ((suzukiApertureL2Equiv suzukiLimitingUnitAperture).symm
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture r)) = _
  exact (suzukiApertureL2Equiv suzukiLimitingUnitAperture).symm.inner_map_map _ _

/-- Strict finite sign defect makes Suzuki's exact finite-aperture bottom eigenspace a complex
line. This is operator simplicity, not merely form-domain uniqueness. -/
theorem ccmRestrictedWeilOperator_groundEigenspace_simple_of_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val) :
    ∃ e : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
      (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ≠ 0 ∧
      ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ e =
        (suzukiSmallScaledGroundEnergy a : ℂ) •
          (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ∧
      ∀ x : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
        ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ x =
            (suzukiSmallScaledGroundEnergy a : ℂ) •
              (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) →
          ∃ c : ℂ, (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) =
            c • (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) := by
  obtain ⟨q, hqreal, hqne, hqground⟩ :=
    exists_nonzero_suzukiSmallRealGroundMinimizer a
  obtain ⟨hmem, heig⟩ :=
    suzukiSmallFormGroundMinimizer_exists_groundEigenstate a q hqground
  let e : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain :=
    ⟨ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q), hmem⟩
  have hunitNe : ccmArchimedeanFormToAperture
      suzukiLimitingUnitAperture q ≠ 0 := by
    intro hzero
    apply hqne
    apply norm_eq_zero.mp
    rw [norm_suzukiLimitingLogFormEmbedding_eq_physical, hzero, norm_zero]
  have heNe : (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ≠ 0 := by
    change ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q) ≠ 0
    rw [← ccmArchimedeanUnitSmallFormEquiv_embedding]
    simpa only [map_zero] using
      (suzukiPhysicalUnitSmallEquiv a).injective.ne hunitNe
  refine ⟨e, heNe, heig, ?_⟩
  intro x hx
  obtain ⟨u, huJ, huform⟩ :=
    ccmRestrictedWeilOperator_exists_completeFormLift ⟨a.val, a.pos⟩ x
  let p := (ccmArchimedeanUnitSmallFormEquiv a).symm u
  have hpu : ccmArchimedeanUnitSmallFormEquiv a p = u :=
    (ccmArchimedeanUnitSmallFormEquiv a).apply_symm_apply u
  have hnorm : ‖(x : suzukiApertureHilbert ⟨a.val, a.pos⟩)‖ =
      ‖suzukiLimitingLogFormEmbedding p‖ := by
    rw [← huJ, ← hpu, ← ccmArchimedeanUnitSmallFormEquiv_embedding,
      (suzukiPhysicalUnitSmallEquiv a).norm_map,
      norm_suzukiLimitingLogFormEmbedding_eq_physical]
  have hinner :
      (inner ℂ (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ x)
        (x : suzukiApertureHilbert ⟨a.val, a.pos⟩)).re =
      suzukiSmallScaledGroundEnergy a *
        ‖(x : suzukiApertureHilbert ⟨a.val, a.pos⟩)‖ ^ 2 := by
    rw [hx]
    have hsmul := inner_smul_left
      (x : suzukiApertureHilbert ⟨a.val, a.pos⟩)
      (x : suzukiApertureHilbert ⟨a.val, a.pos⟩)
      (suzukiSmallScaledGroundEnergy a : ℂ)
    rw [hsmul]
    rw [show (starRingEnd ℂ) (suzukiSmallScaledGroundEnergy a : ℂ) =
        (suzukiSmallScaledGroundEnergy a : ℂ) by
      exact Complex.conj_ofReal _]
    rw [inner_self_eq_norm_sq_to_K]
    norm_num [Complex.mul_re, pow_two]
  have hpground : suzukiSmallScaledClosedEnergy a p =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2 := by
    rw [suzukiSmallScaledClosedEnergy, hpu,
      ← ccmRestrictedWeilForm_self_re_eq_source]
    rw [huform, hinner, hnorm]
  obtain ⟨c, hpc⟩ := exists_complex_smul_eq_of_suzukiSmallGroundMinimizers
    a ha q p hqreal hqground hqne hpground
  refine ⟨c, ?_⟩
  change (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) =
    c • ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q)
  rw [← huJ, ← hpu, hpc, map_smul, map_smul]

end RHTower
