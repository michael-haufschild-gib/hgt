import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundSimplicity
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundParity

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem suzukiApertureZeroExtendL2_re_nonneg_ae
    {b : ℝ} (f : SuzukiApertureIntervalL2 b)
    (hf : ∀ᵐ x : SuzukiApertureInterval b ∂volume, 0 ≤ (f x).re) :
    ∀ᵐ x : ℝ ∂volume, 0 ≤ (suzukiApertureZeroExtendL2 f x).re := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-b) b)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    have hzeroSub :
        (fun x : SuzukiApertureInterval b =>
          suzukiApertureZeroExtendL2 f x) =ᵐ[volume]
        fun x => suzukiApertureZeroExtend f x :=
      (ae_restrict_iff_subtype measurableSet_Icc).mp
        (ae_restrict_of_ae (suzukiApertureZeroExtendL2_coeFn f))
    filter_upwards [hzeroSub, suzukiApertureRepresentative_ae f, hf] with
      x hzero hrep hnonneg
    rw [hzero, suzukiApertureZeroExtend_apply, hrep]
    exact hnonneg
  · filter_upwards [
      (suzukiApertureZeroExtendL2_coeFn f).filter_mono
        (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hzero hx
    have hx' : x ∉ Icc (-b) b := hx
    rw [hzero, suzukiApertureZeroExtend_eq_zero_of_notMem f hx']
    norm_num

theorem suzukiApertureZeroExtendL2_im_eq_zero_ae
    {b : ℝ} (f : SuzukiApertureIntervalL2 b)
    (hf : ∀ᵐ x : SuzukiApertureInterval b ∂volume, (f x).im = 0) :
    ∀ᵐ x : ℝ ∂volume, (suzukiApertureZeroExtendL2 f x).im = 0 := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-b) b)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    have hzeroSub :
        (fun x : SuzukiApertureInterval b =>
          suzukiApertureZeroExtendL2 f x) =ᵐ[volume]
        fun x => suzukiApertureZeroExtend f x :=
      (ae_restrict_iff_subtype measurableSet_Icc).mp
        (ae_restrict_of_ae (suzukiApertureZeroExtendL2_coeFn f))
    filter_upwards [hzeroSub, suzukiApertureRepresentative_ae f, hf] with
      x hzero hrep hreal
    rw [hzero, suzukiApertureZeroExtend_apply, hrep]
    exact hreal
  · filter_upwards [
      (suzukiApertureZeroExtendL2_coeFn f).filter_mono
        (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hzero hx
    have hx' : x ∉ Icc (-b) b := hx
    rw [hzero, suzukiApertureZeroExtend_eq_zero_of_notMem f hx']
    norm_num

/-- A real, nonnegative `L²` vector cannot have odd reflection parity unless it vanishes. -/
theorem eq_zero_of_l2Reflection_eq_neg_of_re_nonneg_of_im_eq_zero
    (f : SoninL2)
    (hodd : l2Reflection f = -f)
    (hnonneg : ∀ᵐ x : ℝ ∂volume, 0 ≤ (f x).re)
    (hreal : ∀ᵐ x : ℝ ∂volume, (f x).im = 0) :
    f = 0 := by
  apply Lp.ext
  have hnonnegNeg : ∀ᵐ x : ℝ ∂volume, 0 ≤ (f (-x)).re :=
    (Measure.measurePreserving_neg
      (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae hnonneg
  have href := l2Reflection_ae f
  rw [hodd] at href
  filter_upwards [hnonneg, hnonnegNeg, hreal, href, Lp.coeFn_neg f] with
    x hx hnx hxim hrefx hneg
  have hcomplex : -(f x) = f (-x) := by
    rw [hneg] at hrefx
    simpa only [Pi.neg_apply] using hrefx
  have hrefRe : -(f x).re = (f (-x)).re := by
    simpa using congrArg Complex.re hcomplex
  have hxre : (f x).re = 0 := by linarith
  have hfx : f x = 0 := Complex.ext hxre hxim
  simpa using hfx

theorem suzukiLimitingPhysical_re_nonneg_ae
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : ∀ᵐ x : SuzukiApertureInterval 1 ∂volume,
      0 ≤ (suzukiLimitingLogFormEmbedding q x).re) :
    ∀ᵐ x : ℝ ∂volume,
      0 ≤ (((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
        suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2) x).re := by
  have hzero := suzukiApertureZeroExtendL2_re_nonneg_ae
    (suzukiLimitingLogFormEmbedding q) hq
  have hphysical :
      (suzukiApertureL2Equiv suzukiLimitingUnitAperture
        (suzukiLimitingLogFormEmbedding q) :
          suzukiApertureHilbert suzukiLimitingUnitAperture) =
        ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q := by
    change (suzukiApertureL2Equiv suzukiLimitingUnitAperture)
      ((suzukiApertureL2Equiv suzukiLimitingUnitAperture).symm
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q)) = _
    exact (suzukiApertureL2Equiv suzukiLimitingUnitAperture).apply_symm_apply _
  change ∀ᵐ x : ℝ ∂volume,
    0 ≤ (suzukiApertureZeroExtendL2
      (suzukiLimitingLogFormEmbedding q) x).re at hzero
  rw [show suzukiApertureZeroExtendL2 (suzukiLimitingLogFormEmbedding q) =
      ((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
        suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2) by
    exact congrArg Subtype.val hphysical] at hzero
  exact hzero

theorem suzukiLimitingPhysical_im_eq_zero_ae
    (q : CCMArchimedeanFormDomain suzukiLimitingUnitAperture)
    (hq : q ∈ SuzukiLimitingRealFormDomain) :
    ∀ᵐ x : ℝ ∂volume,
      (((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
        suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2) x).im = 0 := by
  have hinterval :=
    suzukiLimitingLogFormEmbedding_im_eq_zero_ae_of_mem_realFormDomain hq
  have hzero := suzukiApertureZeroExtendL2_im_eq_zero_ae
    (suzukiLimitingLogFormEmbedding q) hinterval
  have hphysical :
      (suzukiApertureL2Equiv suzukiLimitingUnitAperture
        (suzukiLimitingLogFormEmbedding q) :
          suzukiApertureHilbert suzukiLimitingUnitAperture) =
        ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q := by
    change (suzukiApertureL2Equiv suzukiLimitingUnitAperture)
      ((suzukiApertureL2Equiv suzukiLimitingUnitAperture).symm
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q)) = _
    exact (suzukiApertureL2Equiv suzukiLimitingUnitAperture).apply_symm_apply _
  change ∀ᵐ x : ℝ ∂volume,
    (suzukiApertureZeroExtendL2
      (suzukiLimitingLogFormEmbedding q) x).im = 0 at hzero
  rw [show suzukiApertureZeroExtendL2 (suzukiLimitingLogFormEmbedding q) =
      ((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
        suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2) by
    exact congrArg Subtype.val hphysical] at hzero
  exact hzero

/-- Under the strict finite sign defect, an attained exact ground form state cannot be odd. -/
theorem ccmRestrictedWeil_groundFormState_not_odd_of_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val)
    (f : CCMArchimedeanFormDomain ⟨a.val, a.pos⟩)
    (hfne : ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f ≠ 0)
    (hfground : ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩ f =
      ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ *
        ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f‖ ^ 2) :
    ccmArchimedeanFormReflection ⟨a.val, a.pos⟩ f ≠ -f := by
  intro hfodd
  obtain ⟨q0, hq0real, hq0ne, hq0ground⟩ :=
    exists_nonzero_suzukiSmallRealGroundMinimizer a
  obtain ⟨q, hqreal, hqground, hqne, hqnonneg, _⟩ :=
    exists_nonnegative_orientation_suzukiSmallRealGroundMinimizer
      a ha q0 hq0real hq0ground hq0ne
  let p := (ccmArchimedeanUnitSmallFormEquiv a).symm f
  have hpf : ccmArchimedeanUnitSmallFormEquiv a p = f :=
    (ccmArchimedeanUnitSmallFormEquiv a).apply_symm_apply f
  have hnorm : ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f‖ =
      ‖suzukiLimitingLogFormEmbedding p‖ := by
    rw [← hpf, ← ccmArchimedeanUnitSmallFormEquiv_embedding,
      (suzukiPhysicalUnitSmallEquiv a).norm_map,
      norm_suzukiLimitingLogFormEmbedding_eq_physical]
  have hpground : suzukiSmallScaledClosedEnergy a p =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2 := by
    change ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a p) =
      ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2
    rw [hpf, hfground, hnorm]
  obtain ⟨c, hpc⟩ := exists_complex_smul_eq_of_suzukiSmallGroundMinimizers
    a ha q p hqreal hqground hqne hpground
  have hcne : c ≠ 0 := by
    intro hc
    have hpzero : p = 0 := by rw [hpc, hc, zero_smul]
    apply hfne
    rw [← hpf, hpzero, map_zero, map_zero]
  let F : SoninL2 :=
    ((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
      suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2)
  let Fs : SoninL2 :=
    ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q) :
        suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)
  have hJfOdd :
      l2Reflection
          ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f :
            suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) =
        -((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f :
            suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) := by
    have h := ccmArchimedeanFormToAperture_reflection ⟨a.val, a.pos⟩ f
    rw [hfodd, map_neg] at h
    exact h.symm
  have hJline :
      ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f :
        suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) = c • Fs := by
    change (((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f :
      suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)) =
      c • (((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a q) :
          suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2))
    have hsubtype : ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f =
        c • ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a q) := by
      rw [← hpf, hpc, map_smul, map_smul]
    exact congrArg Subtype.val hsubtype
  have hFsOdd : l2Reflection Fs = -Fs := by
    apply smul_right_injective SoninL2 hcne
    change c • l2Reflection Fs = c • (-Fs)
    rw [← map_smul l2Reflection, ← hJline, hJfOdd, hJline]
    module
  have hdilation : Fs =
      dilation a.val⁻¹ (inv_pos.mpr a.pos) F := by
    change ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a q) :
        suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) =
      dilation a.val⁻¹ (inv_pos.mpr a.pos)
        ((ccmArchimedeanFormToAperture suzukiLimitingUnitAperture q :
          suzukiApertureHilbert suzukiLimitingUnitAperture) : SoninL2)
    exact congrArg Subtype.val
      (ccmArchimedeanUnitSmallFormEquiv_embedding a q).symm
  have hFOdd : l2Reflection F = -F := by
    have h := hFsOdd
    rw [hdilation, l2Reflection_dilation, ← map_neg] at h
    exact (dilation a.val⁻¹ (inv_pos.mpr a.pos)).injective h
  have hFnonneg : ∀ᵐ x : ℝ ∂volume, 0 ≤ (F x).re :=
    suzukiLimitingPhysical_re_nonneg_ae q hqnonneg
  have hFreal : ∀ᵐ x : ℝ ∂volume, (F x).im = 0 :=
    suzukiLimitingPhysical_im_eq_zero_ae q hqreal
  have hFzero :=
    eq_zero_of_l2Reflection_eq_neg_of_re_nonneg_of_im_eq_zero
      F hFOdd hFnonneg hFreal
  have hunitNe : ccmArchimedeanFormToAperture
      suzukiLimitingUnitAperture q ≠ 0 := by
    intro hzero
    apply hqne
    apply norm_eq_zero.mp
    rw [norm_suzukiLimitingLogFormEmbedding_eq_physical, hzero, norm_zero]
  apply hunitNe
  apply Subtype.ext
  exact hFzero

/-- The pure-parity exact ground state is necessarily reflection-even once the finite sign
defect is strict. -/
theorem exists_ccmRestrictedWeil_even_groundFormState_of_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val) :
    ∃ f : CCMArchimedeanFormDomain ⟨a.val, a.pos⟩,
      ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f ≠ 0 ∧
      ccmArchimedeanFormReflection ⟨a.val, a.pos⟩ f = f ∧
      ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩ f =
        ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ *
          ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f‖ ^ 2 := by
  obtain ⟨f, hfne, hparity, hfground⟩ :=
    exists_ccmRestrictedWeil_pureParity_groundFormState ⟨a.val, a.pos⟩
  refine ⟨f, hfne, ?_, hfground⟩
  rcases hparity with hfeven | hfodd
  · exact hfeven
  · exact (ccmRestrictedWeil_groundFormState_not_odd_of_finiteSignDefect
      a ha f hfne hfground hfodd).elim

/-- Suzuki's exact finite-aperture bottom has a genuine nonzero even eigenfunction. -/
theorem ccmRestrictedWeilOperator_exists_even_groundEigenstate_of_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val) :
    ∃ e : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
      (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ≠ 0 ∧
      ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ e =
        (suzukiSmallScaledGroundEnergy a : ℂ) •
          (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ∧
      l2Reflection
          (((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)) =
        ((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) := by
  obtain ⟨f, hfne, hfeven, hfground⟩ :=
    exists_ccmRestrictedWeil_even_groundFormState_of_finiteSignDefect a ha
  let p := (ccmArchimedeanUnitSmallFormEquiv a).symm f
  have hpf : ccmArchimedeanUnitSmallFormEquiv a p = f :=
    (ccmArchimedeanUnitSmallFormEquiv a).apply_symm_apply f
  have hnorm : ‖ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩ f‖ =
      ‖suzukiLimitingLogFormEmbedding p‖ := by
    rw [← hpf, ← ccmArchimedeanUnitSmallFormEquiv_embedding,
      (suzukiPhysicalUnitSmallEquiv a).norm_map,
      norm_suzukiLimitingLogFormEmbedding_eq_physical]
  have hpground : suzukiSmallScaledClosedEnergy a p =
      suzukiSmallScaledGroundEnergy a *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2 := by
    change ccmRestrictedWeilSourceQuadratic ⟨a.val, a.pos⟩
        (ccmArchimedeanUnitSmallFormEquiv a p) =
      ccmRestrictedWeilGroundEnergy ⟨a.val, a.pos⟩ *
        ‖suzukiLimitingLogFormEmbedding p‖ ^ 2
    rw [hpf, hfground, hnorm]
  obtain ⟨hmem, heig⟩ :=
    suzukiSmallFormGroundMinimizer_exists_groundEigenstate a p hpground
  let e : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain :=
    ⟨ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a p), hmem⟩
  have heNe : (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ≠ 0 := by
    change ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
      (ccmArchimedeanUnitSmallFormEquiv a p) ≠ 0
    rw [hpf]
    exact hfne
  have heEven : l2Reflection
      (((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)) =
      ((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) := by
    change l2Reflection
        ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a p) :
            suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) =
      ((ccmArchimedeanFormToAperture ⟨a.val, a.pos⟩
          (ccmArchimedeanUnitSmallFormEquiv a p) :
            suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)
    rw [hpf]
    have hreflection :=
      ccmArchimedeanFormToAperture_reflection ⟨a.val, a.pos⟩ f
    rw [hfeven] at hreflection
    exact hreflection.symm
  exact ⟨e, heNe, heig, heEven⟩

/-- Exact finite-aperture Suzuki conclusion under the strict defect: one nonzero even ground
eigenfunction spans the entire bottom eigenspace. -/
theorem ccmRestrictedWeilOperator_exists_even_simple_groundEigenstate_of_finiteSignDefect
    (a : SuzukiPrimeFreeSmallAperture)
    (ha : 0 < suzukiFiniteSignDefectCoefficient a.val) :
    ∃ e : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
      (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ≠ 0 ∧
      ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ e =
        (suzukiSmallScaledGroundEnergy a : ℂ) •
          (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) ∧
      l2Reflection
          (((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2)) =
        ((e : suzukiApertureHilbert ⟨a.val, a.pos⟩) : SoninL2) ∧
      ∀ x : (ccmRestrictedWeilOperator ⟨a.val, a.pos⟩).domain,
        ccmRestrictedWeilOperator ⟨a.val, a.pos⟩ x =
            (suzukiSmallScaledGroundEnergy a : ℂ) •
              (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) →
          ∃ c : ℂ, (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) =
            c • (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) := by
  obtain ⟨e, heNe, heig, heEven⟩ :=
    ccmRestrictedWeilOperator_exists_even_groundEigenstate_of_finiteSignDefect a ha
  obtain ⟨g, hgNe, hgEig, hgSpan⟩ :=
    ccmRestrictedWeilOperator_groundEigenspace_simple_of_finiteSignDefect a ha
  obtain ⟨ce, heLine⟩ := hgSpan e heig
  have hce : ce ≠ 0 := by
    intro hzero
    apply heNe
    rw [heLine, hzero, zero_smul]
  refine ⟨e, heNe, heig, heEven, ?_⟩
  intro x hx
  obtain ⟨cx, hxLine⟩ := hgSpan x hx
  refine ⟨cx / ce, ?_⟩
  calc
    (x : suzukiApertureHilbert ⟨a.val, a.pos⟩) =
        cx • (g : suzukiApertureHilbert ⟨a.val, a.pos⟩) := hxLine
    _ = (cx / ce) •
        (ce • (g : suzukiApertureHilbert ⟨a.val, a.pos⟩)) := by
          rw [smul_smul, div_mul_cancel₀ cx hce]
    _ = (cx / ce) •
        (e : suzukiApertureHilbert ⟨a.val, a.pos⟩) := by rw [← heLine]

end RHTower
