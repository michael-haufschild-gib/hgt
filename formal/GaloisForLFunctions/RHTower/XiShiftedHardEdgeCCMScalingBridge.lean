import GaloisForLFunctions.RHTower.SuzukiSmallApertureFormScaling
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDensityMeasure

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section

namespace RHTower

def routeUCCMScale : ℝ := 2 * Real.pi

theorem routeUCCMScale_pos : 0 < routeUCCMScale := by
  unfold routeUCCMScale
  positivity

def routeUCCMScaledAperture (a : SuzukiPositiveAperture) : SuzukiPositiveAperture :=
  ⟨routeUCCMScale * a.1, mul_pos routeUCCMScale_pos a.2⟩

@[simp] theorem routeUCCMScaledAperture_val (a : SuzukiPositiveAperture) :
    (routeUCCMScaledAperture a).1 = routeUCCMScale * a.1 := rfl

def routeUScaleApertureVector (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    suzukiApertureHilbert (routeUCCMScaledAperture a) :=
  ⟨dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos) f.1, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    refine ⟨dilation routeUCCMScale⁻¹
      (inv_pos.mpr routeUCCMScale_pos) f.1, ?_⟩
    change indicatorCutoff
      (centralInterval (routeUCCMScale * a.1))
      (measurableSet_centralInterval (routeUCCMScale * a.1))
        (dilation routeUCCMScale⁻¹
          (inv_pos.mpr routeUCCMScale_pos) f.1) = _
    rw [indicatorCutoff_dilation]
    have hfix := indicatorCutoff_suzukiApertureHilbert a f
    change indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1 = f.1 at hfix
    have hscale : routeUCCMScale⁻¹ *
        (routeUCCMScale * a.1) = a.1 := by
      field_simp [routeUCCMScale, Real.pi_ne_zero]
    rw [hscale, hfix]⟩

@[simp] theorem routeUScaleApertureVector_val
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (routeUScaleApertureVector a f).1 =
      dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos) f.1 := rfl

def routeUToCCMHlogFormCLM (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a →L[ℂ]
      SuzukiHlogFormDomain (routeUCCMScaledAperture a) :=
  ((suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
      (inv_pos.mpr routeUCCMScale_pos)).domRestrict
    (suzukiHlogSupportDefect a).ker).codRestrict
      (suzukiHlogSupportDefect (routeUCCMScaledAperture a)).ker fun f => by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff
      (centralInterval (routeUCCMScale * a.1))
      (measurableSet_centralInterval (routeUCCMScale * a.1)))
        (suzukiHlogFourierToTime
          (suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
            (inv_pos.mpr routeUCCMScale_pos) f.1)) = 0
    rw [suzukiHlogFourierToTime_fourierScale, sub_apply,
      one_apply_eq_self, sub_eq_zero, indicatorCutoff_dilation]
    apply congrArg (dilation routeUCCMScale⁻¹
      (inv_pos.mpr routeUCCMScale_pos))
    have hfix := indicatorCutoff_suzukiHlogFormEmbedding a f
    change indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1 at hfix
    have hscale : routeUCCMScale⁻¹ * (routeUCCMScale * a.1) = a.1 := by
      field_simp [routeUCCMScale, Real.pi_ne_zero]
    rw [hscale]
    exact hfix.symm

theorem routeUToCCMHlogFormCLM_time
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    suzukiHlogFormEmbedding (routeUCCMScaledAperture a)
        (routeUToCCMHlogFormCLM a f) =
      dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos)
        (suzukiHlogFormEmbedding a f) := by
  change suzukiHlogFourierToTime
      (suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
        (inv_pos.mpr routeUCCMScale_pos) f.1) = _
  rw [suzukiHlogFourierToTime_fourierScale]
  rfl

theorem routeUToCCMHlogFormCLM_spectral
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    suzukiHlogWeightedToL2 (routeUToCCMHlogFormCLM a f).1 =
      dilation routeUCCMScale routeUCCMScale_pos
        (suzukiHlogWeightedToL2 f.1) := by
  change suzukiHlogWeightedToL2
      (suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
        (inv_pos.mpr routeUCCMScale_pos) f.1) = _
  rw [suzukiHlogWeightedToL2_fourierScale]
  congr 1
  simp [routeUCCMScale]

/-- Inverse normalized dilation from the CCM-scaled aperture back to Route U's angular-frequency
aperture. -/
def ccmToRouteUHlogFormCLM (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain (routeUCCMScaledAperture a) →L[ℂ]
      SuzukiHlogFormDomain a :=
  ((suzukiHlogFourierScaleCLM routeUCCMScale routeUCCMScale_pos).domRestrict
    (suzukiHlogSupportDefect (routeUCCMScaledAperture a)).ker).codRestrict
      (suzukiHlogSupportDefect a).ker fun f => by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (suzukiHlogFourierToTime
          (suzukiHlogFourierScaleCLM routeUCCMScale
            routeUCCMScale_pos f.1)) = 0
    rw [suzukiHlogFourierToTime_fourierScale, sub_apply,
      one_apply_eq_self, sub_eq_zero, indicatorCutoff_dilation]
    apply congrArg (dilation routeUCCMScale routeUCCMScale_pos)
    have hfix := indicatorCutoff_suzukiHlogFormEmbedding
      (routeUCCMScaledAperture a) f
    change indicatorCutoff (centralInterval (routeUCCMScale * a.1))
      (measurableSet_centralInterval (routeUCCMScale * a.1))
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1 at hfix
    simpa using hfix.symm

theorem ccmToRouteUHlogFormCLM_routeUToCCM
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmToRouteUHlogFormCLM a (routeUToCCMHlogFormCLM a f) = f := by
  apply Subtype.ext
  change suzukiHlogFourierScaleCLM routeUCCMScale routeUCCMScale_pos
      (suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
        (inv_pos.mpr routeUCCMScale_pos) f.1) = f.1
  simpa using suzukiHlogFourierScaleCLM_inv_apply routeUCCMScale⁻¹
    (inv_pos.mpr routeUCCMScale_pos) f.1

theorem routeUToCCMHlogFormCLM_ccmToRouteU
    (a : SuzukiPositiveAperture)
    (f : SuzukiHlogFormDomain (routeUCCMScaledAperture a)) :
    routeUToCCMHlogFormCLM a (ccmToRouteUHlogFormCLM a f) = f := by
  apply Subtype.ext
  change suzukiHlogFourierScaleCLM routeUCCMScale⁻¹
      (inv_pos.mpr routeUCCMScale_pos)
      (suzukiHlogFourierScaleCLM routeUCCMScale routeUCCMScale_pos f.1) = f.1
  exact suzukiHlogFourierScaleCLM_inv_apply routeUCCMScale
    routeUCCMScale_pos f.1

/-- Exact equivalence between Route U's angular-frequency form domain and the CCM source domain
at aperture enlarged by `2π`. -/
def routeUCCMHlogFormEquiv (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a ≃L[ℂ]
      SuzukiHlogFormDomain (routeUCCMScaledAperture a) where
  toLinearEquiv :=
    { toFun := routeUToCCMHlogFormCLM a
      invFun := ccmToRouteUHlogFormCLM a
      left_inv := ccmToRouteUHlogFormCLM_routeUToCCM a
      right_inv := routeUToCCMHlogFormCLM_ccmToRouteU a
      map_add' := (routeUToCCMHlogFormCLM a).map_add
      map_smul' := (routeUToCCMHlogFormCLM a).map_smul }
  continuous_toFun := (routeUToCCMHlogFormCLM a).continuous
  continuous_invFun := (ccmToRouteUHlogFormCLM a).continuous

def routeUToCCMFormVector (a : SuzukiPositiveAperture)
    (f : SuzukiHlogFormDomain a) :
    CCMArchimedeanFormDomain (routeUCCMScaledAperture a) :=
  ccmLogFormToArchimedean (routeUCCMScaledAperture a)
    (routeUToCCMHlogFormCLM a f)

/-- Route U's form domain is not merely embedded in the CCM domain: after the forced `2π`
aperture change, it is the whole complete CCM form domain. -/
def routeUCCMFormEquiv (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a ≃L[ℂ]
      CCMArchimedeanFormDomain (routeUCCMScaledAperture a) :=
  (routeUCCMHlogFormEquiv a).trans
    (ccmArchimedeanLogFormDomainEquiv (routeUCCMScaledAperture a))

@[simp] theorem routeUCCMFormEquiv_apply
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    routeUCCMFormEquiv a f = routeUToCCMFormVector a f := rfl

theorem routeUToCCMFormVector_time
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmArchimedeanFormEmbedding (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) =
      dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos)
        (suzukiHlogFormEmbedding a f) := by
  change ccmArchimedeanFourierToTime
      (ccmLogToArchimedean (routeUToCCMHlogFormCLM a f).1) = _
  rw [ccmArchimedeanFourierToTime_logToArchimedean]
  exact routeUToCCMHlogFormCLM_time a f

theorem routeUToCCMFormVector_spectral
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmArchimedeanWeightedToL2 (routeUToCCMFormVector a f).1 =
      dilation routeUCCMScale routeUCCMScale_pos
        (suzukiHlogWeightedToL2 f.1) := by
  change ccmArchimedeanWeightedToL2
      (ccmLogToArchimedean (routeUToCCMHlogFormCLM a f).1) = _
  rw [ccmArchimedeanWeightedToL2_logToArchimedean,
    routeUToCCMHlogFormCLM_spectral]

def routeUHlogApertureVector (a : SuzukiPositiveAperture)
    (f : SuzukiHlogFormDomain a) : suzukiApertureHilbert a :=
  ⟨suzukiHlogFormEmbedding a f, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨suzukiHlogFormEmbedding a f,
      indicatorCutoff_suzukiHlogFormEmbedding a f⟩⟩

@[simp] theorem routeUHlogApertureVector_val
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    (routeUHlogApertureVector a f).1 = suzukiHlogFormEmbedding a f := rfl

theorem ccmArchimedeanFormToAperture_routeUToCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmArchimedeanFormToAperture (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) =
      routeUScaleApertureVector a (routeUHlogApertureVector a f) := by
  apply Subtype.ext
  exact routeUToCCMFormVector_time a f

/-- Route U polar carrier in its unscaled angular-frequency normalization. -/
def routeUClosedPolarQuadratic
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) : ℝ :=
  let p := routeUHlogApertureVector a f
  (((starRingEnd ℂ)
          (inner ℂ (ccmPolarApertureVector a
            (routeUCCMScale * (-1 / 2))) p) *
            inner ℂ (ccmPolarApertureVector a
              (routeUCCMScale * (1 / 2))) p +
        (starRingEnd ℂ)
          (inner ℂ (ccmPolarApertureVector a
            (routeUCCMScale * (1 / 2))) p) *
            inner ℂ (ccmPolarApertureVector a
              (routeUCCMScale * (-1 / 2))) p).re)

/-- Route U's closed source quadratic before angular-frequency normalization. -/
def routeUClosedSourceQuadratic
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) : ℝ :=
  let g := suzukiHlogWeightedToL2 f.1
  let p := routeUHlogApertureVector a f
  (∫ x : ℝ, gammaHardyPhaseRate x * ‖(g : SoninL2) x‖ ^ 2) +
    (routeUCCMScale / 2) * routeUClosedPolarQuadratic a f -
    (1 / 2) *
      ∑ n ∈ Finset.Icc 2
          (routeUHardEdgeFrequencyBound (routeUCCMScaledAperture a).1),
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          (1 / Real.sqrt n) *
            (inner ℂ
                (logTranslationCLM
                  (routeUCCMScale⁻¹ * Real.log n) p.1) p.1 +
              inner ℂ
                (logTranslationCLM
                  (-(routeUCCMScale⁻¹ * Real.log n)) p.1) p.1).re

theorem logTranslationCLM_ae (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + h) := by
  change (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
      (MellinL2.realTranslation_measurePreserving h) f : ℝ → ℂ) =ᵐ[volume]
    fun x => f (x + h)
  have hcoe := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)
  exact hcoe.trans (Filter.Eventually.of_forall fun x => rfl)

theorem logTranslationCLM_dilation
    (c : ℝ) (hc : 0 < c) (h : ℝ) (f : SoninL2) :
    logTranslationCLM h (dilation c hc f) =
      dilation c hc (logTranslationCLM (c * h) f) := by
  apply Lp.ext
  have hdilShift := (dilation_ae c hc f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htransF := (logTranslationCLM_ae (c * h) f).comp_tendsto
      (realMul_quasiMeasurePreserving c hc.ne').tendsto_ae
  filter_upwards [
    logTranslationCLM_ae h (dilation c hc f),
    hdilShift,
    dilation_ae c hc (logTranslationCLM (c * h) f),
    htransF
  ] with x hleft hdil hright htrans
  rw [hleft]
  rw [show (dilation c hc f : SoninL2) (x + h) =
      (Real.sqrt c : ℂ) * f (c * (x + h)) by
        simpa [MellinL2.realTranslationEquiv, Function.comp_apply] using hdil]
  rw [hright]
  have htrans' : (logTranslationCLM (c * h) f : SoninL2) (c * x) =
      f (c * x + c * h) := by
    simpa only [Function.comp_apply] using htrans
  rw [htrans']
  congr 2
  ring

theorem inner_logTranslationCLM_dilation
    (c : ℝ) (hc : 0 < c) (h : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM h (dilation c hc f)) (dilation c hc f) =
      inner ℂ (logTranslationCLM (c * h) f) f := by
  rw [logTranslationCLM_dilation]
  exact (dilation c hc).inner_map_map _ _

theorem inner_logTranslation_fourierUnitary_symm
    (h : ℝ) (g : SoninL2) :
    inner ℂ
        (logTranslationCLM h (fourierUnitary.symm g))
        (fourierUnitary.symm g) =
      inner ℂ (MellinL2.fourierPhaseMulUnitary h g) g := by
  calc
    _ = inner ℂ
        (fourierUnitary (logTranslationCLM h (fourierUnitary.symm g)))
        (fourierUnitary (fourierUnitary.symm g)) :=
      fourierUnitary.inner_map_map _ _ |>.symm
    _ = _ := by
      change inner ℂ
        (fourierUnitary
          (MellinL2.additiveTranslationUnitary h (fourierUnitary.symm g)))
        (fourierUnitary (fourierUnitary.symm g)) = _
      have ht : fourierUnitary
          (MellinL2.additiveTranslationUnitary h (fourierUnitary.symm g)) =
        MellinL2.fourierPhaseMulUnitary h g := by
        calc
          _ = MellinL2.fourierPhaseMulUnitary h
              (fourierUnitary (fourierUnitary.symm g)) := by
            exact MellinL2.fourier_additiveTranslation h (fourierUnitary.symm g)
          _ = _ := by rw [fourierUnitary.apply_symm_apply]
      rw [ht, fourierUnitary.apply_symm_apply]

theorem re_inner_logTranslation_fourierUnitary_symm
    (h : ℝ) (g : SoninL2) :
    (inner ℂ
        (logTranslationCLM h (fourierUnitary.symm g))
        (fourierUnitary.symm g)).re =
      ∫ x : ℝ, ‖g x‖ ^ 2 * Real.cos (2 * Real.pi * h * x) := by
  rw [inner_logTranslation_fourierUnitary_symm, MeasureTheory.L2.inner_def]
  have hint := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
    (MellinL2.fourierPhaseMulUnitary h g) g
  calc
    _ = ∫ x : ℝ, RCLike.re
        (inner ℂ ((MellinL2.fourierPhaseMulUnitary h g) x) (g x)) :=
      (integral_re hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [MellinL2.fourierPhaseMulAux_ae h g] with x hphase
      change RCLike.re
          (inner ℂ (MellinL2.fourierPhaseMulAux h g x) (g x)) = _
      rw [hphase]
      simp only [RCLike.inner_apply', starRingEnd_apply, map_mul,
        MellinL2.fourierPhase, Real.fourierChar_apply]
      simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

theorem re_inner_logTranslation_symm_fourierUnitary_symm
    (h : ℝ) (g : SoninL2) :
    (inner ℂ
          (logTranslationCLM h (fourierUnitary.symm g))
          (fourierUnitary.symm g) +
        inner ℂ
          (logTranslationCLM (-h) (fourierUnitary.symm g))
          (fourierUnitary.symm g)).re =
      2 * ∫ x : ℝ, ‖g x‖ ^ 2 * Real.cos (2 * Real.pi * h * x) := by
  rw [Complex.add_re,
    re_inner_logTranslation_fourierUnitary_symm,
    re_inner_logTranslation_fourierUnitary_symm]
  have hcos : (fun x : ℝ => ‖g x‖ ^ 2 * Real.cos (2 * Real.pi * -h * x)) =
      fun x : ℝ => ‖g x‖ ^ 2 * Real.cos (2 * Real.pi * h * x) := by
    funext x
    rw [show 2 * Real.pi * -h * x = -(2 * Real.pi * h * x) by ring,
      Real.cos_neg]
  rw [hcos]
  ring

theorem routeUHlog_translation_symm_eq_cosine
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) (h : ℝ) :
    (inner ℂ
          (logTranslationCLM (routeUCCMScale⁻¹ * h)
            (routeUHlogApertureVector a f).1)
          (routeUHlogApertureVector a f).1 +
        inner ℂ
          (logTranslationCLM (-(routeUCCMScale⁻¹ * h))
            (routeUHlogApertureVector a f).1)
          (routeUHlogApertureVector a f).1).re =
      2 * ∫ x : ℝ, ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 *
        Real.cos (x * h) := by
  change (inner ℂ
          (logTranslationCLM (routeUCCMScale⁻¹ * h)
            (fourierUnitary.symm (suzukiHlogWeightedToL2 f.1)))
          (fourierUnitary.symm (suzukiHlogWeightedToL2 f.1)) +
        inner ℂ
          (logTranslationCLM (-(routeUCCMScale⁻¹ * h))
            (fourierUnitary.symm (suzukiHlogWeightedToL2 f.1)))
          (fourierUnitary.symm (suzukiHlogWeightedToL2 f.1))).re = _
  rw [re_inner_logTranslation_symm_fourierUnitary_symm]
  congr 2
  funext x
  congr 1
  congr 1
  field_simp [routeUCCMScale, Real.pi_ne_zero]
  unfold routeUCCMScale
  ring

theorem dilation_routeUCCMPolarL2Vector
    (a : SuzukiPositiveAperture) (s : ℝ) :
    dilation routeUCCMScale routeUCCMScale_pos
        (ccmPolarL2Vector (routeUCCMScaledAperture a) s) =
      (Real.sqrt routeUCCMScale : ℂ) •
        ccmPolarL2Vector a (routeUCCMScale * s) := by
  apply Lp.ext
  have hpolarScaled := (ccmPolarL2Vector_coeFn
    (routeUCCMScaledAperture a) s).comp_tendsto
      (realMul_quasiMeasurePreserving routeUCCMScale
        routeUCCMScale_pos.ne').tendsto_ae
  filter_upwards [
    dilation_ae routeUCCMScale routeUCCMScale_pos
      (ccmPolarL2Vector (routeUCCMScaledAperture a) s),
    hpolarScaled,
    ccmPolarL2Vector_coeFn a (routeUCCMScale * s),
    Lp.coeFn_smul (Real.sqrt routeUCCMScale : ℂ)
      (ccmPolarL2Vector a (routeUCCMScale * s))
  ] with x hdil hscaled hbase hsmul
  have hsmul' :
      (((Real.sqrt routeUCCMScale : ℂ) •
          ccmPolarL2Vector a (routeUCCMScale * s) : SoninL2) : ℝ → ℂ) x =
        (Real.sqrt routeUCCMScale : ℂ) *
          (ccmPolarL2Vector a (routeUCCMScale * s) : ℝ → ℂ) x := by
    rw [hsmul]
    rfl
  rw [hdil, hsmul']
  have hscaled' :
      (ccmPolarL2Vector (routeUCCMScaledAperture a) s : ℝ → ℂ)
          (routeUCCMScale * x) =
        (centralInterval (routeUCCMScale * a.1)).indicator
          (ccmPolarProfile s) (routeUCCMScale * x) := by
    simpa only [Function.comp_apply, routeUCCMScaledAperture] using hscaled
  rw [hscaled', hbase]
  change (Real.sqrt routeUCCMScale : ℂ) *
      (centralInterval (routeUCCMScale * a.1)).indicator
        (ccmPolarProfile s) (routeUCCMScale * x) =
    (Real.sqrt routeUCCMScale : ℂ) *
      (centralInterval a.1).indicator
        (ccmPolarProfile (routeUCCMScale * s)) x
  by_cases hx : x ∈ centralInterval a.1
  · have hrx : routeUCCMScale * x ∈
        centralInterval (routeUCCMScale * a.1) :=
      (mem_centralInterval_mul_iff a.1 routeUCCMScale x
        routeUCCMScale_pos).mp hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hrx]
    unfold ccmPolarProfile
    congr 2
    ring
  · have hrx : routeUCCMScale * x ∉
        centralInterval (routeUCCMScale * a.1) :=
      mt (mem_centralInterval_mul_iff a.1 routeUCCMScale x
        routeUCCMScale_pos).mpr hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hrx]

theorem inner_routeUCCMPolar_scaled
    (a : SuzukiPositiveAperture) (s : ℝ)
    (f : suzukiApertureHilbert a) :
    inner ℂ (ccmPolarApertureVector (routeUCCMScaledAperture a) s)
        (routeUScaleApertureVector a f) =
      (Real.sqrt routeUCCMScale : ℂ) *
        inner ℂ (ccmPolarApertureVector a (routeUCCMScale * s)) f := by
  change inner ℂ (ccmPolarL2Vector (routeUCCMScaledAperture a) s)
      (dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos) f.1) =
    (Real.sqrt routeUCCMScale : ℂ) *
      inner ℂ (ccmPolarL2Vector a (routeUCCMScale * s)) f.1
  have hunit : dilation routeUCCMScale routeUCCMScale_pos
      (dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos) f.1) = f.1 :=
    dilation_dilation_inv routeUCCMScale routeUCCMScale_pos f.1
  calc
    _ = inner ℂ
        (dilation routeUCCMScale routeUCCMScale_pos
          (ccmPolarL2Vector (routeUCCMScaledAperture a) s))
        (dilation routeUCCMScale routeUCCMScale_pos
          (dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos) f.1)) :=
      (dilation routeUCCMScale routeUCCMScale_pos).inner_map_map _ _ |>.symm
    _ = inner ℂ
        ((Real.sqrt routeUCCMScale : ℂ) •
          ccmPolarL2Vector a (routeUCCMScale * s)) f.1 := by
      rw [dilation_routeUCCMPolarL2Vector, hunit]
    _ = _ := by
      rw [inner_smul_left, Complex.conj_ofReal]

theorem integral_two_gammaHardyPhaseRate_dilation_routeUCCMScale
    (f : SoninL2) :
    (∫ xi : ℝ, 2 * gammaHardyPhaseRate (routeUCCMScale * xi) *
        ‖(dilation routeUCCMScale routeUCCMScale_pos f : SoninL2) xi‖ ^ 2) =
      2 * ∫ x : ℝ, gammaHardyPhaseRate x * ‖f x‖ ^ 2 := by
  have hdil := dilation_ae routeUCCMScale routeUCCMScale_pos f
  have hsqrt : ‖(Real.sqrt routeUCCMScale : ℂ)‖ ^ 2 = routeUCCMScale := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg routeUCCMScale),
      Real.sq_sqrt routeUCCMScale_pos.le]
  let F : ℝ → ℝ := fun x =>
    2 * routeUCCMScale * (gammaHardyPhaseRate x * ‖f x‖ ^ 2)
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F routeUCCMScale
  have hinvabs : |routeUCCMScale⁻¹| = routeUCCMScale⁻¹ :=
    abs_of_pos (inv_pos.mpr routeUCCMScale_pos)
  calc
    _ = ∫ xi : ℝ, F (routeUCCMScale * xi) := by
      apply integral_congr_ae
      filter_upwards [hdil] with xi hxi
      rw [hxi, norm_mul, mul_pow, hsqrt]
      dsimp [F]
      ring
    _ = routeUCCMScale⁻¹ * ∫ x : ℝ, F x := by
      rw [hscale, hinvabs, smul_eq_mul]
    _ = routeUCCMScale⁻¹ *
        (2 * routeUCCMScale *
          ∫ x : ℝ, gammaHardyPhaseRate x * ‖f x‖ ^ 2) := by
      congr 1
      rw [← MeasureTheory.integral_const_mul]
    _ = _ := by
      field_simp [routeUCCMScale, Real.pi_ne_zero]

theorem integrable_two_gammaHardyPhaseRate_mul_norm_sq
    (f : CCMArchimedeanFourierL2) :
    Integrable (fun xi : ℝ =>
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖(f : ℝ → ℂ) xi‖ ^ 2) := by
  let c : ℝ := 2 * gammaHardyPhaseRate 0 - 1
  have heven (xi : ℝ) :
      gammaHardyPhaseRate (2 * Real.pi * xi) =
        gammaHardyPhaseRate (2 * Real.pi * |xi|) := by
    by_cases hxi : 0 ≤ xi
    · rw [abs_of_nonneg hxi]
    · have hneg : xi < 0 := lt_of_not_ge hxi
      have habs : 2 * Real.pi * |xi| = -(2 * Real.pi * xi) := by
        rw [abs_of_neg hneg]
        ring
      rw [habs]
      exact (gammaHardyPhaseRate_neg (2 * Real.pi * xi)).symm
  have hpoint (xi : ℝ) :
      2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
          ‖(f : ℝ → ℂ) xi‖ ^ 2 =
        ccmArchimedeanFormWeight xi * ‖(f : ℝ → ℂ) xi‖ ^ 2 +
          c * ‖(f : ℝ → ℂ) xi‖ ^ 2 := by
    rw [heven]
    unfold ccmArchimedeanFormWeight c
    ring
  have hfint : Integrable (fun xi : ℝ => ‖(f : ℝ → ℂ) xi‖ ^ 2)
      ccmArchimedeanFormMeasure :=
    (MeasureTheory.Lp.memLp f).integrable_norm_pow (by norm_num)
  have hweighted : Integrable
      (fun xi : ℝ => ccmArchimedeanFormWeight xi *
        ‖(f : ℝ → ℂ) xi‖ ^ 2) volume := by
    have h := (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp hfint
    refine h.congr ?_
    filter_upwards with xi
    rw [NNReal.smul_def, smul_eq_mul,
      coe_ccmArchimedeanFormWeightNNReal]
  have hplain : Integrable (fun xi : ℝ => ‖(f : ℝ → ℂ) xi‖ ^ 2) volume :=
    ((MeasureTheory.Lp.memLp (ccmArchimedeanWeightedToL2 f)).integrable_norm_pow
      (by norm_num)).congr (by
        filter_upwards [ccmArchimedeanWeightedToL2_coeFn f] with xi hxi
        rw [hxi])
  exact (hweighted.add (hplain.const_mul c)).congr
    (Filter.Eventually.of_forall fun xi => (hpoint xi).symm)

theorem integrable_routeUArchimedean_source
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    Integrable (fun x : ℝ => gammaHardyPhaseRate x *
      ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2) := by
  let g : SoninL2 := suzukiHlogWeightedToL2 f.1
  let q := routeUToCCMFormVector a f
  have hq := integrable_two_gammaHardyPhaseRate_mul_norm_sq q.1
  have hcoe := ccmArchimedeanWeightedToL2_coeFn q.1
  rw [routeUToCCMFormVector_spectral] at hcoe
  have hdil := dilation_ae routeUCCMScale routeUCCMScale_pos g
  have hsqrt : ‖(Real.sqrt routeUCCMScale : ℂ)‖ ^ 2 = routeUCCMScale := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg routeUCCMScale),
      Real.sq_sqrt routeUCCMScale_pos.le]
  have hscaled : Integrable (fun xi : ℝ =>
      2 * routeUCCMScale *
        (gammaHardyPhaseRate (routeUCCMScale * xi) *
          ‖g (routeUCCMScale * xi)‖ ^ 2)) := by
    refine hq.congr ?_
    filter_upwards [hcoe, hdil] with xi hqxi hdilxi
    rw [← hqxi, hdilxi, norm_mul, mul_pow, hsqrt]
    rw [show 2 * Real.pi = routeUCCMScale by rfl]
    ring
  have hcomp : Integrable (fun xi : ℝ =>
      gammaHardyPhaseRate (routeUCCMScale * xi) *
        ‖g (routeUCCMScale * xi)‖ ^ 2) := by
    have h := hscaled.const_mul (2 * routeUCCMScale)⁻¹
    refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
    field_simp [routeUCCMScale, Real.pi_ne_zero]
  change Integrable (fun x : ℝ => gammaHardyPhaseRate x * ‖g x‖ ^ 2)
  exact (integrable_comp_mul_left_iff
    (fun x : ℝ => gammaHardyPhaseRate x * ‖g x‖ ^ 2)
    routeUCCMScale_pos.ne').mp hcomp

theorem integrable_routeUCosine_source
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) (h : ℝ) :
    Integrable (fun x : ℝ =>
      ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 *
        Real.cos (x * h)) := by
  have hplain : Integrable (fun x : ℝ =>
      ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2) :=
    (MeasureTheory.Lp.memLp (suzukiHlogWeightedToL2 f.1)).integrable_norm_pow
      (by norm_num)
  refine hplain.mul_bdd (c := 1) ?_ ?_
  · fun_prop
  · filter_upwards with x
    simpa using Real.abs_cos_le_one (x * h)

/-- The unscaled closed Route-U source is exactly its literal hard-edge line density plus its
polar carrier. No smooth-core approximation remains. -/
theorem routeUClosedSourceQuadratic_eq_density
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    routeUClosedSourceQuadratic a f =
      (∫ x : ℝ,
        routeUHardEdgeDensity (routeUCCMScaledAperture a).1 x *
          ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2) +
        (routeUCCMScale / 2) * routeUClosedPolarQuadratic a f := by
  let S := Finset.Icc 2
    (routeUHardEdgeFrequencyBound (routeUCCMScaledAperture a).1)
  let g : SoninL2 := suzukiHlogWeightedToL2 f.1
  have harch : Integrable (fun x : ℝ =>
      gammaHardyPhaseRate x * ‖g x‖ ^ 2) :=
    integrable_routeUArchimedean_source a f
  have hcos (n : ℕ) : Integrable (fun x : ℝ =>
      ‖g x‖ ^ 2 * Real.cos (x * Real.log n)) :=
    integrable_routeUCosine_source a f (Real.log n)
  have hterm (n : ℕ) : Integrable (fun x : ℝ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        (‖g x‖ ^ 2 * Real.cos (x * Real.log n))) :=
    (hcos n).const_mul _
  have hsum : Integrable (fun x : ℝ =>
      ∑ n ∈ S,
        ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          (‖g x‖ ^ 2 * Real.cos (x * Real.log n))) :=
    integrable_finsetSum S fun n _ => hterm n
  have hdensity :
      (∫ x : ℝ,
        routeUHardEdgeDensity (routeUCCMScaledAperture a).1 x * ‖g x‖ ^ 2) =
        (∫ x : ℝ, gammaHardyPhaseRate x * ‖g x‖ ^ 2) -
          ∑ n ∈ S,
            ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
              ∫ x : ℝ, ‖g x‖ ^ 2 * Real.cos (x * Real.log n) := by
    rw [show (fun x : ℝ =>
        routeUHardEdgeDensity (routeUCCMScaledAperture a).1 x * ‖g x‖ ^ 2) =
      fun x : ℝ => gammaHardyPhaseRate x * ‖g x‖ ^ 2 -
        ∑ n ∈ S,
          ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
            (‖g x‖ ^ 2 * Real.cos (x * Real.log n)) by
      funext x
      rw [routeUHardEdgeDensity,
        routeUArchimedeanRate_eq_gammaHardyPhaseRate]
      dsimp [S]
      rw [sub_mul, Finset.sum_mul]
      apply congrArg
        (fun y : ℝ => gammaHardyPhaseRate x * ‖g x‖ ^ 2 - y)
      apply Finset.sum_congr rfl
      intro n hn
      ring]
    rw [integral_sub harch hsum, integral_finsetSum S
      (fun n _ => hterm n)]
    apply congrArg
      (fun y : ℝ => (∫ x : ℝ, gammaHardyPhaseRate x * ‖g x‖ ^ 2) - y)
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_const_mul]
  rw [routeUClosedSourceQuadratic]
  simp_rw [routeUHlog_translation_symm_eq_cosine]
  dsimp [g, S] at hdensity ⊢
  rw [hdensity]
  have hscale (n : ℕ) :
      (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (2 * ∫ x : ℝ,
            ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 *
              Real.cos (x * Real.log n)) =
        2 * (((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
          ∫ x : ℝ,
            ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 *
              Real.cos (x * Real.log n)) := by
    ring
  simp_rw [hscale]
  rw [← Finset.mul_sum]
  ring

theorem routeUToCCMFormVector_archimedean
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    (∫ xi : ℝ, 2 * gammaHardyPhaseRate (routeUCCMScale * xi) *
        ‖((routeUToCCMFormVector a f).1 : ℝ → ℂ) xi‖ ^ 2) =
      2 * ∫ x : ℝ, gammaHardyPhaseRate x *
        ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 := by
  have hcoe := ccmArchimedeanWeightedToL2_coeFn
    (routeUToCCMFormVector a f).1
  rw [routeUToCCMFormVector_spectral] at hcoe
  calc
    _ = ∫ xi : ℝ, 2 * gammaHardyPhaseRate (routeUCCMScale * xi) *
        ‖(dilation routeUCCMScale routeUCCMScale_pos
          (suzukiHlogWeightedToL2 f.1) : SoninL2) xi‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hcoe] with xi hxi
      rw [← hxi]
    _ = _ := integral_two_gammaHardyPhaseRate_dilation_routeUCCMScale
      (suzukiHlogWeightedToL2 f.1)

theorem routeUToCCMFormVector_archimedean_ccmNormalization
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
        ‖((routeUToCCMFormVector a f).1 : ℝ → ℂ) xi‖ ^ 2) =
      2 * ∫ x : ℝ, gammaHardyPhaseRate x *
        ‖(suzukiHlogWeightedToL2 f.1 : SoninL2) x‖ ^ 2 := by
  change (∫ xi : ℝ, 2 * gammaHardyPhaseRate (routeUCCMScale * xi) *
      ‖((routeUToCCMFormVector a f).1 : ℝ → ℂ) xi‖ ^ 2) = _
  exact routeUToCCMFormVector_archimedean a f

theorem routeUToCCMFormVector_translation
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) (h : ℝ) :
    let q := ccmArchimedeanFormToAperture (routeUCCMScaledAperture a)
      (routeUToCCMFormVector a f)
    let p := routeUHlogApertureVector a f
    inner ℂ (logTranslationCLM h q.1) q.1 =
      inner ℂ (logTranslationCLM (routeUCCMScale⁻¹ * h) p.1) p.1 := by
  dsimp only
  rw [ccmArchimedeanFormToAperture_routeUToCCMFormVector]
  change inner ℂ
      (logTranslationCLM h
        (dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos)
          (routeUHlogApertureVector a f).1))
      (dilation routeUCCMScale⁻¹ (inv_pos.mpr routeUCCMScale_pos)
        (routeUHlogApertureVector a f).1) = _
  exact inner_logTranslationCLM_dilation routeUCCMScale⁻¹
    (inv_pos.mpr routeUCCMScale_pos) h (routeUHlogApertureVector a f).1

theorem routeUToCCMFormVector_polar
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector (routeUCCMScaledAperture a) s)
        (ccmArchimedeanFormToAperture (routeUCCMScaledAperture a)
          (routeUToCCMFormVector a f)) =
      (Real.sqrt routeUCCMScale : ℂ) *
        inner ℂ (ccmPolarApertureVector a (routeUCCMScale * s))
          (routeUHlogApertureVector a f) := by
  rw [ccmArchimedeanFormToAperture_routeUToCCMFormVector]
  exact inner_routeUCCMPolar_scaled a s (routeUHlogApertureVector a f)

/-- Exact normalization bridge: the closed CCM source energy of the `2π`-scaled vector is twice
Route U's unscaled angular-frequency source energy. -/
theorem ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) =
      2 * routeUClosedSourceQuadratic a f := by
  have hsqrt :
      (Real.sqrt routeUCCMScale : ℂ) * (Real.sqrt routeUCCMScale : ℂ) =
        (routeUCCMScale : ℂ) := by
    norm_cast
    simpa [pow_two] using Real.sq_sqrt routeUCCMScale_pos.le
  have hpolar :
      (Real.sqrt routeUCCMScale : ℂ) *
            (starRingEnd ℂ)
              (inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (-1 / 2)))
                (routeUHlogApertureVector a f)) *
            ((Real.sqrt routeUCCMScale : ℂ) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (1 / 2)))
                (routeUHlogApertureVector a f)) +
        (Real.sqrt routeUCCMScale : ℂ) *
            (starRingEnd ℂ)
              (inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (1 / 2)))
                (routeUHlogApertureVector a f)) *
            ((Real.sqrt routeUCCMScale : ℂ) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (-1 / 2)))
                (routeUHlogApertureVector a f)) =
      (routeUCCMScale : ℂ) *
        ((starRingEnd ℂ)
              (inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (-1 / 2)))
                (routeUHlogApertureVector a f)) *
            inner ℂ (ccmPolarApertureVector a
              (routeUCCMScale * (1 / 2)))
              (routeUHlogApertureVector a f) +
          (starRingEnd ℂ)
              (inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (1 / 2)))
                (routeUHlogApertureVector a f)) *
            inner ℂ (ccmPolarApertureVector a
              (routeUCCMScale * (-1 / 2)))
              (routeUHlogApertureVector a f)) := by
    calc
      _ = ((Real.sqrt routeUCCMScale : ℂ) *
            (Real.sqrt routeUCCMScale : ℂ)) *
          ((starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (-1 / 2)))
                  (routeUHlogApertureVector a f)) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (1 / 2)))
                (routeUHlogApertureVector a f) +
            (starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (1 / 2)))
                  (routeUHlogApertureVector a f)) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (-1 / 2)))
                (routeUHlogApertureVector a f)) := by ring
      _ = _ := by rw [hsqrt]
  have hpolar_re :
      (↑(Real.sqrt routeUCCMScale) *
              (starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (-1 / 2)))
                  (routeUHlogApertureVector a f)) *
              (↑(Real.sqrt routeUCCMScale) *
                inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (1 / 2)))
                  (routeUHlogApertureVector a f)) +
          ↑(Real.sqrt routeUCCMScale) *
              (starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (1 / 2)))
                  (routeUHlogApertureVector a f)) *
              (↑(Real.sqrt routeUCCMScale) *
                inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (-1 / 2)))
                  (routeUHlogApertureVector a f))).re =
        routeUCCMScale *
          ((starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (-1 / 2)))
                  (routeUHlogApertureVector a f)) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (1 / 2)))
                (routeUHlogApertureVector a f) +
            (starRingEnd ℂ)
                (inner ℂ (ccmPolarApertureVector a
                  (routeUCCMScale * (1 / 2)))
                  (routeUHlogApertureVector a f)) *
              inner ℂ (ccmPolarApertureVector a
                (routeUCCMScale * (-1 / 2)))
                (routeUHlogApertureVector a f)).re := by
    rw [hpolar]
    simp
  unfold ccmRestrictedWeilSourceQuadratic routeUClosedSourceQuadratic
    routeUClosedPolarQuadratic
  dsimp only
  rw [routeUToCCMFormVector_archimedean_ccmNormalization]
  simp_rw [routeUToCCMFormVector_polar]
  simp_rw [routeUToCCMFormVector_translation]
  simp only [routeUHardEdgeFrequencyBound]
  have hneg (x : ℝ) : routeUCCMScale⁻¹ * -x =
      -(routeUCCMScale⁻¹ * x) := by ring
  simp_rw [hneg]
  simp only [map_mul, Complex.conj_ofReal]
  rw [hpolar_re]
  ring

/-- The forced `2π` normalization preserves the sign of the exact source quadratic pointwise. -/
theorem routeUClosedSourceQuadratic_nonneg_iff_ccm
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    0 ≤ routeUClosedSourceQuadratic a f ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) := by
  rw [ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector]
  constructor <;> intro h <;> nlinarith

theorem routeUClosedSourceQuadratic_pos_iff_ccm
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    0 < routeUClosedSourceQuadratic a f ↔
      0 < ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) := by
  rw [ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector]
  constructor <;> intro h <;> nlinarith

theorem routeUClosedSourceQuadratic_eq_zero_iff_ccm
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    routeUClosedSourceQuadratic a f = 0 ↔
      ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a)
        (routeUToCCMFormVector a f) = 0 := by
  rw [ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector]
  constructor <;> intro h <;> nlinarith

/-- Route U positivity at angular-frequency aperture `a` is exactly full CCM restricted-Weil
positivity at physical aperture `2π a`; the scaling map is onto, so this loses no test vectors. -/
theorem routeUClosedSourceQuadratic_nonnegative_everywhere_iff_ccm
    (a : SuzukiPositiveAperture) :
    (∀ f : SuzukiHlogFormDomain a, 0 ≤ routeUClosedSourceQuadratic a f) ↔
      ∀ q : CCMArchimedeanFormDomain (routeUCCMScaledAperture a),
        0 ≤ ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a) q := by
  constructor
  · intro h q
    obtain ⟨f, rfl⟩ := (routeUCCMFormEquiv a).surjective q
    exact (routeUClosedSourceQuadratic_nonneg_iff_ccm a f).mp (h f)
  · intro h f
    exact (routeUClosedSourceQuadratic_nonneg_iff_ccm a f).mpr
      (h (routeUToCCMFormVector a f))

/-- Counterexamples also transport in both directions: the Route U wall is exactly the CCM wall,
not a positivity problem on a smaller privileged class. -/
theorem routeUClosedSourceQuadratic_negative_exists_iff_ccm
    (a : SuzukiPositiveAperture) :
    (∃ f : SuzukiHlogFormDomain a, routeUClosedSourceQuadratic a f < 0) ↔
      ∃ q : CCMArchimedeanFormDomain (routeUCCMScaledAperture a),
        ccmRestrictedWeilSourceQuadratic (routeUCCMScaledAperture a) q < 0 := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨routeUToCCMFormVector a f, ?_⟩
    rw [ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector]
    nlinarith
  · rintro ⟨q, hq⟩
    obtain ⟨f, rfl⟩ := (routeUCCMFormEquiv a).surjective q
    refine ⟨f, ?_⟩
    rw [routeUCCMFormEquiv_apply] at hq
    rw [ccmRestrictedWeilSourceQuadratic_routeUToCCMFormVector] at hq
    nlinarith

end RHTower
