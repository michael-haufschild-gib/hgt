import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaMixedJump
import GaloisForLFunctions.HTGeometry.ConductorHankelBound
import GaloisForLFunctions.HTGeometry.SchurKernelOperator

import GaloisForLFunctions.RHTower.SuzukiPositiveHalfLine
import GaloisForLFunctions.RHTower.CCMActualHeadQuantileGammaChiSquareProducer
import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.RHTower.SoninApertureStrictEigen

/-!
# Actual Gamma interaction across sharp aperture boundaries

The literal Gamma Hankel kernel is bounded on positive-half-line L2. Absolute
integrability and a measure-preserving shear identify its full complex pairing
with the mixed Gamma translation-jump form. Translation and reflection give
both exterior actions for every actual aperture-supported L2 source.

No smoothness or full Gamma multiplier-domain premise is used in the boundary
identities. Assembling these actions with the actual interior ground forcing
and proving global multiplier-domain admission is a separate remaining step.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower


theorem ccmGammaTranslationDensity_le_carleman {h : ℝ} (hh : 0 < h) :
    ccmGammaTranslationDensity h ≤ 2 / h := by
  have hden : 0 < 1 - Real.exp (-(2*h)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hexp : Real.exp (-(2*h)) ≤ Real.exp (-(h/2)) :=
    Real.exp_le_exp.mpr (by linarith)
  have ht := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h/2))
    (Real.exp_pos (-(h/2))).le
  have hid : Real.exp (h/2) * Real.exp (-(h/2)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hid] at ht
  unfold ccmGammaTranslationDensity
  apply (div_le_div_iff₀ hden hh).mpr
  nlinarith

private theorem density_meas : Measurable ccmGammaTranslationDensity := by
  unfold ccmGammaTranslationDensity
  fun_prop

theorem lintegral_ccmGammaBoundary_sq_le {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ s in Ioi (0:ℝ),
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * F t)^2) ≤
      ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ t in Ioi (0:ℝ), F t^2 := by
  have h := lintegral_dominatedHankel_sq_le
    (k := fun r => ccmGammaTranslationDensity r / 2)
    (fun r hr => by
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
      calc
        ccmGammaTranslationDensity r ≤ 2/r := ccmGammaTranslationDensity_le_carleman hr
        _ = (1/r)*2 := by ring) hF
  have hf (s : ℝ) :
      (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * F t) =
      2 * ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (ccmGammaTranslationDensity (s+t)/2) * F t := by
    rw [← lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞) ≠ ⊤)]
    apply lintegral_congr
    intro t
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
    congr 2
    ring
  simp_rw [hf, mul_pow]
  rw [lintegral_const_mul' _ _ (by norm_num : (2:ℝ≥0∞)^2 ≠ ⊤)]
  refine (mul_le_mul' le_rfl h).trans_eq ?_
  rw [← mul_assoc]
  congr 1
  rw [show (2:ℝ≥0∞)^2 = ENNReal.ofReal (4:ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

def ccmGammaBoundaryAction (f : ℝ → ℂ) (s : ℝ) : ℂ :=
    ∫ t in Ioi (0:ℝ), (ccmGammaTranslationDensity (s+t):ℂ) * f t

private theorem boundary_meas {f : ℝ → ℂ} (hf : Measurable f) :
    StronglyMeasurable (ccmGammaBoundaryAction f) := by
  apply StronglyMeasurable.integral_prod_right
  exact ((Complex.measurable_ofReal.comp
    (density_meas.comp (measurable_fst.add measurable_snd))).mul
      (hf.comp measurable_snd)).stronglyMeasurable

private theorem boundary_enorm_le (f : ℝ → ℂ) {s : ℝ} (hs : 0 < s) :
    ‖ccmGammaBoundaryAction f s‖ₑ ≤
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * ‖f t‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ccmGammaTranslationDensity_pos (by linarith [show 0<t from ht]))]

private theorem boundary_sq_le {f : ℝ → ℂ} (hf : Measurable f) :
    (∫⁻ s in Ioi (0:ℝ), ‖ccmGammaBoundaryAction f s‖ₑ^2) ≤
      ENNReal.ofReal ((2*Real.pi)^2) * ∫⁻ t in Ioi (0:ℝ), ‖f t‖ₑ^2 := by
  refine (setLIntegral_mono' measurableSet_Ioi (fun s hs =>
    pow_le_pow_left' (boundary_enorm_le f hs) 2)).trans ?_
  exact lintegral_ccmGammaBoundary_sq_le hf.enorm

theorem eLpNorm_ccmGammaBoundaryAction_le {f : ℝ → ℂ} (hf : Measurable f) :
    eLpNorm (ccmGammaBoundaryAction f) 2 (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (2*Real.pi) * eLpNorm f 2 (volume.restrict (Ioi 0)) := by
  rw [SchurKernel.eLpNorm_two_eq, SchurKernel.eLpNorm_two_eq]
  have h := ENNReal.rpow_le_rpow (boundary_sq_le hf) (by norm_num : (0:ℝ) ≤ 1/2)
  refine h.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_ccmGammaBoundaryAction
    (f : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) :
    MemLp (ccmGammaBoundaryAction f) 2 (volume.restrict (Ioi (0:ℝ))) :=
  ⟨(boundary_meas (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable,
    (eLpNorm_ccmGammaBoundaryAction_le (Lp.stronglyMeasurable f).measurable).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f))⟩

private theorem boundary_ae_integrable
    (f : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) :
    ∀ᵐ s ∂volume.restrict (Ioi (0:ℝ)),
      IntegrableOn (fun t => (ccmGammaTranslationDensity (s+t):ℂ) * f t) (Ioi (0:ℝ)) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  let K : ℝ → ℝ≥0∞ := fun s =>
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * ‖f t‖ₑ
  have hK : Measurable K :=
    ((ENNReal.measurable_ofReal.comp
      (density_meas.comp (measurable_fst.add measurable_snd))).mul
        (hf.enorm.comp measurable_snd)).lintegral_prod_right'
  have hfin : (∫⁻ s in Ioi (0:ℝ), K s^2) < ⊤ := by
    refine (lintegral_ccmGammaBoundary_sq_le hf.enorm).trans_lt ?_
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    rw [← SchurKernel.eLpNorm_two_sq]
    exact ENNReal.pow_lt_top (Lp.eLpNorm_lt_top f)
  filter_upwards [ae_lt_top (hK.pow_const 2) hfin.ne,
    ae_restrict_mem measurableSet_Ioi] with s hs hsp
  refine ⟨((Complex.measurable_ofReal.comp
    (density_meas.comp (measurable_const.add measurable_id))).mul hf).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have heq : (∫⁻ t in Ioi (0:ℝ),
      ‖(ccmGammaTranslationDensity (s+t):ℂ) * f t‖ₑ) = K s := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [enorm_mul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ccmGammaTranslationDensity_pos (by linarith [show 0<s from hsp,
        show 0<t from ht]))]
  rw [heq]
  by_contra hn
  have : K s = ⊤ := top_le_iff.mp (not_lt.mp hn)
  rw [this] at hs
  simp at hs

private theorem boundary_add
    (f g : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) :
    ccmGammaBoundaryAction (f+g : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) =ᵐ[
      volume.restrict (Ioi (0:ℝ))] ccmGammaBoundaryAction f + ccmGammaBoundaryAction g := by
  filter_upwards [boundary_ae_integrable f, boundary_ae_integrable g] with s hf hg
  simp only [ccmGammaBoundaryAction, Pi.add_apply]
  rw [← integral_add hf hg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with t ht
  rw [ht, Pi.add_apply, mul_add]

private theorem boundary_smul (c : ℂ)
    (f : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) :
    ccmGammaBoundaryAction (c • f : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) =
      c • ccmGammaBoundaryAction f := by
  funext s
  simp only [ccmGammaBoundaryAction, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with t ht
  rw [ht, Pi.smul_apply, smul_eq_mul]
  ring

/-- The literal one-endpoint Gamma transfer on positive-half-line L2. -/
def ccmGammaBoundaryCLM :
    Lp ℂ 2 (volume.restrict (Ioi (0:ℝ))) →L[ℂ]
      Lp ℂ 2 (volume.restrict (Ioi (0:ℝ))) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_ccmGammaBoundaryAction f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact (MemLp.toLp_eq_toLp_iff _ _).mpr (boundary_add f g)
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        congr 1
        exact boundary_smul c f }
    (2*Real.pi) (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (Lp.eLpNorm_ne_top f))
        (eLpNorm_ccmGammaBoundaryAction_le (Lp.stronglyMeasurable f).measurable)).trans_eq ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)])

theorem ccmGammaBoundaryCLM_coeFn
    (f : Lp ℂ 2 (volume.restrict (Ioi (0:ℝ)))) :
    (ccmGammaBoundaryCLM f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      ccmGammaBoundaryAction f :=
  (memLp_ccmGammaBoundaryAction f).coeFn_toLp

theorem norm_ccmGammaBoundaryCLM_le : ‖ccmGammaBoundaryCLM‖ ≤ 2*Real.pi :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _




private theorem halfLine_norm_le (f : SoninL2) : ‖soninHalfLine f‖ ≤ ‖f‖ := by
  rw [soninHalfLine, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem translate_ae (a : ℝ) (f : SoninL2) :
    (logTranslationCLM a f : ℝ → ℂ) =ᵐ[volume] fun x => f (x+a) := by
  exact Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving a)

private theorem reflected_translate_ae (a : ℝ) (f : SoninL2) :
    (l2Reflection (logTranslationCLM a f) : ℝ → ℂ) =ᵐ[volume] fun t => f (a-t) := by
  have ht := (translate_ae a f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [l2Reflection_ae (logTranslationCLM a f), ht] with t hr ht
  rw [hr]
  dsimp only [Function.comp_apply, neg_neg] at ht
  rw [ht]
  congr 1
  ring

/-- Exterior Gamma action in distance coordinates x=a+s, y=a-t. -/
def ccmGammaRightBoundaryTransfer (a : ℝ) (f : SoninL2) : SuzukiPositiveL2 :=
  ccmGammaBoundaryCLM (soninHalfLine (l2Reflection (logTranslationCLM a f)))

/-- Literal integral formula; a supported aperture input vanishes automatically for t>2a. -/
theorem ccmGammaRightBoundaryTransfer_coeFn (a : ℝ) (f : SoninL2) :
    (ccmGammaRightBoundaryTransfer a f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0:ℝ))]
      fun s => ∫ t in Ioi (0:ℝ), (ccmGammaTranslationDensity (s+t):ℂ) * f (a-t) := by
  have hin := (coeFn_soninHalfLine (l2Reflection (logTranslationCLM a f))).trans
    (ae_restrict_of_ae (reflected_translate_ae a f))
  refine (ccmGammaBoundaryCLM_coeFn _).trans (Eventually.of_forall fun s => ?_)
  unfold ccmGammaBoundaryAction
  apply integral_congr_ae
  filter_upwards [hin] with t ht
  rw [ht]

/-- The actual boundary transfer has a uniform L2 bound, including at a sharp endpoint. -/
theorem norm_ccmGammaRightBoundaryTransfer_le (a : ℝ) (f : SoninL2) :
    ‖ccmGammaRightBoundaryTransfer a f‖ ≤ 2*Real.pi*‖f‖ := by
  have hn : ‖l2Reflection (logTranslationCLM a f)‖ = ‖f‖ :=
    (l2ReflectionIsometry.norm_map _).trans
      ((MellinL2.additiveTranslationUnitary a).norm_map f)
  calc
    ‖ccmGammaRightBoundaryTransfer a f‖ ≤
        ‖ccmGammaBoundaryCLM‖ * ‖soninHalfLine (l2Reflection (logTranslationCLM a f))‖ :=
      ccmGammaBoundaryCLM.le_opNorm _
    _ ≤ (2*Real.pi) * ‖l2Reflection (logTranslationCLM a f)‖ :=
      mul_le_mul norm_ccmGammaBoundaryCLM_le (halfLine_norm_le _)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [hn]


private theorem boundary_triple_lt_top (f g : SuzukiPositiveL2) :
    (∫⁻ s in Ioi (0:ℝ), ‖g s‖ₑ * ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * ‖f t‖ₑ) < ⊤ := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hρ : Measurable ccmGammaTranslationDensity := by
    unfold ccmGammaTranslationDensity
    fun_prop
  have hK : Measurable fun s => ∫⁻ t in Ioi (0:ℝ),
      ENNReal.ofReal (ccmGammaTranslationDensity (s+t)) * ‖f t‖ₑ :=
    ((ENNReal.measurable_ofReal.comp
      (hρ.comp (measurable_fst.add measurable_snd))).mul
        (hf.enorm.comp measurable_snd)).lintegral_prod_right'
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi (0:ℝ)))
    Real.HolderConjugate.two_two hg.enorm.aemeasurable hK.aemeasurable
  refine h.trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · have hnorm := Lp.eLpNorm_lt_top g
    rw [SchurKernel.eLpNorm_two_eq] at hnorm
    simpa only [ENNReal.rpow_two] using hnorm
  · simp only [ENNReal.rpow_two]
    have hfin := (lintegral_ccmGammaBoundary_sq_le hf.enorm).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        rw [← SchurKernel.eLpNorm_two_sq]
        exact ENNReal.pow_lt_top (Lp.eLpNorm_lt_top f)))
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-- Absolute integrability of the actual cross-boundary Gamma form on arbitrary L2 inputs. -/
theorem integrable_ccmGammaBoundary_pair (f g : SuzukiPositiveL2) :
    Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (g p.1) *
      (ccmGammaTranslationDensity (p.1+p.2):ℂ) * f p.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hρ : Measurable ccmGammaTranslationDensity := by
    unfold ccmGammaTranslationDensity
    fun_prop
  have hm : Measurable fun p : ℝ × ℝ => (starRingEnd ℂ) (g p.1) *
      (ccmGammaTranslationDensity (p.1+p.2):ℂ) * f p.2 :=
    ((Complex.continuous_conj.measurable.comp (hg.comp measurable_fst)).mul
      (Complex.measurable_ofReal.comp (hρ.comp (measurable_fst.add measurable_snd)))).mul
        (hf.comp measurable_snd)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hm.enorm.aemeasurable]
  refine (le_of_eq ?_).trans_lt (boundary_triple_lt_top f g)
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [← lintegral_const_mul' _ _ (by simp : ‖g s‖ₑ ≠ ⊤)]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [enorm_mul, enorm_mul, RCLike.enorm_conj, ← ofReal_norm (ccmGammaTranslationDensity (s+t):ℂ),
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (ccmGammaTranslationDensity_pos (by linarith [show 0<s from hs,
      show 0<t from ht]))]
  ring

/-- The boundary operator realizes the full complex, absolutely convergent kernel pairing. -/
theorem inner_ccmGammaBoundaryCLM (f g : SuzukiPositiveL2) :
    inner ℂ g (ccmGammaBoundaryCLM f) =
      ∫ s in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ),
        (starRingEnd ℂ) (g s) * (ccmGammaTranslationDensity (s+t):ℂ) * f t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmGammaBoundaryCLM_coeFn f] with s hs
  rw [hs, RCLike.inner_apply, ccmGammaBoundaryAction, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with t
  ring




private abbrev positiveFun (f : SuzukiPositiveL2) := suzukiPositiveZeroExtensionFun f

private def boundaryWholeKernel (f g : SuzukiPositiveL2) (p : ℝ × ℝ) : ℂ :=
  (starRingEnd ℂ) (positiveFun g p.1) *
    (ccmGammaTranslationDensity (p.1+p.2):ℂ) * positiveFun f p.2

private theorem boundaryWholeKernel_indicator (f g : SuzukiPositiveL2) :
    boundaryWholeKernel f g =
      ((Ioi (0:ℝ)) ×ˢ (Ioi (0:ℝ))).indicator
        (fun p : ℝ × ℝ => (starRingEnd ℂ) (g p.1) *
          (ccmGammaTranslationDensity (p.1+p.2):ℂ) * f p.2) := by
  funext p
  by_cases hs : 0 < p.1 <;> by_cases ht : 0 < p.2 <;>
    simp [boundaryWholeKernel, positiveFun, suzukiPositiveZeroExtensionFun,
      Set.mem_prod, hs, ht]

private theorem integrable_boundaryWholeKernel (f g : SuzukiPositiveL2) :
    Integrable (boundaryWholeKernel f g) (volume.prod volume) := by
  rw [boundaryWholeKernel_indicator, integrable_indicator_iff
    (measurableSet_Ioi.prod measurableSet_Ioi), IntegrableOn, ← Measure.prod_restrict]
  exact integrable_ccmGammaBoundary_pair f g

private theorem boundaryWholeKernel_integral (f g : SuzukiPositiveL2) :
    (∫ s, ∫ t, boundaryWholeKernel f g (s,t)) = inner ℂ g (ccmGammaBoundaryCLM f) := by
  rw [← integral_prod _ (integrable_boundaryWholeKernel f g),
    boundaryWholeKernel_indicator, integral_indicator
      (measurableSet_Ioi.prod measurableSet_Ioi), ← Measure.prod_restrict,
    integral_prod _ (integrable_ccmGammaBoundary_pair f g), inner_ccmGammaBoundaryCLM]

private def boundaryShiftKernel (f g : SuzukiPositiveL2) (p : ℝ × ℝ) : ℂ :=
  (starRingEnd ℂ) (positiveFun g (p.1-p.2)) *
    (ccmGammaTranslationDensity p.1:ℂ) * positiveFun f p.2

private theorem integrable_boundaryShiftKernel (f g : SuzukiPositiveL2) :
    Integrable (boundaryShiftKernel f g) (volume.prod volume) := by
  have h := (measurePreserving_sub_prod (volume : Measure ℝ) volume).integrable_comp_of_integrable (integrable_boundaryWholeKernel f g)
  change Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (positiveFun g (p.1-p.2)) *
    (ccmGammaTranslationDensity p.1:ℂ) * positiveFun f p.2) (volume.prod volume)
  simpa only [Function.comp_def, boundaryWholeKernel, sub_add_cancel] using h

private theorem boundaryShiftKernel_integral (f g : SuzukiPositiveL2) :
    (∫ h, ∫ t, boundaryShiftKernel f g (h,t)) = inner ℂ g (ccmGammaBoundaryCLM f) := by
  rw [integral_integral_swap (f := fun h t => boundaryShiftKernel f g (h,t))
    (integrable_boundaryShiftKernel f g)]
  have hsub (t : ℝ) : (∫ h, boundaryShiftKernel f g (h,t)) =
      ∫ s, boundaryWholeKernel f g (s,t) := by
    convert integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun s => boundaryWholeKernel f g (s,t)) t using 1
    simp only [boundaryWholeKernel, boundaryShiftKernel, sub_add_cancel]
  simp_rw [hsub]
  rw [integral_integral_swap (f := fun t s => boundaryWholeKernel f g (s,t))
    (integrable_boundaryWholeKernel f g).swap,
    boundaryWholeKernel_integral]

private theorem translated_positive_ae (h : ℝ) (g : SuzukiPositiveL2) :
    (logTranslationCLM h (suzukiPositiveZeroExtension g) : ℝ → ℂ) =ᵐ[volume]
      fun x => positiveFun g (x+h) := by
  refine (translate_ae h _).trans ?_
  exact (suzukiPositiveZeroExtension_ae g).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae

private theorem reflected_positive_ae (f : SuzukiPositiveL2) :
    (l2Reflection (suzukiPositiveZeroExtension f) : ℝ → ℂ) =ᵐ[volume]
      fun x => positiveFun f (-x) := by
  refine (l2Reflection_ae _).trans ?_
  exact (suzukiPositiveZeroExtension_ae f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae

private theorem inner_translated_positive_reflected (h : ℝ) (f g : SuzukiPositiveL2) :
    inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
      (l2Reflection (suzukiPositiveZeroExtension f)) =
        ∫ t, (starRingEnd ℂ) (positiveFun g (h-t)) * positiveFun f t := by
  rw [L2.inner_def]
  rw [← integral_neg_eq_self (fun x => inner ℂ
    (logTranslationCLM h (suzukiPositiveZeroExtension g) x)
    (l2Reflection (suzukiPositiveZeroExtension f) x)) volume]
  have ht := (translated_positive_ae h g).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hr := (reflected_positive_ae f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  apply integral_congr_ae
  filter_upwards [ht, hr] with t ht hr
  dsimp only [Function.comp_apply] at ht hr
  rw [ht, hr, neg_neg, RCLike.inner_apply]
  rw [show -t+h = h-t by ring]
  ring

/-- Absolute integrability across a sharp boundary for every pair of L2 inputs. -/
theorem integrableOn_ccmGamma_oppositeHalfLines (f g : SuzukiPositiveL2) :
    IntegrableOn (fun h => (ccmGammaTranslationDensity h:ℂ) *
      inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
        (l2Reflection (suzukiPositiveZeroExtension f))) (Ioi (0:ℝ)) := by
  have h := (integrable_boundaryShiftKernel f g).integral_prod_left
  have heq : (fun h => ∫ t, boundaryShiftKernel f g (h,t)) =
      fun h => (ccmGammaTranslationDensity h:ℂ) *
        inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
          (l2Reflection (suzukiPositiveZeroExtension f)) := by
    funext h
    rw [inner_translated_positive_reflected, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [boundaryShiftKernel]
    ring
  rw [heq] at h
  exact h.integrableOn

/-- The exact Hankel identity for the actual Gamma interaction across a sharp endpoint. -/
theorem integral_ccmGamma_oppositeHalfLines (f g : SuzukiPositiveL2) :
    (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h:ℂ) *
      inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
        (l2Reflection (suzukiPositiveZeroExtension f))) =
      inner ℂ g (ccmGammaBoundaryCLM f) := by
  have heq (h : ℝ) : (ccmGammaTranslationDensity h:ℂ) *
      inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
        (l2Reflection (suzukiPositiveZeroExtension f)) =
      ∫ t, boundaryShiftKernel f g (h,t) := by
    rw [inner_translated_positive_reflected, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [boundaryShiftKernel]
    ring
  simp_rw [heq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, boundaryShiftKernel_integral]
  intro h hh
  apply integral_eq_zero_of_ae
  filter_upwards [] with t
  have hh0 : h ≤ 0 := le_of_not_gt hh
  by_cases ht : 0 < t
  · have hs : ¬ 0 < h-t := by linarith
    simp [boundaryShiftKernel, positiveFun, suzukiPositiveZeroExtensionFun, hs]
  · simp [boundaryShiftKernel, positiveFun, suzukiPositiveZeroExtensionFun, ht]


private theorem translated_reflected_positive_ae (h : ℝ) (f : SuzukiPositiveL2) :
    (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f)) : ℝ → ℂ) =ᵐ[volume]
      fun x => positiveFun f (-(x+h)) := by
  refine (translate_ae h _).trans ?_
  exact (reflected_positive_ae f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae

private theorem inner_positive_translated_reflected_eq_zero {h : ℝ} (hh : 0 ≤ h)
    (f g : SuzukiPositiveL2) :
    inner ℂ (suzukiPositiveZeroExtension g)
      (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f))) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [suzukiPositiveZeroExtension_ae g,
    translated_reflected_positive_ae h f] with x hg hf
  rw [hg, hf, RCLike.inner_apply]
  by_cases hx : 0 < x
  · have hnx : ¬0 < -(x+h) := by linarith
    rw [show positiveFun f (-(x+h)) = 0 from Set.indicator_of_notMem hnx _]
    simp
  · rw [show suzukiPositiveZeroExtensionFun g x = 0 from Set.indicator_of_notMem hx _]
    simp

private theorem opposite_jump_pair {h : ℝ} (hh : 0 ≤ h) (f g : SuzukiPositiveL2) :
    inner ℂ
      (logTranslationCLM h (suzukiPositiveZeroExtension g) - suzukiPositiveZeroExtension g)
      (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f)) -
        l2Reflection (suzukiPositiveZeroExtension f)) =
      -inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
        (l2Reflection (suzukiPositiveZeroExtension f)) := by
  have h0 := inner_positive_translated_reflected_eq_zero (h:=0) le_rfl f g
  have heq : logTranslationCLM 0 = (1 : SoninL2 →L[ℂ] SoninL2) := by
    ext q
    filter_upwards [translate_ae 0 q] with x hx
    simpa using hx
  rw [heq, one_apply_eq_self] at h0
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  have hiso := (MellinL2.additiveTranslationUnitary h).inner_map_map
    (suzukiPositiveZeroExtension g) (l2Reflection (suzukiPositiveZeroExtension f))
  change inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
      (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f))) = _ at hiso
  rw [hiso, h0, inner_positive_translated_reflected_eq_zero hh f g]
  ring

/-- The complete Gamma jump interaction across a sharp endpoint is absolutely integrable. -/
theorem integrableOn_ccmGamma_oppositeJump (f g : SuzukiPositiveL2) :
    IntegrableOn (fun h => (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (suzukiPositiveZeroExtension g) - suzukiPositiveZeroExtension g)
      (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f)) -
        l2Reflection (suzukiPositiveZeroExtension f))) (Ioi (0:ℝ)) := by
  refine (integrableOn_ccmGamma_oppositeHalfLines f g).neg.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [opposite_jump_pair (le_of_lt hh), mul_neg]
  rfl

/-- Exact full mixed Gamma form across a sharp boundary, without a regularity premise. -/
theorem integral_ccmGamma_oppositeJump (f g : SuzukiPositiveL2) :
    (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (suzukiPositiveZeroExtension g) - suzukiPositiveZeroExtension g)
      (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension f)) -
        l2Reflection (suzukiPositiveZeroExtension f))) =
      -inner ℂ g (ccmGammaBoundaryCLM f) := by
  calc
    _ = ∫ h in Ioi (0:ℝ), -((ccmGammaTranslationDensity h:ℂ) *
        inner ℂ (logTranslationCLM h (suzukiPositiveZeroExtension g))
          (l2Reflection (suzukiPositiveZeroExtension f))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      rw [opposite_jump_pair (le_of_lt hh), mul_neg]
    _ = _ := by rw [integral_neg, integral_ccmGamma_oppositeHalfLines]



private theorem rightBoundary_reconstruction (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    l2Reflection (suzukiPositiveZeroExtension
      (soninHalfLine (l2Reflection (logTranslationCLM a.1 f.1)))) =
      logTranslationCLM a.1 f.1 := by
  let q := l2Reflection (logTranslationCLM a.1 f.1)
  have hext : suzukiPositiveZeroExtension (soninHalfLine q) = q := by
    apply Lp.ext
    have hhalf := (ae_restrict_iff' measurableSet_Ioi).mp (coeFn_soninHalfLine q)
    have hsupport := indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1
    rw [indicatorCutoff_suzukiApertureHilbert a f] at hsupport
    have hs := hsupport.comp_tendsto
      ((MellinL2.realTranslation_measurePreserving a.1).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
    filter_upwards [suzukiPositiveZeroExtension_ae (soninHalfLine q), hhalf,
      reflected_translate_ae a.1 f.1, hs, volume.ae_ne (0:ℝ)] with t hz hh hq hs ht
    rw [hz]
    change (Ioi (0:ℝ)).indicator (fun x => soninHalfLine q x) t = q t
    by_cases hpos : 0<t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0:ℝ) from hpos)]
      exact hh hpos
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0:ℝ) from hpos)]
      change q t = f.1 (a.1-t) at hq
      rw [hq]
      dsimp only [Function.comp_apply] at hs
      change f.1 (-t+a.1) = (centralInterval a.1).indicator (fun x => f.1 x) (-t+a.1) at hs
      have hn : -t+a.1 ∉ centralInterval a.1 := by
        intro hm
        have hb : -t+a.1 ≤ a.1 := hm.2
        have he : t=0 := by linarith
        exact ht he
      rw [Set.indicator_of_notMem hn, show -t+a.1=a.1-t by ring] at hs
      exact hs.symm
  have h := congrArg l2Reflection hext
  rw [l2Reflection_involutive] at h
  exact h

private theorem mixedJump_translate (a h : ℝ) (f g : SoninL2) :
    inner ℂ (logTranslationCLM h (logTranslationCLM a f) - logTranslationCLM a f)
      (logTranslationCLM h (logTranslationCLM a g) - logTranslationCLM a g) =
      inner ℂ (logTranslationCLM h f-f) (logTranslationCLM h g-g) := by
  have hcomm (v : SoninL2) : logTranslationCLM h (logTranslationCLM a v) =
      logTranslationCLM a (logTranslationCLM h v) := by
    rw [logTranslationCLM_add_apply, logTranslationCLM_add_apply, add_comm h a]
  rw [hcomm f, hcomm g, ← map_sub, ← map_sub]
  exact (MellinL2.additiveTranslationUnitary a).inner_map_map _ _

private theorem apertureRightJump_eq (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (g : SuzukiPositiveL2) (h : ℝ) :
    inner ℂ
      (logTranslationCLM h (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) -
        logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))
      (logTranslationCLM h f.1-f.1) =
      inner ℂ
        (logTranslationCLM h (suzukiPositiveZeroExtension g) - suzukiPositiveZeroExtension g)
        (logTranslationCLM h (l2Reflection (suzukiPositiveZeroExtension
          (soninHalfLine (l2Reflection (logTranslationCLM a.1 f.1))))) -
          l2Reflection (suzukiPositiveZeroExtension
            (soninHalfLine (l2Reflection (logTranslationCLM a.1 f.1)))) ) := by
  have hinv : logTranslationCLM a.1 (logTranslationCLM (-a.1)
      (suzukiPositiveZeroExtension g)) = suzukiPositiveZeroExtension g := by
    have heq := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 =>
      T (suzukiPositiveZeroExtension g)) (logTranslationCLM_neg_mul (-a.1))
    simpa using heq
  rw [← mixedJump_translate a.1 h, hinv, rightBoundary_reconstruction]

/-- The actual aperture source has the constructed right boundary action as its complete
mixed Gamma interaction against arbitrary exterior L2 tests. -/
theorem integral_ccmGamma_apertureRightBoundary (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (g : SuzukiPositiveL2) :
    (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) -
        logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))
      (logTranslationCLM h f.1-f.1)) =
      -inner ℂ g (ccmGammaRightBoundaryTransfer a.1 f.1) := by
  simp_rw [apertureRightJump_eq]
  exact integral_ccmGamma_oppositeJump _ g

/-- The right exterior mixed Gamma form is absolutely integrable for the actual aperture
source, with no smoothness or global multiplier-domain assumption. -/
theorem integrableOn_ccmGamma_apertureRightBoundary (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (g : SuzukiPositiveL2) :
    IntegrableOn (fun h => (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) -
        logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))
      (logTranslationCLM h f.1-f.1)) (Ioi (0:ℝ)) := by
  simp_rw [apertureRightJump_eq]
  exact integrableOn_ccmGamma_oppositeJump _ g



private theorem mixedJump_reflection (h : ℝ) (f g : SoninL2) :
    inner ℂ (logTranslationCLM h (l2Reflection f)-l2Reflection f)
      (logTranslationCLM h (l2Reflection g)-l2Reflection g) =
      inner ℂ (logTranslationCLM h f-f) (logTranslationCLM h g-g) := by
  have href (v : SoninL2) : logTranslationCLM h (l2Reflection v) =
      l2Reflection (logTranslationCLM (-h) v) := by
    change MellinL2.additiveTranslationUnitary h (l2Reflection v) =
      l2Reflection (MellinL2.additiveTranslationUnitary (-h) v)
    simpa only [neg_neg] using (MellinL2.l2Reflection_additiveTranslation (-h) v).symm
  rw [href f, href g]
  change inner ℂ (l2ReflectionIsometry (logTranslationCLM (-h) f)-l2ReflectionIsometry f)
    (l2ReflectionIsometry (logTranslationCLM (-h) g)-l2ReflectionIsometry g) = _
  rw [← map_sub, ← map_sub, l2ReflectionIsometry.inner_map_map]
  have hneg (v : SoninL2) : logTranslationCLM (-h) v-v =
      -logTranslationCLM (-h) (logTranslationCLM h v-v) := by
    have hinv := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T v)
      (logTranslationCLM_neg_mul h)
    change logTranslationCLM (-h) (logTranslationCLM h v) = v at hinv
    rw [map_sub, hinv]
    abel
  rw [hneg f, hneg g, inner_neg_neg]
  exact (MellinL2.additiveTranslationUnitary (-h)).inner_map_map _ _

/-- The left exterior Gamma action in reflected distance coordinates. -/
def ccmGammaLeftBoundaryTransfer (a : ℝ) (f : SoninL2) : SuzukiPositiveL2 :=
  ccmGammaRightBoundaryTransfer a (l2Reflection f)

/-- Exact left exterior mixed Gamma form for every actual aperture vector. -/
theorem integral_ccmGamma_apertureLeftBoundary (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (g : SuzukiPositiveL2) :
    (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (l2Reflection
        (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))) -
          l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)))
      (logTranslationCLM h f.1-f.1)) =
      -inner ℂ g (ccmGammaLeftBoundaryTransfer a.1 f.1) := by
  let rf : suzukiApertureHilbert a :=
    ⟨l2Reflection f.1, l2Reflection_mem_centralPhysicalForbidden f.property⟩
  have hm (h : ℝ) := mixedJump_reflection h
    (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) (l2Reflection f.1)
  simp only [l2Reflection_involutive] at hm
  simp_rw [hm]
  exact integral_ccmGamma_apertureRightBoundary a rf g

/-- Absolute convergence of the left exterior interaction, without a regularity premise. -/
theorem integrableOn_ccmGamma_apertureLeftBoundary (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (g : SuzukiPositiveL2) :
    IntegrableOn (fun h => (ccmGammaTranslationDensity h:ℂ) * inner ℂ
      (logTranslationCLM h (l2Reflection
        (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))) -
          l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)))
      (logTranslationCLM h f.1-f.1)) (Ioi (0:ℝ)) := by
  let rf : suzukiApertureHilbert a :=
    ⟨l2Reflection f.1, l2Reflection_mem_centralPhysicalForbidden f.property⟩
  have hm (h : ℝ) := mixedJump_reflection h
    (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) (l2Reflection f.1)
  simp only [l2Reflection_involutive] at hm
  simp_rw [hm]
  exact integrableOn_ccmGamma_apertureRightBoundary a rf g

/-- Both actual exterior Gamma actions are bounded on L2. -/
theorem norm_ccmGammaLeftBoundaryTransfer_le (a : ℝ) (f : SoninL2) :
    ‖ccmGammaLeftBoundaryTransfer a f‖ ≤ 2*Real.pi*‖f‖ := by
  unfold ccmGammaLeftBoundaryTransfer
  have hn : ‖l2Reflection f‖ = ‖f‖ := l2ReflectionIsometry.norm_map f
  simpa only [hn] using norm_ccmGammaRightBoundaryTransfer_le a (l2Reflection f)

end RHTower
