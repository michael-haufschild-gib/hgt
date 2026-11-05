import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicAndWeilFormDomainsAgree
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaBoundaryPairing
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGammaMixedJump
import GaloisForLFunctions.HTGeometry.HardyPaleyWienerTransport

/-!
# Bounded exterior crossings of the complete Weil form

The complete Gamma form between an aperture source and an adjacent exterior
source is its actual half-line boundary transfer. Disjoint support removes
the mass term. The remaining prime and polar terms are the bounded physical
Weil remainder, so the full crossing has a width-independent L² bound.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy

/-- Restriction in distance coordinates reconstructs every source supported to the right of a boundary. -/
theorem rightExterior_reconstruction (a : ℝ) (f : SoninL2)
    (hf : ∀ᵐ x ∂volume, x < a → f x = 0) :
    logTranslationCLM (-a) (suzukiPositiveZeroExtension
      (soninHalfLine (logTranslationCLM a f))) = f := by
  have hs := (MellinL2.realTranslation_measurePreserving a).quasiMeasurePreserving.tendsto_ae.eventually hf
  have hhalf : logTranslationCLM a f ∈ halfLineL2 := by
    rw [mem_halfLineL2_iff]
    filter_upwards [hs, logarithmicTranslation_coeFn a f] with x hs ht hx
    rw [ht]
    apply hs
    change x+a < a
    linarith only [hx]
  rw [suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2 hhalf]
  have h := congrArg (fun T : SoninL2 →L[ℂ] SoninL2 => T f) (logTranslationCLM_neg_mul a)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

/-- Reflection gives the corresponding exact reconstruction on the left. -/
theorem leftExterior_reconstruction (a : ℝ) (f : SoninL2)
    (hf : ∀ᵐ x ∂volume, -a < x → f x = 0) :
    l2Reflection (logTranslationCLM (-a) (suzukiPositiveZeroExtension
      (soninHalfLine (logTranslationCLM a (l2Reflection f))))) = f := by
  have hs := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hf
  have hr : ∀ᵐ x ∂volume, x < a → l2Reflection f x = 0 := by
    filter_upwards [hs, l2Reflection_ae f] with x hs ht hx
    rw [ht]
    apply hs
    change -a < -x
    linarith only [hx]
  rw [rightExterior_reconstruction a (l2Reflection f) hr, l2Reflection_involutive]

/-- Zero extension is adjoint to literal restriction to the positive half-line. -/
theorem inner_positiveZeroExtension_halfLine (g : SuzukiPositiveL2) (f : SoninL2) :
    inner ℂ (suzukiPositiveZeroExtension g) f = inner ℂ g (soninHalfLine f) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x : ℝ, (Ioi (0 : ℝ)).indicator (fun y => inner ℂ (g y) (f y)) x := by
      apply integral_congr_ae
      filter_upwards [suzukiPositiveZeroExtension_ae g] with x hx
      rw [hx]
      unfold suzukiPositiveZeroExtensionFun
      by_cases hp : x ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hp, indicator_of_mem hp]
      · rw [indicator_of_notMem hp, indicator_of_notMem hp, inner_zero_left]
    _ = ∫ x in Ioi (0 : ℝ), inner ℂ (g x) (f x) := integral_indicator measurableSet_Ioi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [coeFn_soninHalfLine f] with x hx
      rw [hx]

/-- Right exterior distance coordinates give the exact physical pairing. -/
theorem inner_rightExterior_halfLine (a : ℝ) (g : SuzukiPositiveL2) (f : SoninL2) :
    inner ℂ (logTranslationCLM (-a) (suzukiPositiveZeroExtension g)) f =
      inner ℂ g (soninHalfLine (logTranslationCLM a f)) := by
  rw [inner_logTranslationCLM, neg_neg, inner_positiveZeroExtension_halfLine]

/-- Left exterior coordinates are obtained by reflecting the physical source. -/
theorem inner_leftExterior_halfLine (a : ℝ) (g : SuzukiPositiveL2) (f : SoninL2) :
    inner ℂ (l2Reflection (logTranslationCLM (-a) (suzukiPositiveZeroExtension g))) f =
      inner ℂ g (soninHalfLine (logTranslationCLM a (l2Reflection f))) := by
  calc
    _ = inner ℂ (l2Reflection (logTranslationCLM (-a) (suzukiPositiveZeroExtension g)))
        (l2Reflection (l2Reflection f)) := by rw [l2Reflection_involutive]
    _ = inner ℂ (logTranslationCLM (-a) (suzukiPositiveZeroExtension g))
        (l2Reflection f) := l2ReflectionIsometry.inner_map_map _ _
    _ = _ := inner_rightExterior_halfLine a g (l2Reflection f)

private theorem inner_rightExterior_eq_zero (a : SuzukiPositiveAperture)
    (g : SuzukiPositiveL2) (f : suzukiApertureHilbert a) :
    inner ℂ (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) (f : SoninL2) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hcut := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
    (f : SoninL2)
  rw [indicatorCutoff_suzukiApertureHilbert] at hcut
  have hg := (suzukiPositiveZeroExtension_ae g).comp_tendsto
    (MellinL2.realTranslation_measurePreserving (-a.1)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcut, hg, logarithmicTranslation_coeFn (-a.1) (suzukiPositiveZeroExtension g)]
    with x hx hg ht
  change inner ℂ ((logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) x)
    ((f : SoninL2) x) = 0
  by_cases hm : x ∈ centralInterval a.1
  · rw [ht]
    change suzukiPositiveZeroExtension g (x+-a.1) =
      (Ioi (0 : ℝ)).indicator (fun y => g y) (x+-a.1) at hg
    rw [hg, indicator_of_notMem (show x+-a.1 ∉ Ioi (0 : ℝ) by
      intro hp; change 0 < x+-a.1 at hp; linarith only [hm.2, hp]), inner_zero_left]
  · rw [hx, indicator_of_notMem hm, inner_zero_right]

private theorem inner_leftExterior_eq_zero (a : SuzukiPositiveAperture)
    (g : SuzukiPositiveL2) (f : suzukiApertureHilbert a) :
    inner ℂ (l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)))
      (f : SoninL2) = 0 := by
  let rf : suzukiApertureHilbert a :=
    ⟨l2Reflection (f : SoninL2), l2Reflection_mem_centralPhysicalForbidden f.property⟩
  have h := inner_rightExterior_eq_zero a g rf
  change inner ℂ (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))
    (l2Reflection (f : SoninL2)) = 0 at h
  calc
    _ = inner ℂ (l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)))
        (l2Reflection (l2Reflection (f : SoninL2))) := by rw [l2Reflection_involutive]
    _ = _ := (l2ReflectionIsometry.inner_map_map _ _).trans h

private theorem extension_physical {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (v : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormEmbedding b (apertureExt hab v) = ccmArchimedeanFormEmbedding a v := by
  simpa only [ccmArchimedeanFormToAperture_coe] using
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq (apertureExt_val hab v)

/-- The exact right exterior crossing retains the actual Gamma boundary transfer and full remainder. -/
theorem ccmWeilForm_rightExterior_pair {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u =
      logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) :
    ccmRestrictedWeilForm b u (apertureExt hab v) =
      -inner ℂ g (ccmGammaRightBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v)) +
        inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
          (ccmArchimedeanFormToAperture b (apertureExt hab v)) := by
  have hm := integral_ccmGammaTranslationMixed b u (apertureExt hab v)
  have ht := integral_ccmGamma_apertureRightBoundary a (ccmArchimedeanFormToAperture a v) g
  simp only [ccmArchimedeanFormToAperture_coe] at ht
  have hi : inner ℂ (ccmArchimedeanFormToAperture b u)
      (ccmArchimedeanFormToAperture b (apertureExt hab v)) = 0 := by
    change inner ℂ (ccmArchimedeanFormEmbedding b u)
      (ccmArchimedeanFormEmbedding b (apertureExt hab v)) = 0
    rw [hu, extension_physical]
    exact inner_rightExterior_eq_zero a g (ccmArchimedeanFormToAperture a v)
  rw [hu, extension_physical, ht, hi, sub_zero] at hm
  rw [ccmRestrictedWeilForm, ← hm]

/-- The full old/right-exterior crossing is bounded independently of collar width. -/
theorem norm_ccmWeilForm_rightExterior_le {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u =
      logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g)) :
    ‖ccmRestrictedWeilForm b u (apertureExt hab v)‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture a v‖ := by
  have hng : ‖g‖ = ‖ccmArchimedeanFormToAperture b u‖ := by
    change _ = ‖ccmArchimedeanFormEmbedding b u‖
    rw [hu]
    exact ((MellinL2.additiveTranslationUnitary (-a.1)).norm_map _).trans
      (norm_suzukiPositiveZeroExtension g) |>.symm
  have hnv : ‖ccmArchimedeanFormToAperture b (apertureExt hab v)‖ =
      ‖ccmArchimedeanFormToAperture a v‖ := by
    change ‖ccmArchimedeanFormEmbedding b (apertureExt hab v)‖ = _
    rw [extension_physical]
    rfl
  have hphys : ‖ccmArchimedeanFormEmbedding a v‖ = ‖ccmArchimedeanFormToAperture a v‖ := rfl
  rw [ccmWeilForm_rightExterior_pair hab u v g hu]
  calc
    _ ≤ ‖inner ℂ g (ccmGammaRightBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v))‖ +
        ‖inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
          (ccmArchimedeanFormToAperture b (apertureExt hab v))‖ := by
      simpa only [norm_neg] using norm_add_le
        (-inner ℂ g (ccmGammaRightBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v))) _
    _ ≤ ‖g‖*(2*Real.pi*‖ccmArchimedeanFormEmbedding a v‖) +
        (‖ccmRestrictedWeilBoundedRemainder b‖*‖ccmArchimedeanFormToAperture b u‖)*
          ‖ccmArchimedeanFormToAperture b (apertureExt hab v)‖ := by
      apply add_le_add
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_left (norm_ccmGammaRightBoundaryTransfer_le _ _) (norm_nonneg _))
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_right ((ccmRestrictedWeilBoundedRemainder b).le_opNorm _)
            (norm_nonneg _))
    _ = _ := by rw [hng, hnv, hphys]; ring

/-- The exact left exterior crossing retains the actual Gamma boundary transfer and full remainder. -/
theorem ccmWeilForm_leftExterior_pair {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u =
      l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))) :
    ccmRestrictedWeilForm b u (apertureExt hab v) =
      -inner ℂ g (ccmGammaLeftBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v)) +
        inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
          (ccmArchimedeanFormToAperture b (apertureExt hab v)) := by
  have hm := integral_ccmGammaTranslationMixed b u (apertureExt hab v)
  have ht := integral_ccmGamma_apertureLeftBoundary a (ccmArchimedeanFormToAperture a v) g
  simp only [ccmArchimedeanFormToAperture_coe] at ht
  have hi : inner ℂ (ccmArchimedeanFormToAperture b u)
      (ccmArchimedeanFormToAperture b (apertureExt hab v)) = 0 := by
    change inner ℂ (ccmArchimedeanFormEmbedding b u)
      (ccmArchimedeanFormEmbedding b (apertureExt hab v)) = 0
    rw [hu, extension_physical]
    exact inner_leftExterior_eq_zero a g (ccmArchimedeanFormToAperture a v)
  rw [hu, extension_physical, ht, hi, sub_zero] at hm
  rw [ccmRestrictedWeilForm, ← hm]

/-- The full old/left-exterior crossing is bounded independently of collar width. -/
theorem norm_ccmWeilForm_leftExterior_le {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u =
      l2Reflection (logTranslationCLM (-a.1) (suzukiPositiveZeroExtension g))) :
    ‖ccmRestrictedWeilForm b u (apertureExt hab v)‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture a v‖ := by
  have hng : ‖g‖ = ‖ccmArchimedeanFormToAperture b u‖ := by
    change _ = ‖ccmArchimedeanFormEmbedding b u‖
    rw [hu]
    exact ((l2ReflectionIsometry.norm_map _).trans
      ((MellinL2.additiveTranslationUnitary (-a.1)).norm_map _)).trans
      (norm_suzukiPositiveZeroExtension g) |>.symm
  have hnv : ‖ccmArchimedeanFormToAperture b (apertureExt hab v)‖ =
      ‖ccmArchimedeanFormToAperture a v‖ := by
    change ‖ccmArchimedeanFormEmbedding b (apertureExt hab v)‖ = _
    rw [extension_physical]
    rfl
  have hphys : ‖ccmArchimedeanFormEmbedding a v‖ = ‖ccmArchimedeanFormToAperture a v‖ := rfl
  rw [ccmWeilForm_leftExterior_pair hab u v g hu]
  calc
    _ ≤ ‖inner ℂ g (ccmGammaLeftBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v))‖ +
        ‖inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
          (ccmArchimedeanFormToAperture b (apertureExt hab v))‖ := by
      simpa only [norm_neg] using norm_add_le
        (-inner ℂ g (ccmGammaLeftBoundaryTransfer a.1 (ccmArchimedeanFormEmbedding a v))) _
    _ ≤ ‖g‖*(2*Real.pi*‖ccmArchimedeanFormEmbedding a v‖) +
        (‖ccmRestrictedWeilBoundedRemainder b‖*‖ccmArchimedeanFormToAperture b u‖)*
          ‖ccmArchimedeanFormToAperture b (apertureExt hab v)‖ := by
      apply add_le_add
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_left (norm_ccmGammaLeftBoundaryTransfer_le _ _) (norm_nonneg _))
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_right ((ccmRestrictedWeilBoundedRemainder b).le_opNorm _)
            (norm_nonneg _))
    _ = _ := by rw [hng, hnv, hphys]; ring

private theorem inner_oppositeHalfLines_eq_zero (f g : SuzukiPositiveL2) :
    inner ℂ (suzukiPositiveZeroExtension g)
      (l2Reflection (suzukiPositiveZeroExtension f)) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  have hf := (suzukiPositiveZeroExtension_ae f).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [suzukiPositiveZeroExtension_ae g, hf,
    l2Reflection_ae (suzukiPositiveZeroExtension f)] with x hg hf hr
  change inner ℂ (suzukiPositiveZeroExtension g x)
    (l2Reflection (suzukiPositiveZeroExtension f) x) = 0
  change suzukiPositiveZeroExtension f (-x) =
    (Ioi (0 : ℝ)).indicator (fun y => f y) (-x) at hf
  change suzukiPositiveZeroExtension g x =
    (Ioi (0 : ℝ)).indicator (fun y => g y) x at hg
  rw [hg, hr, hf]
  by_cases hx : 0 < x
  · rw [indicator_of_notMem (show -x ∉ Ioi (0 : ℝ) from
      not_lt.mpr (neg_nonpos.mpr hx.le)), inner_zero_right]
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx), inner_zero_left]

/-- Opposite half-lines have the same bounded Gamma crossing as adjacent collars. -/
theorem ccmWeilForm_oppositeHalfLines_pair (b : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain b) (f g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u = suzukiPositiveZeroExtension g)
    (hv : ccmArchimedeanFormEmbedding b v =
      l2Reflection (suzukiPositiveZeroExtension f)) :
    ccmRestrictedWeilForm b u v = -inner ℂ g (ccmGammaBoundaryCLM f) +
      inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
        (ccmArchimedeanFormToAperture b v) := by
  have hm := integral_ccmGammaTranslationMixed b u v
  have hi : inner ℂ (ccmArchimedeanFormToAperture b u)
      (ccmArchimedeanFormToAperture b v) = 0 := by
    change inner ℂ (ccmArchimedeanFormEmbedding b u)
      (ccmArchimedeanFormEmbedding b v) = 0
    rw [hu, hv]
    exact inner_oppositeHalfLines_eq_zero f g
  rw [hu, hv, integral_ccmGamma_oppositeJump, hi, sub_zero] at hm
  rw [ccmRestrictedWeilForm, ← hm]

/-- The two collar interaction is bounded by physical mass, without a separation loss. -/
theorem norm_ccmWeilForm_oppositeHalfLines_le (b : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain b) (f g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b u = suzukiPositiveZeroExtension g)
    (hv : ccmArchimedeanFormEmbedding b v =
      l2Reflection (suzukiPositiveZeroExtension f)) :
    ‖ccmRestrictedWeilForm b u v‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture b v‖ := by
  have hng : ‖g‖ = ‖ccmArchimedeanFormToAperture b u‖ := by
    change _ = ‖ccmArchimedeanFormEmbedding b u‖
    rw [hu, norm_suzukiPositiveZeroExtension]
  have hnf : ‖f‖ = ‖ccmArchimedeanFormToAperture b v‖ := by
    change _ = ‖ccmArchimedeanFormEmbedding b v‖
    rw [hv]
    exact ((l2ReflectionIsometry.norm_map (suzukiPositiveZeroExtension f)).trans
      (norm_suzukiPositiveZeroExtension f)).symm
  rw [ccmWeilForm_oppositeHalfLines_pair b u v f g hu hv]
  calc
    _ ≤ ‖inner ℂ g (ccmGammaBoundaryCLM f)‖ +
        ‖inner ℂ (ccmRestrictedWeilBoundedRemainder b (ccmArchimedeanFormToAperture b u))
          (ccmArchimedeanFormToAperture b v)‖ := by
      simpa only [norm_neg] using norm_add_le (-inner ℂ g (ccmGammaBoundaryCLM f)) _
    _ ≤ ‖g‖*(2*Real.pi*‖f‖) +
        (‖ccmRestrictedWeilBoundedRemainder b‖*‖ccmArchimedeanFormToAperture b u‖)*
          ‖ccmArchimedeanFormToAperture b v‖ := by
      apply add_le_add
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_left
            ((ccmGammaBoundaryCLM.le_opNorm f).trans
              (mul_le_mul_of_nonneg_right norm_ccmGammaBoundaryCLM_le (norm_nonneg f)))
            (norm_nonneg g))
      · exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
          (mul_le_mul_of_nonneg_right ((ccmRestrictedWeilBoundedRemainder b).le_opNorm _)
            (norm_nonneg _))
    _ = _ := by rw [hng, hnf]; ring

/-- Literal right support is sufficient for the complete old/collar crossing bound. -/
theorem norm_ccmWeilForm_rightExterior_of_supported {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a)
    (hu : ∀ᵐ x ∂volume, x < a.1 → ccmArchimedeanFormEmbedding b u x = 0) :
    ‖ccmRestrictedWeilForm b u (apertureExt hab v)‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture a v‖ :=
  norm_ccmWeilForm_rightExterior_le hab u v _ (rightExterior_reconstruction a.1 _ hu).symm

/-- Literal left support gives the same full crossing bound. -/
theorem norm_ccmWeilForm_leftExterior_of_supported {a b : SuzukiPositiveAperture}
    (hab : a.1 ≤ b.1) (u : CCMArchimedeanFormDomain b) (v : CCMArchimedeanFormDomain a)
    (hu : ∀ᵐ x ∂volume, -a.1 < x → ccmArchimedeanFormEmbedding b u x = 0) :
    ‖ccmRestrictedWeilForm b u (apertureExt hab v)‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture a v‖ :=
  norm_ccmWeilForm_leftExterior_le hab u v _ (leftExterior_reconstruction a.1 _ hu).symm

/-- Sources on opposite half-lines interact by a bounded full Weil operator. -/
theorem norm_ccmWeilForm_oppositeHalfLines_of_supported (b : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain b)
    (hu : ∀ᵐ x ∂volume, x < 0 → ccmArchimedeanFormEmbedding b u x = 0)
    (hv : ∀ᵐ x ∂volume, 0 < x → ccmArchimedeanFormEmbedding b v x = 0) :
    ‖ccmRestrictedWeilForm b u v‖ ≤
      (2*Real.pi+‖ccmRestrictedWeilBoundedRemainder b‖) *
        ‖ccmArchimedeanFormToAperture b u‖ * ‖ccmArchimedeanFormToAperture b v‖ := by
  have huf : ccmArchimedeanFormEmbedding b u ∈ halfLineL2 := by
    rwa [mem_halfLineL2_iff]
  have hvs := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae.eventually hv
  have hvf : l2Reflection (ccmArchimedeanFormEmbedding b v) ∈ halfLineL2 := by
    rw [mem_halfLineL2_iff]
    filter_upwards [hvs, l2Reflection_ae (ccmArchimedeanFormEmbedding b v)] with x hs hr hx
    rw [hr]
    exact hs (neg_pos.mpr hx)
  have hue := suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2 huf
  have hve := congrArg l2Reflection
    (suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2 hvf)
  rw [l2Reflection_involutive] at hve
  exact norm_ccmWeilForm_oppositeHalfLines_le b u v _ _ hue.symm hve.symm

#print axioms norm_ccmWeilForm_rightExterior_of_supported
#print axioms norm_ccmWeilForm_leftExterior_of_supported
#print axioms norm_ccmWeilForm_oppositeHalfLines_of_supported
#print axioms ccmWeilForm_oppositeHalfLines_pair
#print axioms norm_ccmWeilForm_oppositeHalfLines_le
#print axioms ccmWeilForm_rightExterior_pair
#print axioms norm_ccmWeilForm_rightExterior_le
#print axioms ccmWeilForm_leftExterior_pair
#print axioms norm_ccmWeilForm_leftExterior_le
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
